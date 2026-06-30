// Lean compiler output
// Module: Lean.Server.FileWorker.InlayHints
// Imports: Lean.Server.GoTo Lean.Server.Requests
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_int_add, lean_int_sub, lean_io_basemutex_lock,
    lean_io_basemutex_unlock, lean_io_mono_ms_now, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_dec_eq, lean_string_hash, lean_string_utf8_byte_size,
    lean_task_pure, lean_uint32_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::{l_instInhabitedEIO___aux__1___boxed, l_instMonadEIO};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Lsp::LanguageFeatures::{
    l_Lean_Lsp_instFromJsonInlayHintParams_fromJson, l_Lean_Lsp_instToJsonInlayHint_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::{
    l_Lean_FileMap_lspRangeToUtf8Range, l_Lean_FileMap_utf8PosToLspPos,
    l_Lean_FileMap_utf8RangeToLspRange,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_toList___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::InfoTree::InlayHints::{
    l_Lean_Elab_InlayHint_ofCustomInfo_x3f, l_Lean_Elab_InlayHint_resolveDeferred___boxed,
    l_Lean_Elab_instBEqInlayHintTextEdit_beq,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_ContextInfo_runMetaM___redArg, l_Lean_Elab_Info_updateContext_x3f,
    l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Server::AsyncList::l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg;
use crate::r#gen::Lean::Server::GoTo::{
    initialize_Lean_Server_GoTo, runtime_initialize_Lean_Server_GoTo,
};
use crate::r#gen::Lean::Server::RequestCancellation::{
    l_Lean_Server_RequestCancellationToken_cancellationTasks,
    l_Lean_Server_RequestCancellationToken_wasCancelled,
};
use crate::r#gen::Lean::Server::Requests::{
    initialize_Lean_Server_Requests, l___private_Lean_Server_Requests_0__Lean_Server_getState_x21,
    l_Lean_Server_RequestError_ofIoError, l_Lean_Server_RequestM_mapTaskCostly___redArg,
    l_Lean_Server_instInhabitedRequestError_default, l_Lean_Server_requestHandlers,
    l_Lean_Server_statefulRequestHandlers, runtime_initialize_Lean_Server_Requests,
};
use crate::r#gen::Lean::Server::ServerTask::l_Lean_Server_ServerTask_mapCheap___redArg;
use crate::r#gen::Lean::Server::Snapshots::{
    l_Lean_Server_Snapshots_Snapshot_endPos, l_Lean_Server_Snapshots_Snapshot_infoTree,
};
use crate::r#gen::Lean::Server::Utils::l_Lean_Server_documentUriFromModule_x3f;
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_bsize, l_Lean_Syntax_Range_contains, l_Lean_Syntax_Range_overlaps,
};
use crate::r#gen::Std::Sync::Mutex::l_Std_Mutex_new___redArg;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 70, 105, 108, 101, 87, 111, 114, 107, 101, 114, 46, 73, 110, 108, 97, 121, 72, 105, 110, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 70, 105, 108, 101, 87, 111, 114, 107, 101, 114, 46, 97, 112, 112, 108, 121, 69, 100, 105, 116, 84, 111, 72, 105, 110, 116, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [71, 111, 116, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3_value: leanh::LeanStringObject<53> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110, 32, 105, 110, 118, 97, 108, 105, 100, 97, 116, 101, 100, 32, 98, 121, 32, 101, 100, 105, 116, 32, 97, 116, 32, 114, 97, 110, 103, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [70, 105, 108, 101, 87, 111, 114, 107, 101, 114, 0]};
static mut l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [73, 110, 108, 97, 121, 72, 105, 110, 116, 83, 116, 97, 116, 101, 0]};
static mut l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
static l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject,15371898625421214203 as *mut leanh::LeanObject] };
static l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject,2627710428663975656 as *mut leanh::LeanObject] };
pub static l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject,15862368019090892393 as *mut leanh::LeanObject] };
static mut l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_instTypeNameInlayHintState: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value:
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
static mut l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_instInhabitedInlayHintState_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_instInhabitedInlayHintState: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value
)
    as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value:
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
static mut l_Lean_Server_FileWorker_InlayHintState_init___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_InlayHintState_init___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_InlayHintState_init: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value: leanh::LeanStringObject<62> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleInlayHints___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 70, 105, 108, 101, 87, 111, 114,
        107, 101, 114, 46, 104, 97, 110, 100, 108, 101, 73, 110, 108, 97, 121, 72, 105, 110, 116,
        115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_handleInlayHints___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_handleInlayHints___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleInlayHints___closed__1_value:
    leanh::LeanStringObject<399> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 399,
    m_capacity: 399,
    m_length: 398,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 102, 105, 110, 105, 115, 104, 101, 100, 83, 110, 97, 112, 115, 32, 62, 61, 32, 111,
        108, 100, 70, 105, 110, 105, 115, 104, 101, 100, 83, 110, 97, 112, 115, 10, 32, 32, 45, 45,
        32, 86, 83, 32, 67, 111, 100, 101, 32, 101, 109, 105, 116, 115, 32, 105, 110, 108, 97, 121,
        32, 104, 105, 110, 116, 32, 114, 101, 113, 117, 101, 115, 116, 115, 32, 42, 101, 118, 101,
        114, 121, 32, 116, 105, 109, 101, 32, 116, 104, 101, 32, 117, 115, 101, 114, 32, 115, 99,
        114, 111, 108, 108, 115, 42, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 114, 101, 97,
        115, 111, 110, 97, 98, 108, 121, 32, 101, 120, 112, 101, 110, 115, 105, 118, 101, 44, 10,
        32, 32, 45, 45, 32, 115, 111, 32, 105, 110, 32, 97, 100, 100, 105, 116, 105, 111, 110, 32,
        116, 111, 32, 114, 101, 45, 117, 115, 105, 110, 103, 32, 111, 108, 100, 32, 105, 110, 108,
        97, 121, 32, 104, 105, 110, 116, 115, 32, 102, 114, 111, 109, 32, 112, 97, 114, 116, 115,
        32, 111, 102, 32, 116, 104, 101, 32, 102, 105, 108, 101, 32, 116, 104, 97, 116, 32, 104,
        97, 118, 101, 110, 39, 116, 32, 98, 101, 101, 110, 32, 112, 114, 111, 99, 101, 115, 115,
        101, 100, 10, 32, 32, 45, 45, 32, 121, 101, 116, 44, 32, 119, 101, 32, 97, 108, 115, 111,
        32, 114, 101, 45, 117, 115, 101, 32, 111, 108, 100, 32, 105, 110, 108, 97, 121, 32, 104,
        105, 110, 116, 115, 32, 102, 114, 111, 109, 32, 112, 97, 114, 116, 115, 32, 111, 102, 32,
        116, 104, 101, 32, 102, 105, 108, 101, 32, 116, 104, 97, 116, 32, 104, 97, 118, 101, 32,
        98, 101, 101, 110, 32, 112, 114, 111, 99, 101, 115, 115, 101, 100, 32, 97, 108, 114, 101,
        97, 100, 121, 10, 32, 32, 45, 45, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 99, 117,
        114, 114, 101, 110, 116, 32, 115, 116, 97, 116, 101, 32, 111, 102, 32, 116, 104, 101, 32,
        100, 111, 99, 117, 109, 101, 110, 116, 46, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Server_FileWorker_handleInlayHints___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_handleInlayHints___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_FileWorker_handleInlayHints___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_FileWorker_handleInlayHints___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 114, 101, 113, 117, 101, 115, 116, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0]};
static mut l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 115, 116, 97, 116, 101, 102, 117, 108, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0]};
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [39, 58, 32, 111, 110, 108, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [39, 58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 47, 105, 110, 108, 97, 121, 72, 105, 110, 116, 0]};
static mut l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [119, 111, 114, 107, 115, 112, 97, 99, 101, 47, 105, 110, 108, 97, 121, 72, 105, 110, 116, 47, 114, 101, 102, 114, 101, 115, 104, 0]};
static mut l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_FileWorker_handleInlayHints___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_InlayHintLinkLocation_toLspLocation(
    mut v_text_2773_: *mut leanh::LeanObject,
    mut v_l_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_module_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v_val_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_a_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_2776_ = leanh::lean_ctor_get(v_l_2774_, 0);
                v_range_2777_ = leanh::lean_ctor_get(v_l_2774_, 1);
                v_isSharedCheck_2814_ = (!leanh::lean_is_exclusive(v_l_2774_)) as u8;
                if v_isSharedCheck_2814_ == 0 {
                    v___x_2779_ = v_l_2774_;
                    v_isShared_2780_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2777_);
                    leanh::lean_inc(v_module_2776_);
                    leanh::lean_dec(v_l_2774_);
                    v___x_2779_ = leanh::lean_box(0);
                    v_isShared_2780_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2781_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2776_);
                if leanh::lean_obj_tag(v___x_2781_) == 0 {
                    v_a_2782_ = leanh::lean_ctor_get(v___x_2781_, 0);
                    v_isSharedCheck_2805_ = (!leanh::lean_is_exclusive(v___x_2781_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2784_ = v___x_2781_;
                        v_isShared_2785_ = v_isSharedCheck_2805_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2782_);
                        leanh::lean_dec(v___x_2781_);
                        v___x_2784_ = leanh::lean_box(0);
                        v_isShared_2785_ = v_isSharedCheck_2805_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2779_);
                    leanh::lean_dec_ref(v_range_2777_);
                    leanh::lean_dec_ref(v_text_2773_);
                    v_a_2806_ = leanh::lean_ctor_get(v___x_2781_, 0);
                    v_isSharedCheck_2813_ = (!leanh::lean_is_exclusive(v___x_2781_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v___x_2808_ = v___x_2781_;
                        v_isShared_2809_ = v_isSharedCheck_2813_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2806_);
                        leanh::lean_dec(v___x_2781_);
                        v___x_2808_ = leanh::lean_box(0);
                        v_isShared_2809_ = v_isSharedCheck_2813_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2782_) == 1 {
                    v_val_2786_ = leanh::lean_ctor_get(v_a_2782_, 0);
                    v_isSharedCheck_2800_ = (!leanh::lean_is_exclusive(v_a_2782_)) as u8;
                    if v_isSharedCheck_2800_ == 0 {
                        v___x_2788_ = v_a_2782_;
                        v_isShared_2789_ = v_isSharedCheck_2800_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2786_);
                        leanh::lean_dec(v_a_2782_);
                        v___x_2788_ = leanh::lean_box(0);
                        v_isShared_2789_ = v_isSharedCheck_2800_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2782_);
                    leanh::lean_del_object(v___x_2779_);
                    leanh::lean_dec_ref(v_range_2777_);
                    leanh::lean_dec_ref(v_text_2773_);
                    v___x_2801_ = leanh::lean_box(0);
                    if v_isShared_2785_ == 0 {
                        leanh::lean_ctor_set(v___x_2784_, 0, v___x_2801_);
                        v___x_2803_ = v___x_2784_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                        v___x_2803_ = v_reuseFailAlloc_2804_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2790_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_2773_, v_range_2777_);
                if v_isShared_2780_ == 0 {
                    leanh::lean_ctor_set(v___x_2779_, 1, v___x_2790_);
                    leanh::lean_ctor_set(v___x_2779_, 0, v_val_2786_);
                    v___x_2792_ = v___x_2779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_val_2786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2790_);
                    v___x_2792_ = v_reuseFailAlloc_2799_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2789_ == 0 {
                    leanh::lean_ctor_set(v___x_2788_, 0, v___x_2792_);
                    v___x_2794_ = v___x_2788_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2792_);
                    v___x_2794_ = v_reuseFailAlloc_2798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2785_ == 0 {
                    leanh::lean_ctor_set(v___x_2784_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2784_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2796_;
            }
            7 => {
                return v___x_2803_;
            }
            8 => {
                if v_isShared_2809_ == 0 {
                    v___x_2811_ = v___x_2808_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
                    v___x_2811_ = v_reuseFailAlloc_2812_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(
    mut v_text_2815_: *mut leanh::LeanObject,
    mut v_l_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_2815_, v_l_2816_);
    return v_res_2818_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(
    mut v_text_2819_: *mut leanh::LeanObject,
    mut v_p_2820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tooltip_x3f_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_x3f_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2852_: u8 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_2822_ = leanh::lean_ctor_get(v_p_2820_, 0);
                leanh::lean_inc_ref(v_value_2822_);
                v_tooltip_x3f_2823_ = leanh::lean_ctor_get(v_p_2820_, 1);
                leanh::lean_inc(v_tooltip_x3f_2823_);
                v_location_x3f_2824_ = leanh::lean_ctor_get(v_p_2820_, 2);
                leanh::lean_inc(v_location_x3f_2824_);
                leanh::lean_dec_ref(v_p_2820_);
                if leanh::lean_obj_tag(v_location_x3f_2824_) == 0 {
                    leanh::lean_dec_ref(v_text_2819_);
                    v___x_2845_ = leanh::lean_box(0);
                    v_a_2832_ = v___x_2845_;
                    state = 2;
                    continue;
                } else {
                    v_val_2846_ = leanh::lean_ctor_get(v_location_x3f_2824_, 0);
                    leanh::lean_inc(v_val_2846_);
                    leanh::lean_dec_ref_known(v_location_x3f_2824_, 1);
                    v___x_2847_ =
                        l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_2819_, v_val_2846_);
                    if leanh::lean_obj_tag(v___x_2847_) == 0 {
                        v_a_2848_ = leanh::lean_ctor_get(v___x_2847_, 0);
                        leanh::lean_inc(v_a_2848_);
                        leanh::lean_dec_ref_known(v___x_2847_, 1);
                        v_a_2832_ = v_a_2848_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_tooltip_x3f_2823_);
                        leanh::lean_dec_ref(v_value_2822_);
                        v_a_2849_ = leanh::lean_ctor_get(v___x_2847_, 0);
                        v_isSharedCheck_2856_ =
                            (!leanh::lean_is_exclusive(v___x_2847_)) as u8;
                        if v_isSharedCheck_2856_ == 0 {
                            v___x_2851_ = v___x_2847_;
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2849_);
                            leanh::lean_dec(v___x_2847_);
                            v___x_2851_ = leanh::lean_box(0);
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2828_ = leanh::lean_box(0);
                v___x_2829_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2829_, 0, v_value_2822_);
                leanh::lean_ctor_set(v___x_2829_, 1, v___y_2827_);
                leanh::lean_ctor_set(v___x_2829_, 2, v___y_2826_);
                leanh::lean_ctor_set(v___x_2829_, 3, v___x_2828_);
                v___x_2830_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2830_, 0, v___x_2829_);
                return v___x_2830_;
            }
            2 => {
                if leanh::lean_obj_tag(v_tooltip_x3f_2823_) == 0 {
                    v___x_2833_ = leanh::lean_box(0);
                    v___y_2826_ = v_a_2832_;
                    v___y_2827_ = v___x_2833_;
                    state = 1;
                    continue;
                } else {
                    v_val_2834_ = leanh::lean_ctor_get(v_tooltip_x3f_2823_, 0);
                    v_isSharedCheck_2844_ =
                        (!leanh::lean_is_exclusive(v_tooltip_x3f_2823_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v___x_2836_ = v_tooltip_x3f_2823_;
                        v_isShared_2837_ = v_isSharedCheck_2844_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2834_);
                        leanh::lean_dec(v_tooltip_x3f_2823_);
                        v___x_2836_ = leanh::lean_box(0);
                        v_isShared_2837_ = v_isSharedCheck_2844_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2838_ = 1;
                v___x_2839_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2839_, 0, v_val_2834_);
                leanh::lean_ctor_set_uint8(
                    v___x_2839_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2838_,
                );
                v___x_2840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2840_, 0, v___x_2839_);
                if v_isShared_2837_ == 0 {
                    leanh::lean_ctor_set(v___x_2836_, 0, v___x_2840_);
                    v___x_2842_ = v___x_2836_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2826_ = v_a_2832_;
                v___y_2827_ = v___x_2842_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2852_ == 0 {
                    v___x_2854_ = v___x_2851_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
                    v___x_2854_ = v_reuseFailAlloc_2855_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart___boxed(
    mut v_text_2857_: *mut leanh::LeanObject,
    mut v_p_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2860_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_2857_, v_p_2858_);
    return v_res_2860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(
    mut v_text_2861_: *mut leanh::LeanObject,
    mut v_sz_2862_: usize,
    mut v_i_2863_: usize,
    mut v_bs_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: usize = 0;
    let mut v___x_2874_: usize = 0;
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2866_ = lean_usize_dec_lt(v_i_2863_, v_sz_2862_);
                if v___x_2866_ == 0 {
                    leanh::lean_dec_ref(v_text_2861_);
                    v___x_2867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2867_, 0, v_bs_2864_);
                    return v___x_2867_;
                } else {
                    v_v_2868_ = lean_array_uget_borrowed(v_bs_2864_, v_i_2863_);
                    leanh::lean_inc(v_v_2868_);
                    leanh::lean_inc_ref(v_text_2861_);
                    v___x_2869_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(
                        v_text_2861_,
                        v_v_2868_,
                    );
                    if leanh::lean_obj_tag(v___x_2869_) == 0 {
                        v_a_2870_ = leanh::lean_ctor_get(v___x_2869_, 0);
                        leanh::lean_inc(v_a_2870_);
                        leanh::lean_dec_ref_known(v___x_2869_, 1);
                        v___x_2871_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2872_ = lean_array_uset(v_bs_2864_, v_i_2863_, v___x_2871_);
                        v___x_2873_ = 1usize;
                        v___x_2874_ = lean_usize_add(v_i_2863_, v___x_2873_);
                        v___x_2875_ = lean_array_uset(v_bs_x27_2872_, v_i_2863_, v_a_2870_);
                        v_i_2863_ = v___x_2874_;
                        v_bs_2864_ = v___x_2875_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_2864_);
                        leanh::lean_dec_ref(v_text_2861_);
                        v_a_2877_ = leanh::lean_ctor_get(v___x_2869_, 0);
                        v_isSharedCheck_2884_ =
                            (!leanh::lean_is_exclusive(v___x_2869_)) as u8;
                        if v_isSharedCheck_2884_ == 0 {
                            v___x_2879_ = v___x_2869_;
                            v_isShared_2880_ = v_isSharedCheck_2884_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2877_);
                            leanh::lean_dec(v___x_2869_);
                            v___x_2879_ = leanh::lean_box(0);
                            v_isShared_2880_ = v_isSharedCheck_2884_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2880_ == 0 {
                    v___x_2882_ = v___x_2879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
                    v___x_2882_ = v_reuseFailAlloc_2883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0___boxed(
    mut v_text_2885_: *mut leanh::LeanObject,
    mut v_sz_2886_: *mut leanh::LeanObject,
    mut v_i_2887_: *mut leanh::LeanObject,
    mut v_bs_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2890_: usize = 0;
    let mut v_i_boxed_2891_: usize = 0;
    let mut v_res_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2890_ = leanh::lean_unbox_usize(v_sz_2886_);
    leanh::lean_dec(v_sz_2886_);
    v_i_boxed_2891_ = leanh::lean_unbox_usize(v_i_2887_);
    leanh::lean_dec(v_i_2887_);
    v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_2885_, v_sz_boxed_2890_, v_i_boxed_2891_, v_bs_2888_);
    return v_res_2892_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(
    mut v_text_2893_: *mut leanh::LeanObject,
    mut v_x_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_p_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_sz_2909_: usize = 0;
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v_a_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2894_) == 0 {
                    leanh::lean_dec_ref(v_text_2893_);
                    v_n_2896_ = leanh::lean_ctor_get(v_x_2894_, 0);
                    v_isSharedCheck_2904_ = (!leanh::lean_is_exclusive(v_x_2894_)) as u8;
                    if v_isSharedCheck_2904_ == 0 {
                        v___x_2898_ = v_x_2894_;
                        v_isShared_2899_ = v_isSharedCheck_2904_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_2896_);
                        leanh::lean_dec(v_x_2894_);
                        v___x_2898_ = leanh::lean_box(0);
                        v_isShared_2899_ = v_isSharedCheck_2904_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_p_2905_ = leanh::lean_ctor_get(v_x_2894_, 0);
                    v_isSharedCheck_2931_ = (!leanh::lean_is_exclusive(v_x_2894_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2907_ = v_x_2894_;
                        v_isShared_2908_ = v_isSharedCheck_2931_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_2905_);
                        leanh::lean_dec(v_x_2894_);
                        v___x_2907_ = leanh::lean_box(0);
                        v_isShared_2908_ = v_isSharedCheck_2931_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2899_ == 0 {
                    v___x_2901_ = v___x_2898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_n_2896_);
                    v___x_2901_ = v_reuseFailAlloc_2903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2902_, 0, v___x_2901_);
                return v___x_2902_;
            }
            3 => {
                v_sz_2909_ = lean_array_size(v_p_2905_);
                v___x_2910_ = 0usize;
                v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_2893_, v_sz_2909_, v___x_2910_, v_p_2905_);
                if leanh::lean_obj_tag(v___x_2911_) == 0 {
                    v_a_2912_ = leanh::lean_ctor_get(v___x_2911_, 0);
                    v_isSharedCheck_2922_ = (!leanh::lean_is_exclusive(v___x_2911_)) as u8;
                    if v_isSharedCheck_2922_ == 0 {
                        v___x_2914_ = v___x_2911_;
                        v_isShared_2915_ = v_isSharedCheck_2922_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2912_);
                        leanh::lean_dec(v___x_2911_);
                        v___x_2914_ = leanh::lean_box(0);
                        v_isShared_2915_ = v_isSharedCheck_2922_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2907_);
                    v_a_2923_ = leanh::lean_ctor_get(v___x_2911_, 0);
                    v_isSharedCheck_2930_ = (!leanh::lean_is_exclusive(v___x_2911_)) as u8;
                    if v_isSharedCheck_2930_ == 0 {
                        v___x_2925_ = v___x_2911_;
                        v_isShared_2926_ = v_isSharedCheck_2930_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2923_);
                        leanh::lean_dec(v___x_2911_);
                        v___x_2925_ = leanh::lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2930_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2908_ == 0 {
                    leanh::lean_ctor_set(v___x_2907_, 0, v_a_2912_);
                    v___x_2917_ = v___x_2907_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2912_);
                    v___x_2917_ = v_reuseFailAlloc_2921_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2915_ == 0 {
                    leanh::lean_ctor_set(v___x_2914_, 0, v___x_2917_);
                    v___x_2919_ = v___x_2914_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
                    v___x_2919_ = v_reuseFailAlloc_2920_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2919_;
            }
            7 => {
                if v_isShared_2926_ == 0 {
                    v___x_2928_ = v___x_2925_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
                    v___x_2928_ = v_reuseFailAlloc_2929_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___boxed(
    mut v_text_2932_: *mut leanh::LeanObject,
    mut v_x_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2935_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_2932_, v_x_2933_);
    return v_res_2935_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_toLspInlayHintKind(mut v_x_2936_: u8) -> u8 {
    if v_x_2936_ == 0 {
        let mut v___x_2937_: u8 = 0;
        v___x_2937_ = 0;
        return v___x_2937_;
    } else {
        let mut v___x_2938_: u8 = 0;
        v___x_2938_ = 1;
        return v___x_2938_;
    }
}
pub unsafe fn l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(
    mut v_x_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_2940_: u8 = 0;
    let mut v_res_2941_: u8 = 0;
    let mut v_r_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_2940_ = (leanh::lean_unbox(v_x_2939_) as u8);
    v_res_2941_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v_x_18__boxed_2940_);
    v_r_2942_ = leanh::lean_box((v_res_2941_) as usize);
    return v_r_2942_;
}
pub unsafe fn l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(
    mut v_text_2943_: *mut leanh::LeanObject,
    mut v_e_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_2945_ = leanh::lean_ctor_get(v_e_2944_, 0);
    leanh::lean_inc_ref(v_range_2945_);
    v_newText_2946_ = leanh::lean_ctor_get(v_e_2944_, 1);
    leanh::lean_inc_ref(v_newText_2946_);
    leanh::lean_dec_ref(v_e_2944_);
    v___x_2947_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_2943_, v_range_2945_);
    v___x_2948_ = leanh::lean_box(0);
    v___x_2949_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2949_, 0, v___x_2947_);
    leanh::lean_ctor_set(v___x_2949_, 1, v_newText_2946_);
    leanh::lean_ctor_set(v___x_2949_, 2, v___x_2948_);
    leanh::lean_ctor_set(v___x_2949_, 3, v___x_2948_);
    return v___x_2949_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(
    mut v_text_2950_: *mut leanh::LeanObject,
    mut v_sz_2951_: usize,
    mut v_i_2952_: usize,
    mut v_bs_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2954_: u8 = 0;
    let mut v_v_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = lean_usize_dec_lt(v_i_2952_, v_sz_2951_);
                if v___x_2954_ == 0 {
                    leanh::lean_dec_ref(v_text_2950_);
                    return v_bs_2953_;
                } else {
                    v_v_2955_ = lean_array_uget(v_bs_2953_, v_i_2952_);
                    v___x_2956_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2957_ = lean_array_uset(v_bs_2953_, v_i_2952_, v___x_2956_);
                    leanh::lean_inc_ref(v_text_2950_);
                    v___x_2958_ =
                        l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(v_text_2950_, v_v_2955_);
                    v___x_2959_ = 1usize;
                    v___x_2960_ = lean_usize_add(v_i_2952_, v___x_2959_);
                    v___x_2961_ = lean_array_uset(v_bs_x27_2957_, v_i_2952_, v___x_2958_);
                    v_i_2952_ = v___x_2960_;
                    v_bs_2953_ = v___x_2961_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0___boxed(
    mut v_text_2963_: *mut leanh::LeanObject,
    mut v_sz_2964_: *mut leanh::LeanObject,
    mut v_i_2965_: *mut leanh::LeanObject,
    mut v_bs_2966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2967_: usize = 0;
    let mut v_i_boxed_2968_: usize = 0;
    let mut v_res_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2967_ = leanh::lean_unbox_usize(v_sz_2964_);
    leanh::lean_dec(v_sz_2964_);
    v_i_boxed_2968_ = leanh::lean_unbox_usize(v_i_2965_);
    leanh::lean_dec(v_i_2965_);
    v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_2963_, v_sz_boxed_2967_, v_i_boxed_2968_, v_bs_2966_);
    return v_res_2969_;
}
pub unsafe fn l_Lean_Elab_InlayHintInfo_toLspInlayHint(
    mut v_text_2970_: *mut leanh::LeanObject,
    mut v_i_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_position_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdits_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tooltip_x3f_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paddingLeft_2978_: u8 = 0;
    let mut v_paddingRight_2979_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3001_: usize = 0;
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3016_: u8 = 0;
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v___x_3022_: u8 = 0;
    let mut v___x_3023_: u8 = 0;
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut v_isSharedCheck_3029_: u8 = 0;
    let mut v_a_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_position_2973_ = leanh::lean_ctor_get(v_i_2971_, 0);
                leanh::lean_inc(v_position_2973_);
                v_label_2974_ = leanh::lean_ctor_get(v_i_2971_, 1);
                leanh::lean_inc_ref(v_label_2974_);
                v_kind_x3f_2975_ = leanh::lean_ctor_get(v_i_2971_, 2);
                leanh::lean_inc(v_kind_x3f_2975_);
                v_textEdits_2976_ = leanh::lean_ctor_get(v_i_2971_, 3);
                leanh::lean_inc_ref(v_textEdits_2976_);
                v_tooltip_x3f_2977_ = leanh::lean_ctor_get(v_i_2971_, 4);
                leanh::lean_inc(v_tooltip_x3f_2977_);
                v_paddingLeft_2978_ = leanh::lean_ctor_get_uint8(
                    v_i_2971_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_paddingRight_2979_ = leanh::lean_ctor_get_uint8(
                    v_i_2971_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                leanh::lean_dec_ref(v_i_2971_);
                leanh::lean_inc_ref(v_text_2970_);
                v___x_2980_ =
                    l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_2970_, v_label_2974_);
                if leanh::lean_obj_tag(v___x_2980_) == 0 {
                    v_a_2981_ = leanh::lean_ctor_get(v___x_2980_, 0);
                    v_isSharedCheck_3029_ = (!leanh::lean_is_exclusive(v___x_2980_)) as u8;
                    if v_isSharedCheck_3029_ == 0 {
                        v___x_2983_ = v___x_2980_;
                        v_isShared_2984_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2981_);
                        leanh::lean_dec(v___x_2980_);
                        v___x_2983_ = leanh::lean_box(0);
                        v_isShared_2984_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_tooltip_x3f_2977_);
                    leanh::lean_dec_ref(v_textEdits_2976_);
                    leanh::lean_dec(v_kind_x3f_2975_);
                    leanh::lean_dec(v_position_2973_);
                    leanh::lean_dec_ref(v_text_2970_);
                    v_a_3030_ = leanh::lean_ctor_get(v___x_2980_, 0);
                    v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v___x_2980_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3032_ = v___x_2980_;
                        v_isShared_3033_ = v_isSharedCheck_3037_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3030_);
                        leanh::lean_dec(v___x_2980_);
                        v___x_3032_ = leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3037_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_text_2970_);
                v___x_2985_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2970_, v_position_2973_);
                leanh::lean_dec(v_position_2973_);
                if leanh::lean_obj_tag(v_kind_x3f_2975_) == 0 {
                    v___x_3017_ = leanh::lean_box(0);
                    v___y_3000_ = v___x_3017_;
                    state = 4;
                    continue;
                } else {
                    v_val_3018_ = leanh::lean_ctor_get(v_kind_x3f_2975_, 0);
                    v_isSharedCheck_3028_ =
                        (!leanh::lean_is_exclusive(v_kind_x3f_2975_)) as u8;
                    if v_isSharedCheck_3028_ == 0 {
                        v___x_3020_ = v_kind_x3f_2975_;
                        v_isShared_3021_ = v_isSharedCheck_3028_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3018_);
                        leanh::lean_dec(v_kind_x3f_2975_);
                        v___x_3020_ = leanh::lean_box(0);
                        v_isShared_3021_ = v_isSharedCheck_3028_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2990_ = leanh::lean_box((v_paddingLeft_2978_) as usize);
                v___x_2991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2991_, 0, v___x_2990_);
                v___x_2992_ = leanh::lean_box((v_paddingRight_2979_) as usize);
                v___x_2993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2993_, 0, v___x_2992_);
                v___x_2994_ = leanh::lean_box(0);
                v___x_2995_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_2995_, 0, v___x_2985_);
                leanh::lean_ctor_set(v___x_2995_, 1, v_a_2981_);
                leanh::lean_ctor_set(v___x_2995_, 2, v___y_2988_);
                leanh::lean_ctor_set(v___x_2995_, 3, v___y_2987_);
                leanh::lean_ctor_set(v___x_2995_, 4, v___y_2989_);
                leanh::lean_ctor_set(v___x_2995_, 5, v___x_2991_);
                leanh::lean_ctor_set(v___x_2995_, 6, v___x_2993_);
                leanh::lean_ctor_set(v___x_2995_, 7, v___x_2994_);
                if v_isShared_2984_ == 0 {
                    leanh::lean_ctor_set(v___x_2983_, 0, v___x_2995_);
                    v___x_2997_ = v___x_2983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
                    v___x_2997_ = v_reuseFailAlloc_2998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2997_;
            }
            4 => {
                v_sz_3001_ = lean_array_size(v_textEdits_2976_);
                v___x_3002_ = 0usize;
                v___x_3003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_2970_, v_sz_3001_, v___x_3002_, v_textEdits_2976_);
                v___x_3004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3004_, 0, v___x_3003_);
                if leanh::lean_obj_tag(v_tooltip_x3f_2977_) == 0 {
                    v___x_3005_ = leanh::lean_box(0);
                    v___y_2987_ = v___x_3004_;
                    v___y_2988_ = v___y_3000_;
                    v___y_2989_ = v___x_3005_;
                    state = 2;
                    continue;
                } else {
                    v_val_3006_ = leanh::lean_ctor_get(v_tooltip_x3f_2977_, 0);
                    v_isSharedCheck_3016_ =
                        (!leanh::lean_is_exclusive(v_tooltip_x3f_2977_)) as u8;
                    if v_isSharedCheck_3016_ == 0 {
                        v___x_3008_ = v_tooltip_x3f_2977_;
                        v_isShared_3009_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3006_);
                        leanh::lean_dec(v_tooltip_x3f_2977_);
                        v___x_3008_ = leanh::lean_box(0);
                        v_isShared_3009_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3010_ = 1;
                v___x_3011_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3011_, 0, v_val_3006_);
                leanh::lean_ctor_set_uint8(
                    v___x_3011_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3010_,
                );
                v___x_3012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3012_, 0, v___x_3011_);
                if v_isShared_3009_ == 0 {
                    leanh::lean_ctor_set(v___x_3008_, 0, v___x_3012_);
                    v___x_3014_ = v___x_3008_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
                    v___x_3014_ = v_reuseFailAlloc_3015_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_2987_ = v___x_3004_;
                v___y_2988_ = v___y_3000_;
                v___y_2989_ = v___x_3014_;
                state = 2;
                continue;
            }
            7 => {
                v___x_3022_ = (leanh::lean_unbox(v_val_3018_) as u8);
                leanh::lean_dec(v_val_3018_);
                v___x_3023_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v___x_3022_);
                v___x_3024_ = leanh::lean_box((v___x_3023_) as usize);
                if v_isShared_3021_ == 0 {
                    leanh::lean_ctor_set(v___x_3020_, 0, v___x_3024_);
                    v___x_3026_ = v___x_3020_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_3000_ = v___x_3026_;
                state = 4;
                continue;
            }
            9 => {
                if v_isShared_3033_ == 0 {
                    v___x_3035_ = v___x_3032_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InlayHintInfo_toLspInlayHint___boxed(
    mut v_text_3038_: *mut leanh::LeanObject,
    mut v_i_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v_text_3038_, v_i_3039_);
    return v_res_3041_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__0(
    mut v_a_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = lean_nat_to_int(v_a_3042_);
    return v___x_3043_;
}
pub unsafe fn l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(
    mut v_msg_3044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = leanh::lean_unsigned_to_nat(0);
    v___x_3046_ = lean_panic_fn_borrowed(v___x_3045_, v_msg_3044_);
    return v___x_3046_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(
    mut v_range_3052_: *mut leanh::LeanObject,
    mut v_byteOffset_3053_: *mut leanh::LeanObject,
    mut v_p_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    v_start_3055_ = leanh::lean_ctor_get(v_range_3052_, 0);
    leanh::lean_inc(v_start_3055_);
    v_stop_3056_ = leanh::lean_ctor_get(v_range_3052_, 1);
    leanh::lean_inc(v_stop_3056_);
    leanh::lean_dec_ref(v_range_3052_);
    v___x_3057_ = lean_nat_dec_lt(v_stop_3056_, v_p_3054_);
    if v___x_3057_ == 0 {
        let mut v___x_3058_: u8 = 0;
        v___x_3058_ = lean_nat_dec_lt(v_p_3054_, v_start_3055_);
        if v___x_3058_ == 0 {
            let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0;
            v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1;
            v___x_3061_ = leanh::lean_unsigned_to_nat(87);
            v___x_3062_ = leanh::lean_unsigned_to_nat(6);
            v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2;
            v___x_3064_ = l_Nat_reprFast(v_p_3054_);
            v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
            leanh::lean_dec_ref(v___x_3064_);
            v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3;
            v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
            v___x_3068_ = l_Nat_reprFast(v_start_3055_);
            v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
            leanh::lean_dec_ref(v___x_3068_);
            v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4;
            v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
            v___x_3072_ = l_Nat_reprFast(v_stop_3056_);
            v___x_3073_ = lean_string_append(v___x_3071_, v___x_3072_);
            leanh::lean_dec_ref(v___x_3072_);
            v___x_3074_ = l_mkPanicMessageWithDecl(
                v___x_3059_,
                v___x_3060_,
                v___x_3061_,
                v___x_3062_,
                v___x_3073_,
            );
            leanh::lean_dec_ref(v___x_3073_);
            v___x_3075_ =
                l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_3074_);
            return v___x_3075_;
        } else {
            leanh::lean_dec(v_stop_3056_);
            leanh::lean_dec(v_start_3055_);
            return v_p_3054_;
        }
    } else {
        let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stop_3056_);
        leanh::lean_dec(v_start_3055_);
        v___x_3076_ = lean_nat_to_int(v_p_3054_);
        v___x_3077_ = lean_int_add(v___x_3076_, v_byteOffset_3053_);
        leanh::lean_dec(v___x_3076_);
        v___x_3078_ = l_Int_toNat(v___x_3077_);
        leanh::lean_dec(v___x_3077_);
        return v___x_3078_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___boxed(
    mut v_range_3079_: *mut leanh::LeanObject,
    mut v_byteOffset_3080_: *mut leanh::LeanObject,
    mut v_p_3081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3079_, v_byteOffset_3080_, v_p_3081_);
    leanh::lean_dec(v_byteOffset_3080_);
    return v_res_3082_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(
    mut v_hintMod_3083_: *mut leanh::LeanObject,
    mut v_range_3084_: *mut leanh::LeanObject,
    mut v_byteOffset_3085_: *mut leanh::LeanObject,
    mut v_sz_3086_: usize,
    mut v_i_3087_: usize,
    mut v_bs_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3089_: u8 = 0;
    let mut v_v_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tooltip_x3f_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_x3f_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v_start_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut v_unused_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3089_ = lean_usize_dec_lt(v_i_3087_, v_sz_3086_);
                if v___x_3089_ == 0 {
                    leanh::lean_dec_ref(v_range_3084_);
                    return v_bs_3088_;
                } else {
                    v_v_3090_ = lean_array_uget(v_bs_3088_, v_i_3087_);
                    v_value_3091_ = leanh::lean_ctor_get(v_v_3090_, 0);
                    v_tooltip_x3f_3092_ = leanh::lean_ctor_get(v_v_3090_, 1);
                    v_location_x3f_3093_ = leanh::lean_ctor_get(v_v_3090_, 2);
                    v_isSharedCheck_3136_ = (!leanh::lean_is_exclusive(v_v_3090_)) as u8;
                    if v_isSharedCheck_3136_ == 0 {
                        v___x_3095_ = v_v_3090_;
                        v_isShared_3096_ = v_isSharedCheck_3136_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_location_x3f_3093_);
                        leanh::lean_inc(v_tooltip_x3f_3092_);
                        leanh::lean_inc(v_value_3091_);
                        leanh::lean_dec(v_v_3090_);
                        v___x_3095_ = leanh::lean_box(0);
                        v_isShared_3096_ = v_isSharedCheck_3136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3097_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3098_ = lean_array_uset(v_bs_3088_, v_i_3087_, v___x_3097_);
                if leanh::lean_obj_tag(v_location_x3f_3093_) == 0 {
                    leanh::lean_del_object(v___x_3095_);
                    v___x_3111_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3111_, 0, v_value_3091_);
                    leanh::lean_ctor_set(v___x_3111_, 1, v_tooltip_x3f_3092_);
                    leanh::lean_ctor_set(v___x_3111_, 2, v_location_x3f_3093_);
                    v___y_3100_ = v___x_3111_;
                    state = 2;
                    continue;
                } else {
                    v_val_3112_ = leanh::lean_ctor_get(v_location_x3f_3093_, 0);
                    leanh::lean_inc(v_val_3112_);
                    leanh::lean_dec_ref_known(v_location_x3f_3093_, 1);
                    v_module_3113_ = leanh::lean_ctor_get(v_val_3112_, 0);
                    v_range_3114_ = leanh::lean_ctor_get(v_val_3112_, 1);
                    leanh::lean_inc_ref(v_range_3114_);
                    v___x_3115_ = lean_name_eq(v_module_3113_, v_hintMod_3083_);
                    if v___x_3115_ == 0 {
                        leanh::lean_dec_ref(v_range_3114_);
                        v___y_3106_ = v_val_3112_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_module_3113_);
                        v_isSharedCheck_3133_ =
                            (!leanh::lean_is_exclusive(v_val_3112_)) as u8;
                        if v_isSharedCheck_3133_ == 0 {
                            v_unused_3134_ = leanh::lean_ctor_get(v_val_3112_, 1);
                            leanh::lean_dec(v_unused_3134_);
                            v_unused_3135_ = leanh::lean_ctor_get(v_val_3112_, 0);
                            leanh::lean_dec(v_unused_3135_);
                            v___x_3117_ = v_val_3112_;
                            v_isShared_3118_ = v_isSharedCheck_3133_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_3112_);
                            v___x_3117_ = leanh::lean_box(0);
                            v_isShared_3118_ = v_isSharedCheck_3133_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3101_ = 1usize;
                v___x_3102_ = lean_usize_add(v_i_3087_, v___x_3101_);
                v___x_3103_ = lean_array_uset(v_bs_x27_3098_, v_i_3087_, v___y_3100_);
                v_i_3087_ = v___x_3102_;
                v_bs_3088_ = v___x_3103_;
                state = 0;
                continue;
            }
            3 => {
                v___x_3107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3107_, 0, v___y_3106_);
                if v_isShared_3096_ == 0 {
                    leanh::lean_ctor_set(v___x_3095_, 2, v___x_3107_);
                    v___x_3109_ = v___x_3095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_value_3091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_tooltip_x3f_3092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 2, v___x_3107_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3100_ = v___x_3109_;
                state = 2;
                continue;
            }
            5 => {
                v_start_3119_ = leanh::lean_ctor_get(v_range_3114_, 0);
                v_stop_3120_ = leanh::lean_ctor_get(v_range_3114_, 1);
                v_isSharedCheck_3132_ = (!leanh::lean_is_exclusive(v_range_3114_)) as u8;
                if v_isSharedCheck_3132_ == 0 {
                    v___x_3122_ = v_range_3114_;
                    v_isShared_3123_ = v_isSharedCheck_3132_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3120_);
                    leanh::lean_inc(v_start_3119_);
                    leanh::lean_dec(v_range_3114_);
                    v___x_3122_ = leanh::lean_box(0);
                    v_isShared_3123_ = v_isSharedCheck_3132_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref_n(v_range_3084_, 2);
                v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3084_, v_byteOffset_3085_, v_start_3119_);
                v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3084_, v_byteOffset_3085_, v_stop_3120_);
                if v_isShared_3123_ == 0 {
                    leanh::lean_ctor_set(v___x_3122_, 1, v___x_3125_);
                    leanh::lean_ctor_set(v___x_3122_, 0, v___x_3124_);
                    v___x_3127_ = v___x_3122_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3125_);
                    v___x_3127_ = v_reuseFailAlloc_3131_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3118_ == 0 {
                    leanh::lean_ctor_set(v___x_3117_, 1, v___x_3127_);
                    v___x_3129_ = v___x_3117_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_module_3113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3127_);
                    v___x_3129_ = v_reuseFailAlloc_3130_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_3106_ = v___x_3129_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(
    mut v_hintMod_3137_: *mut leanh::LeanObject,
    mut v_range_3138_: *mut leanh::LeanObject,
    mut v_byteOffset_3139_: *mut leanh::LeanObject,
    mut v_sz_3140_: *mut leanh::LeanObject,
    mut v_i_3141_: *mut leanh::LeanObject,
    mut v_bs_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3143_: usize = 0;
    let mut v_i_boxed_3144_: usize = 0;
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3143_ = leanh::lean_unbox_usize(v_sz_3140_);
    leanh::lean_dec(v_sz_3140_);
    v_i_boxed_3144_ = leanh::lean_unbox_usize(v_i_3141_);
    leanh::lean_dec(v_i_3141_);
    v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_3137_, v_range_3138_, v_byteOffset_3139_, v_sz_boxed_3143_, v_i_boxed_3144_, v_bs_3142_);
    leanh::lean_dec(v_byteOffset_3139_);
    leanh::lean_dec(v_hintMod_3137_);
    return v_res_3145_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(
    mut v_hintMod_3146_: *mut leanh::LeanObject,
    mut v_range_3147_: *mut leanh::LeanObject,
    mut v_byteOffset_3148_: *mut leanh::LeanObject,
    mut v_sz_3149_: usize,
    mut v_i_3150_: usize,
    mut v_bs_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3152_: u8 = 0;
    let mut v_v_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tooltip_x3f_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_x3f_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v_start_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v_isSharedCheck_3196_: u8 = 0;
    let mut v_unused_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3152_ = lean_usize_dec_lt(v_i_3150_, v_sz_3149_);
                if v___x_3152_ == 0 {
                    leanh::lean_dec_ref(v_range_3147_);
                    return v_bs_3151_;
                } else {
                    v_v_3153_ = lean_array_uget(v_bs_3151_, v_i_3150_);
                    v_value_3154_ = leanh::lean_ctor_get(v_v_3153_, 0);
                    v_tooltip_x3f_3155_ = leanh::lean_ctor_get(v_v_3153_, 1);
                    v_location_x3f_3156_ = leanh::lean_ctor_get(v_v_3153_, 2);
                    v_isSharedCheck_3199_ = (!leanh::lean_is_exclusive(v_v_3153_)) as u8;
                    if v_isSharedCheck_3199_ == 0 {
                        v___x_3158_ = v_v_3153_;
                        v_isShared_3159_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_location_x3f_3156_);
                        leanh::lean_inc(v_tooltip_x3f_3155_);
                        leanh::lean_inc(v_value_3154_);
                        leanh::lean_dec(v_v_3153_);
                        v___x_3158_ = leanh::lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3160_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3161_ = lean_array_uset(v_bs_3151_, v_i_3150_, v___x_3160_);
                if leanh::lean_obj_tag(v_location_x3f_3156_) == 0 {
                    leanh::lean_del_object(v___x_3158_);
                    v___x_3174_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3174_, 0, v_value_3154_);
                    leanh::lean_ctor_set(v___x_3174_, 1, v_tooltip_x3f_3155_);
                    leanh::lean_ctor_set(v___x_3174_, 2, v_location_x3f_3156_);
                    v___y_3163_ = v___x_3174_;
                    state = 2;
                    continue;
                } else {
                    v_val_3175_ = leanh::lean_ctor_get(v_location_x3f_3156_, 0);
                    leanh::lean_inc(v_val_3175_);
                    leanh::lean_dec_ref_known(v_location_x3f_3156_, 1);
                    v_module_3176_ = leanh::lean_ctor_get(v_val_3175_, 0);
                    v_range_3177_ = leanh::lean_ctor_get(v_val_3175_, 1);
                    leanh::lean_inc_ref(v_range_3177_);
                    v___x_3178_ = lean_name_eq(v_module_3176_, v_hintMod_3146_);
                    if v___x_3178_ == 0 {
                        leanh::lean_dec_ref(v_range_3177_);
                        v___y_3169_ = v_val_3175_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_module_3176_);
                        v_isSharedCheck_3196_ =
                            (!leanh::lean_is_exclusive(v_val_3175_)) as u8;
                        if v_isSharedCheck_3196_ == 0 {
                            v_unused_3197_ = leanh::lean_ctor_get(v_val_3175_, 1);
                            leanh::lean_dec(v_unused_3197_);
                            v_unused_3198_ = leanh::lean_ctor_get(v_val_3175_, 0);
                            leanh::lean_dec(v_unused_3198_);
                            v___x_3180_ = v_val_3175_;
                            v_isShared_3181_ = v_isSharedCheck_3196_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_3175_);
                            v___x_3180_ = leanh::lean_box(0);
                            v_isShared_3181_ = v_isSharedCheck_3196_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3164_ = 1usize;
                v___x_3165_ = lean_usize_add(v_i_3150_, v___x_3164_);
                v___x_3166_ = lean_array_uset(v_bs_x27_3161_, v_i_3150_, v___y_3163_);
                v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_3146_, v_range_3147_, v_byteOffset_3148_, v_sz_3149_, v___x_3165_, v___x_3166_);
                return v___x_3167_;
            }
            3 => {
                v___x_3170_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3170_, 0, v___y_3169_);
                if v_isShared_3159_ == 0 {
                    leanh::lean_ctor_set(v___x_3158_, 2, v___x_3170_);
                    v___x_3172_ = v___x_3158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3173_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_value_3154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_tooltip_x3f_3155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 2, v___x_3170_);
                    v___x_3172_ = v_reuseFailAlloc_3173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3163_ = v___x_3172_;
                state = 2;
                continue;
            }
            5 => {
                v_start_3182_ = leanh::lean_ctor_get(v_range_3177_, 0);
                v_stop_3183_ = leanh::lean_ctor_get(v_range_3177_, 1);
                v_isSharedCheck_3195_ = (!leanh::lean_is_exclusive(v_range_3177_)) as u8;
                if v_isSharedCheck_3195_ == 0 {
                    v___x_3185_ = v_range_3177_;
                    v_isShared_3186_ = v_isSharedCheck_3195_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3183_);
                    leanh::lean_inc(v_start_3182_);
                    leanh::lean_dec(v_range_3177_);
                    v___x_3185_ = leanh::lean_box(0);
                    v_isShared_3186_ = v_isSharedCheck_3195_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref_n(v_range_3147_, 2);
                v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3147_, v_byteOffset_3148_, v_start_3182_);
                v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3147_, v_byteOffset_3148_, v_stop_3183_);
                if v_isShared_3186_ == 0 {
                    leanh::lean_ctor_set(v___x_3185_, 1, v___x_3188_);
                    leanh::lean_ctor_set(v___x_3185_, 0, v___x_3187_);
                    v___x_3190_ = v___x_3185_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3188_);
                    v___x_3190_ = v_reuseFailAlloc_3194_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3181_ == 0 {
                    leanh::lean_ctor_set(v___x_3180_, 1, v___x_3190_);
                    v___x_3192_ = v___x_3180_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_module_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3190_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_3169_ = v___x_3192_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(
    mut v_hintMod_3200_: *mut leanh::LeanObject,
    mut v_range_3201_: *mut leanh::LeanObject,
    mut v_byteOffset_3202_: *mut leanh::LeanObject,
    mut v_sz_3203_: *mut leanh::LeanObject,
    mut v_i_3204_: *mut leanh::LeanObject,
    mut v_bs_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3206_: usize = 0;
    let mut v_i_boxed_3207_: usize = 0;
    let mut v_res_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3206_ = leanh::lean_unbox_usize(v_sz_3203_);
    leanh::lean_dec(v_sz_3203_);
    v_i_boxed_3207_ = leanh::lean_unbox_usize(v_i_3204_);
    leanh::lean_dec(v_i_3204_);
    v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_3200_, v_range_3201_, v_byteOffset_3202_, v_sz_boxed_3206_, v_i_boxed_3207_, v_bs_3205_);
    leanh::lean_dec(v_byteOffset_3202_);
    leanh::lean_dec(v_hintMod_3200_);
    return v_res_3208_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(
    mut v_range_3209_: *mut leanh::LeanObject,
    mut v_byteOffset_3210_: *mut leanh::LeanObject,
    mut v_sz_3211_: usize,
    mut v_i_3212_: usize,
    mut v_bs_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3214_: u8 = 0;
    let mut v_v_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v_start_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: usize = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3214_ = lean_usize_dec_lt(v_i_3212_, v_sz_3211_);
                if v___x_3214_ == 0 {
                    leanh::lean_dec_ref(v_range_3209_);
                    return v_bs_3213_;
                } else {
                    v_v_3215_ = lean_array_uget(v_bs_3213_, v_i_3212_);
                    v_range_3216_ = leanh::lean_ctor_get(v_v_3215_, 0);
                    v_newText_3217_ = leanh::lean_ctor_get(v_v_3215_, 1);
                    v_isSharedCheck_3241_ = (!leanh::lean_is_exclusive(v_v_3215_)) as u8;
                    if v_isSharedCheck_3241_ == 0 {
                        v___x_3219_ = v_v_3215_;
                        v_isShared_3220_ = v_isSharedCheck_3241_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_newText_3217_);
                        leanh::lean_inc(v_range_3216_);
                        leanh::lean_dec(v_v_3215_);
                        v___x_3219_ = leanh::lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_start_3221_ = leanh::lean_ctor_get(v_range_3216_, 0);
                v_stop_3222_ = leanh::lean_ctor_get(v_range_3216_, 1);
                v_isSharedCheck_3240_ = (!leanh::lean_is_exclusive(v_range_3216_)) as u8;
                if v_isSharedCheck_3240_ == 0 {
                    v___x_3224_ = v_range_3216_;
                    v_isShared_3225_ = v_isSharedCheck_3240_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3222_);
                    leanh::lean_inc(v_start_3221_);
                    leanh::lean_dec(v_range_3216_);
                    v___x_3224_ = leanh::lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3226_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3227_ = lean_array_uset(v_bs_3213_, v_i_3212_, v___x_3226_);
                leanh::lean_inc_ref_n(v_range_3209_, 2);
                v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3209_, v_byteOffset_3210_, v_start_3221_);
                v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3209_, v_byteOffset_3210_, v_stop_3222_);
                if v_isShared_3225_ == 0 {
                    leanh::lean_ctor_set(v___x_3224_, 1, v___x_3229_);
                    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3228_);
                    v___x_3231_ = v___x_3224_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 1, v___x_3229_);
                    v___x_3231_ = v_reuseFailAlloc_3239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3220_ == 0 {
                    leanh::lean_ctor_set(v___x_3219_, 0, v___x_3231_);
                    v___x_3233_ = v___x_3219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_newText_3217_);
                    v___x_3233_ = v_reuseFailAlloc_3238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3234_ = 1usize;
                v___x_3235_ = lean_usize_add(v_i_3212_, v___x_3234_);
                v___x_3236_ = lean_array_uset(v_bs_x27_3227_, v_i_3212_, v___x_3233_);
                v_i_3212_ = v___x_3235_;
                v_bs_3213_ = v___x_3236_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(
    mut v_range_3242_: *mut leanh::LeanObject,
    mut v_byteOffset_3243_: *mut leanh::LeanObject,
    mut v_sz_3244_: *mut leanh::LeanObject,
    mut v_i_3245_: *mut leanh::LeanObject,
    mut v_bs_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3247_: usize = 0;
    let mut v_i_boxed_3248_: usize = 0;
    let mut v_res_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3247_ = leanh::lean_unbox_usize(v_sz_3244_);
    leanh::lean_dec(v_sz_3244_);
    v_i_boxed_3248_ = leanh::lean_unbox_usize(v_i_3245_);
    leanh::lean_dec(v_i_3245_);
    v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_3242_, v_byteOffset_3243_, v_sz_boxed_3247_, v_i_boxed_3248_, v_bs_3246_);
    leanh::lean_dec(v_byteOffset_3243_);
    return v_res_3249_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(
    mut v_range_3250_: *mut leanh::LeanObject,
    mut v_byteOffset_3251_: *mut leanh::LeanObject,
    mut v_sz_3252_: usize,
    mut v_i_3253_: usize,
    mut v_bs_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3255_: u8 = 0;
    let mut v_v_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_start_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
                if v___x_3255_ == 0 {
                    leanh::lean_dec_ref(v_range_3250_);
                    return v_bs_3254_;
                } else {
                    v_v_3256_ = lean_array_uget(v_bs_3254_, v_i_3253_);
                    v_range_3257_ = leanh::lean_ctor_get(v_v_3256_, 0);
                    v_newText_3258_ = leanh::lean_ctor_get(v_v_3256_, 1);
                    v_isSharedCheck_3282_ = (!leanh::lean_is_exclusive(v_v_3256_)) as u8;
                    if v_isSharedCheck_3282_ == 0 {
                        v___x_3260_ = v_v_3256_;
                        v_isShared_3261_ = v_isSharedCheck_3282_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_newText_3258_);
                        leanh::lean_inc(v_range_3257_);
                        leanh::lean_dec(v_v_3256_);
                        v___x_3260_ = leanh::lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_start_3262_ = leanh::lean_ctor_get(v_range_3257_, 0);
                v_stop_3263_ = leanh::lean_ctor_get(v_range_3257_, 1);
                v_isSharedCheck_3281_ = (!leanh::lean_is_exclusive(v_range_3257_)) as u8;
                if v_isSharedCheck_3281_ == 0 {
                    v___x_3265_ = v_range_3257_;
                    v_isShared_3266_ = v_isSharedCheck_3281_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3263_);
                    leanh::lean_inc(v_start_3262_);
                    leanh::lean_dec(v_range_3257_);
                    v___x_3265_ = leanh::lean_box(0);
                    v_isShared_3266_ = v_isSharedCheck_3281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3267_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3268_ = lean_array_uset(v_bs_3254_, v_i_3253_, v___x_3267_);
                leanh::lean_inc_ref_n(v_range_3250_, 2);
                v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3250_, v_byteOffset_3251_, v_start_3262_);
                v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_3250_, v_byteOffset_3251_, v_stop_3263_);
                if v_isShared_3266_ == 0 {
                    leanh::lean_ctor_set(v___x_3265_, 1, v___x_3270_);
                    leanh::lean_ctor_set(v___x_3265_, 0, v___x_3269_);
                    v___x_3272_ = v___x_3265_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 1, v___x_3270_);
                    v___x_3272_ = v_reuseFailAlloc_3280_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3261_ == 0 {
                    leanh::lean_ctor_set(v___x_3260_, 0, v___x_3272_);
                    v___x_3274_ = v___x_3260_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_newText_3258_);
                    v___x_3274_ = v_reuseFailAlloc_3279_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3275_ = 1usize;
                v___x_3276_ = lean_usize_add(v_i_3253_, v___x_3275_);
                v___x_3277_ = lean_array_uset(v_bs_x27_3268_, v_i_3253_, v___x_3274_);
                v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_3250_, v_byteOffset_3251_, v_sz_3252_, v___x_3276_, v___x_3277_);
                return v___x_3278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(
    mut v_range_3283_: *mut leanh::LeanObject,
    mut v_byteOffset_3284_: *mut leanh::LeanObject,
    mut v_sz_3285_: *mut leanh::LeanObject,
    mut v_i_3286_: *mut leanh::LeanObject,
    mut v_bs_3287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3288_: usize = 0;
    let mut v_i_boxed_3289_: usize = 0;
    let mut v_res_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3288_ = leanh::lean_unbox_usize(v_sz_3285_);
    leanh::lean_dec(v_sz_3285_);
    v_i_boxed_3289_ = leanh::lean_unbox_usize(v_i_3286_);
    leanh::lean_dec(v_i_3286_);
    v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_3283_, v_byteOffset_3284_, v_sz_boxed_3288_, v_i_boxed_3289_, v_bs_3287_);
    leanh::lean_dec(v_byteOffset_3284_);
    return v_res_3290_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(
    mut v_hintMod_3291_: *mut leanh::LeanObject,
    mut v_range_3292_: *mut leanh::LeanObject,
    mut v_as_3293_: *mut leanh::LeanObject,
    mut v_i_3294_: usize,
    mut v_stop_3295_: usize,
) -> u8 {
    let mut v___x_3296_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_x3f_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: u8 = 0;
    let mut v___y_3301_: u8 = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: usize = 0;
    let mut v_val_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3296_ = lean_usize_dec_eq(v_i_3294_, v_stop_3295_);
                if v___x_3296_ == 0 {
                    v___x_3297_ = lean_array_uget_borrowed(v_as_3293_, v_i_3294_);
                    v_location_x3f_3298_ = leanh::lean_ctor_get(v___x_3297_, 2);
                    v___x_3299_ = 1;
                    if leanh::lean_obj_tag(v_location_x3f_3298_) == 0 {
                        v___y_3301_ = v___x_3296_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3305_ = leanh::lean_ctor_get(v_location_x3f_3298_, 0);
                        v_module_3306_ = leanh::lean_ctor_get(v_val_3305_, 0);
                        v_range_3307_ = leanh::lean_ctor_get(v_val_3305_, 1);
                        v___x_3308_ = lean_name_eq(v_module_3306_, v_hintMod_3291_);
                        if v___x_3308_ == 0 {
                            v___y_3301_ = v___x_3308_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3309_ = l_Lean_Syntax_Range_overlaps(
                                v_range_3292_,
                                v_range_3307_,
                                v___x_3308_,
                                v___x_3296_,
                            );
                            v___y_3301_ = v___x_3309_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3310_ = 0;
                    return v___x_3310_;
                }
            }
            1 => {
                if v___y_3301_ == 0 {
                    v___x_3302_ = 1usize;
                    v___x_3303_ = lean_usize_add(v_i_3294_, v___x_3302_);
                    v_i_3294_ = v___x_3303_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3299_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(
    mut v_hintMod_3311_: *mut leanh::LeanObject,
    mut v_range_3312_: *mut leanh::LeanObject,
    mut v_as_3313_: *mut leanh::LeanObject,
    mut v_i_3314_: *mut leanh::LeanObject,
    mut v_stop_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3316_: usize = 0;
    let mut v_stop_boxed_3317_: usize = 0;
    let mut v_res_3318_: u8 = 0;
    let mut v_r_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3316_ = leanh::lean_unbox_usize(v_i_3314_);
    leanh::lean_dec(v_i_3314_);
    v_stop_boxed_3317_ = leanh::lean_unbox_usize(v_stop_3315_);
    leanh::lean_dec(v_stop_3315_);
    v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_3311_, v_range_3312_, v_as_3313_, v_i_boxed_3316_, v_stop_boxed_3317_);
    leanh::lean_dec_ref(v_as_3313_);
    leanh::lean_dec_ref(v_range_3312_);
    leanh::lean_dec(v_hintMod_3311_);
    v_r_3319_ = leanh::lean_box((v_res_3318_) as usize);
    return v_r_3319_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(
    mut v_range_3320_: *mut leanh::LeanObject,
    mut v___x_3321_: u8,
    mut v_as_3322_: *mut leanh::LeanObject,
    mut v_i_3323_: usize,
    mut v_stop_3324_: usize,
) -> u8 {
    let mut v___x_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3325_ = lean_usize_dec_eq(v_i_3323_, v_stop_3324_);
                if v___x_3325_ == 0 {
                    v___x_3326_ = lean_array_uget_borrowed(v_as_3322_, v_i_3323_);
                    v_range_3327_ = leanh::lean_ctor_get(v___x_3326_, 0);
                    v___x_3328_ = 1;
                    v___x_3329_ = l_Lean_Syntax_Range_overlaps(
                        v_range_3320_,
                        v_range_3327_,
                        v___x_3328_,
                        v___x_3321_,
                    );
                    if v___x_3329_ == 0 {
                        v___x_3330_ = 1usize;
                        v___x_3331_ = lean_usize_add(v_i_3323_, v___x_3330_);
                        v_i_3323_ = v___x_3331_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3328_;
                    }
                } else {
                    v___x_3333_ = 0;
                    return v___x_3333_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(
    mut v_range_3334_: *mut leanh::LeanObject,
    mut v___x_3335_: *mut leanh::LeanObject,
    mut v_as_3336_: *mut leanh::LeanObject,
    mut v_i_3337_: *mut leanh::LeanObject,
    mut v_stop_3338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2648__boxed_3339_: u8 = 0;
    let mut v_i_boxed_3340_: usize = 0;
    let mut v_stop_boxed_3341_: usize = 0;
    let mut v_res_3342_: u8 = 0;
    let mut v_r_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2648__boxed_3339_ = (leanh::lean_unbox(v___x_3335_) as u8);
    v_i_boxed_3340_ = leanh::lean_unbox_usize(v_i_3337_);
    leanh::lean_dec(v_i_3337_);
    v_stop_boxed_3341_ = leanh::lean_unbox_usize(v_stop_3338_);
    leanh::lean_dec(v_stop_3338_);
    v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_3334_, v___x_2648__boxed_3339_, v_as_3336_, v_i_boxed_3340_, v_stop_boxed_3341_);
    leanh::lean_dec_ref(v_as_3336_);
    leanh::lean_dec_ref(v_range_3334_);
    v_r_3343_ = leanh::lean_box((v_res_3342_) as usize);
    return v_r_3343_;
}
pub unsafe fn l_Lean_Server_FileWorker_applyEditToHint_x3f(
    mut v_hintMod_3344_: *mut leanh::LeanObject,
    mut v_ihi_3345_: *mut leanh::LeanObject,
    mut v_range_3346_: *mut leanh::LeanObject,
    mut v_newText_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_position_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdits_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tooltip_x3f_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paddingLeft_3353_: u8 = 0;
    let mut v_paddingRight_3354_: u8 = 0;
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___y_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3362_: usize = 0;
    let mut v___x_3363_: usize = 0;
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v_sz_3376_: usize = 0;
    let mut v___x_3377_: usize = 0;
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut v___y_3384_: u8 = 0;
    let mut v___y_3385_: u8 = 0;
    let mut v_start_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_byteOffset_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3418_: u8 = 0;
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: u8 = 0;
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: usize = 0;
    let mut v___x_3425_: usize = 0;
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v_p_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: u8 = 0;
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_position_3348_ = leanh::lean_ctor_get(v_ihi_3345_, 0);
                v_label_3349_ = leanh::lean_ctor_get(v_ihi_3345_, 1);
                v_kind_x3f_3350_ = leanh::lean_ctor_get(v_ihi_3345_, 2);
                v_textEdits_3351_ = leanh::lean_ctor_get(v_ihi_3345_, 3);
                v_tooltip_x3f_3352_ = leanh::lean_ctor_get(v_ihi_3345_, 4);
                v_paddingLeft_3353_ = leanh::lean_ctor_get_uint8(
                    v_ihi_3345_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_paddingRight_3354_ = leanh::lean_ctor_get_uint8(
                    v_ihi_3345_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_isSharedCheck_3435_ = (!leanh::lean_is_exclusive(v_ihi_3345_)) as u8;
                if v_isSharedCheck_3435_ == 0 {
                    v___x_3356_ = v_ihi_3345_;
                    v_isShared_3357_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tooltip_x3f_3352_);
                    leanh::lean_inc(v_textEdits_3351_);
                    leanh::lean_inc(v_kind_x3f_3350_);
                    leanh::lean_inc(v_label_3349_);
                    leanh::lean_inc(v_position_3348_);
                    leanh::lean_dec(v_ihi_3345_);
                    v___x_3356_ = leanh::lean_box(0);
                    v_isShared_3357_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_label_3349_) == 0 {
                    v___x_3427_ = 0;
                    v___y_3418_ = v___x_3427_;
                    state = 8;
                    continue;
                } else {
                    v_p_3428_ = leanh::lean_ctor_get(v_label_3349_, 0);
                    v___x_3429_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3430_ = lean_array_get_size(v_p_3428_);
                    v___x_3431_ = lean_nat_dec_lt(v___x_3429_, v___x_3430_);
                    if v___x_3431_ == 0 {
                        v___y_3418_ = v___x_3431_;
                        state = 8;
                        continue;
                    } else {
                        if v___x_3431_ == 0 {
                            v___y_3418_ = v___x_3431_;
                            state = 8;
                            continue;
                        } else {
                            v___x_3432_ = 0usize;
                            v___x_3433_ = lean_usize_of_nat(v___x_3430_);
                            v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_3344_, v_range_3346_, v_p_3428_, v___x_3432_, v___x_3433_);
                            v___y_3418_ = v___x_3434_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_sz_3362_ = lean_array_size(v_textEdits_3351_);
                v___x_3363_ = 0usize;
                v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_3346_, v___y_3360_, v_sz_3362_, v___x_3363_, v_textEdits_3351_);
                leanh::lean_dec(v___y_3360_);
                if v_isShared_3357_ == 0 {
                    leanh::lean_ctor_set(v___x_3356_, 3, v___x_3364_);
                    leanh::lean_ctor_set(v___x_3356_, 1, v___y_3361_);
                    leanh::lean_ctor_set(v___x_3356_, 0, v___y_3359_);
                    v___x_3366_ = v___x_3356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___y_3359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___y_3361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_kind_x3f_3350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 3, v___x_3364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_tooltip_x3f_3352_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3368_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_paddingLeft_3353_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3368_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v_paddingRight_3354_,
                    );
                    v___x_3366_ = v_reuseFailAlloc_3368_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3367_, 0, v___x_3366_);
                return v___x_3367_;
            }
            4 => {
                if leanh::lean_obj_tag(v_label_3349_) == 0 {
                    v___y_3359_ = v___y_3371_;
                    v___y_3360_ = v___y_3370_;
                    v___y_3361_ = v_label_3349_;
                    state = 2;
                    continue;
                } else {
                    v_p_3372_ = leanh::lean_ctor_get(v_label_3349_, 0);
                    v_isSharedCheck_3382_ = (!leanh::lean_is_exclusive(v_label_3349_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3374_ = v_label_3349_;
                        v_isShared_3375_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_3372_);
                        leanh::lean_dec(v_label_3349_);
                        v___x_3374_ = leanh::lean_box(0);
                        v_isShared_3375_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_sz_3376_ = lean_array_size(v_p_3372_);
                v___x_3377_ = 0usize;
                leanh::lean_inc_ref(v_range_3346_);
                v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_3344_, v_range_3346_, v___y_3370_, v_sz_3376_, v___x_3377_, v_p_3372_);
                if v_isShared_3375_ == 0 {
                    leanh::lean_ctor_set(v___x_3374_, 0, v___x_3378_);
                    v___x_3380_ = v___x_3374_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_3359_ = v___y_3371_;
                v___y_3360_ = v___y_3370_;
                v___y_3361_ = v___x_3380_;
                state = 2;
                continue;
            }
            7 => {
                if v___y_3385_ == 0 {
                    if v___y_3384_ == 0 {
                        v_start_3386_ = leanh::lean_ctor_get(v_range_3346_, 0);
                        v_stop_3387_ = leanh::lean_ctor_get(v_range_3346_, 1);
                        v___x_3388_ = lean_string_utf8_byte_size(v_newText_3347_);
                        v___x_3389_ = lean_nat_to_int(v___x_3388_);
                        v___x_3390_ = l_Lean_Syntax_Range_bsize(v_range_3346_);
                        v___x_3391_ = lean_nat_to_int(v___x_3390_);
                        v_byteOffset_3392_ = lean_int_sub(v___x_3389_, v___x_3391_);
                        leanh::lean_dec(v___x_3391_);
                        leanh::lean_dec(v___x_3389_);
                        v___x_3393_ = lean_nat_dec_lt(v_stop_3387_, v_position_3348_);
                        if v___x_3393_ == 0 {
                            v___x_3394_ = lean_nat_dec_lt(v_position_3348_, v_start_3386_);
                            if v___x_3394_ == 0 {
                                v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0;
                                v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1;
                                v___x_3397_ = leanh::lean_unsigned_to_nat(87);
                                v___x_3398_ = leanh::lean_unsigned_to_nat(6);
                                v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2;
                                v___x_3400_ = l_Nat_reprFast(v_position_3348_);
                                v___x_3401_ = lean_string_append(v___x_3399_, v___x_3400_);
                                leanh::lean_dec_ref(v___x_3400_);
                                v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3;
                                v___x_3403_ = lean_string_append(v___x_3401_, v___x_3402_);
                                leanh::lean_inc(v_start_3386_);
                                v___x_3404_ = l_Nat_reprFast(v_start_3386_);
                                v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
                                leanh::lean_dec_ref(v___x_3404_);
                                v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4;
                                v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
                                leanh::lean_inc(v_stop_3387_);
                                v___x_3408_ = l_Nat_reprFast(v_stop_3387_);
                                v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
                                leanh::lean_dec_ref(v___x_3408_);
                                v___x_3410_ = l_mkPanicMessageWithDecl(
                                    v___x_3395_,
                                    v___x_3396_,
                                    v___x_3397_,
                                    v___x_3398_,
                                    v___x_3409_,
                                );
                                leanh::lean_dec_ref(v___x_3409_);
                                v___x_3411_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_3410_);
                                v___y_3370_ = v_byteOffset_3392_;
                                v___y_3371_ = v___x_3411_;
                                state = 4;
                                continue;
                            } else {
                                v___y_3370_ = v_byteOffset_3392_;
                                v___y_3371_ = v_position_3348_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_3412_ = lean_nat_to_int(v_position_3348_);
                            v___x_3413_ = lean_int_add(v___x_3412_, v_byteOffset_3392_);
                            leanh::lean_dec(v___x_3412_);
                            v___x_3414_ = l_Int_toNat(v___x_3413_);
                            leanh::lean_dec(v___x_3413_);
                            v___y_3370_ = v_byteOffset_3392_;
                            v___y_3371_ = v___x_3414_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3356_);
                        leanh::lean_dec(v_tooltip_x3f_3352_);
                        leanh::lean_dec_ref(v_textEdits_3351_);
                        leanh::lean_dec(v_kind_x3f_3350_);
                        leanh::lean_dec_ref(v_label_3349_);
                        leanh::lean_dec(v_position_3348_);
                        leanh::lean_dec_ref(v_range_3346_);
                        v___x_3415_ = leanh::lean_box(0);
                        return v___x_3415_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3356_);
                    leanh::lean_dec(v_tooltip_x3f_3352_);
                    leanh::lean_dec_ref(v_textEdits_3351_);
                    leanh::lean_dec(v_kind_x3f_3350_);
                    leanh::lean_dec_ref(v_label_3349_);
                    leanh::lean_dec(v_position_3348_);
                    leanh::lean_dec_ref(v_range_3346_);
                    v___x_3416_ = leanh::lean_box(0);
                    return v___x_3416_;
                }
            }
            8 => {
                v___x_3419_ = 1;
                v___x_3420_ =
                    l_Lean_Syntax_Range_contains(v_range_3346_, v_position_3348_, v___x_3419_);
                if v___x_3420_ == 0 {
                    v___x_3421_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3422_ = lean_array_get_size(v_textEdits_3351_);
                    v___x_3423_ = lean_nat_dec_lt(v___x_3421_, v___x_3422_);
                    if v___x_3423_ == 0 {
                        v___y_3384_ = v___y_3418_;
                        v___y_3385_ = v___x_3420_;
                        state = 7;
                        continue;
                    } else {
                        if v___x_3423_ == 0 {
                            v___y_3384_ = v___y_3418_;
                            v___y_3385_ = v___x_3420_;
                            state = 7;
                            continue;
                        } else {
                            v___x_3424_ = 0usize;
                            v___x_3425_ = lean_usize_of_nat(v___x_3422_);
                            v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_3346_, v___x_3420_, v_textEdits_3351_, v___x_3424_, v___x_3425_);
                            v___y_3384_ = v___y_3418_;
                            v___y_3385_ = v___x_3426_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___y_3384_ = v___y_3418_;
                    v___y_3385_ = v___x_3420_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(
    mut v_hintMod_3436_: *mut leanh::LeanObject,
    mut v_ihi_3437_: *mut leanh::LeanObject,
    mut v_range_3438_: *mut leanh::LeanObject,
    mut v_newText_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3440_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(
        v_hintMod_3436_,
        v_ihi_3437_,
        v_range_3438_,
        v_newText_3439_,
    );
    leanh::lean_dec_ref(v_newText_3439_);
    leanh::lean_dec(v_hintMod_3436_);
    return v_res_3440_;
}
pub unsafe fn _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_3470_ = leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_3470_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3470_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3470_, 2, v___x_3469_);
    return v___x_3470_;
}
pub unsafe fn l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(
    mut v_msg_3471_: *mut leanh::LeanObject,
    mut v___y_3472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17537__overap_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0,
    );
    v___f_3475_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3475_, 0, v___x_3474_);
    v___x_17537__overap_3476_ = lean_panic_fn_borrowed(v___f_3475_, v_msg_3471_);
    leanh::lean_dec_ref(v___f_3475_);
    leanh::lean_inc_ref(v___y_3472_);
    v___x_3477_ = leanh::lean_apply_2(
        v___x_17537__overap_3476_,
        v___y_3472_,
        leanh::lean_box(0),
    );
    return v___x_3477_;
}
pub unsafe fn l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(
    mut v_msg_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ =
        l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_3478_, v___y_3479_);
    leanh::lean_dec_ref(v___y_3479_);
    return v_res_3481_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(
    mut v___x_3482_: u8,
    mut v_x_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v_x_3485_: *mut leanh::LeanObject,
    mut v___y_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = leanh::lean_box((v___x_3482_) as usize);
    v___x_3490_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3490_, 0, v___x_3489_);
    leanh::lean_ctor_set(v___x_3490_, 1, v___y_3486_);
    v___x_3491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(
    mut v___x_3492_: *mut leanh::LeanObject,
    mut v_x_3493_: *mut leanh::LeanObject,
    mut v_x_3494_: *mut leanh::LeanObject,
    mut v_x_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
    mut v___y_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_20479__boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_20479__boxed_3499_ = (leanh::lean_unbox(v___x_3492_) as u8);
    v_res_3500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_20479__boxed_3499_, v_x_3493_, v_x_3494_, v_x_3495_, v___y_3496_, v___y_3497_);
    leanh::lean_dec_ref(v___y_3497_);
    leanh::lean_dec_ref(v_x_3495_);
    leanh::lean_dec_ref(v_x_3494_);
    leanh::lean_dec_ref(v_x_3493_);
    return v_res_3500_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(
    mut v_ci_3501_: *mut leanh::LeanObject,
    mut v_i_3502_: *mut leanh::LeanObject,
    mut v_x_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v_toInlayHintInfo_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut v_a_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_i_3502_) == 10 {
                    v_i_3507_ = leanh::lean_ctor_get(v_i_3502_, 0);
                    v_isSharedCheck_3542_ = (!leanh::lean_is_exclusive(v_i_3502_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3509_ = v_i_3502_;
                        v_isShared_3510_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_3507_);
                        leanh::lean_dec(v_i_3502_);
                        v___x_3509_ = leanh::lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_i_3502_);
                    leanh::lean_dec_ref(v_ci_3501_);
                    v___x_3543_ = leanh::lean_box(0);
                    v___x_3544_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                    leanh::lean_ctor_set(v___x_3544_, 1, v___y_3504_);
                    v___x_3545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3545_, 0, v___x_3544_);
                    return v___x_3545_;
                }
            }
            1 => {
                v___x_3511_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_i_3507_);
                leanh::lean_dec_ref(v_i_3507_);
                if leanh::lean_obj_tag(v___x_3511_) == 1 {
                    leanh::lean_del_object(v___x_3509_);
                    v_val_3512_ = leanh::lean_ctor_get(v___x_3511_, 0);
                    leanh::lean_inc(v_val_3512_);
                    leanh::lean_dec_ref_known(v___x_3511_, 1);
                    v_lctx_3513_ = leanh::lean_ctor_get(v_val_3512_, 1);
                    leanh::lean_inc_ref(v_lctx_3513_);
                    v___x_3514_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_InlayHint_resolveDeferred___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___x_3514_, 0, v_val_3512_);
                    v___x_3515_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ci_3501_,
                        v_lctx_3513_,
                        v___x_3514_,
                    );
                    if leanh::lean_obj_tag(v___x_3515_) == 0 {
                        v_a_3516_ = leanh::lean_ctor_get(v___x_3515_, 0);
                        v_isSharedCheck_3527_ =
                            (!leanh::lean_is_exclusive(v___x_3515_)) as u8;
                        if v_isSharedCheck_3527_ == 0 {
                            v___x_3518_ = v___x_3515_;
                            v_isShared_3519_ = v_isSharedCheck_3527_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3516_);
                            leanh::lean_dec(v___x_3515_);
                            v___x_3518_ = leanh::lean_box(0);
                            v_isShared_3519_ = v_isSharedCheck_3527_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3504_);
                        v_a_3528_ = leanh::lean_ctor_get(v___x_3515_, 0);
                        v_isSharedCheck_3536_ =
                            (!leanh::lean_is_exclusive(v___x_3515_)) as u8;
                        if v_isSharedCheck_3536_ == 0 {
                            v___x_3530_ = v___x_3515_;
                            v_isShared_3531_ = v_isSharedCheck_3536_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3528_);
                            leanh::lean_dec(v___x_3515_);
                            v___x_3530_ = leanh::lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3536_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3511_);
                    leanh::lean_dec_ref(v_ci_3501_);
                    v___x_3537_ = leanh::lean_box(0);
                    v___x_3538_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
                    leanh::lean_ctor_set(v___x_3538_, 1, v___y_3504_);
                    if v_isShared_3510_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3509_, 0);
                        leanh::lean_ctor_set(v___x_3509_, 0, v___x_3538_);
                        v___x_3540_ = v___x_3509_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
                        v___x_3540_ = v_reuseFailAlloc_3541_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_toInlayHintInfo_3520_ = leanh::lean_ctor_get(v_a_3516_, 0);
                leanh::lean_inc_ref(v_toInlayHintInfo_3520_);
                leanh::lean_dec(v_a_3516_);
                v___x_3521_ = leanh::lean_box(0);
                v___x_3522_ = lean_array_push(v___y_3504_, v_toInlayHintInfo_3520_);
                v___x_3523_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3523_, 0, v___x_3521_);
                leanh::lean_ctor_set(v___x_3523_, 1, v___x_3522_);
                if v_isShared_3519_ == 0 {
                    leanh::lean_ctor_set(v___x_3518_, 0, v___x_3523_);
                    v___x_3525_ = v___x_3518_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
                    v___x_3525_ = v_reuseFailAlloc_3526_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3525_;
            }
            4 => {
                v___x_3532_ = l_Lean_Server_RequestError_ofIoError(v_a_3528_);
                if v_isShared_3531_ == 0 {
                    leanh::lean_ctor_set(v___x_3530_, 0, v___x_3532_);
                    v___x_3534_ = v___x_3530_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
                    v___x_3534_ = v_reuseFailAlloc_3535_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3534_;
            }
            6 => {
                return v___x_3540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(
    mut v_ci_3546_: *mut leanh::LeanObject,
    mut v_i_3547_: *mut leanh::LeanObject,
    mut v_x_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_3546_, v_i_3547_, v_x_3548_, v___y_3549_, v___y_3550_);
    leanh::lean_dec_ref(v___y_3550_);
    leanh::lean_dec_ref(v_x_3548_);
    return v_res_3552_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_3553_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(
    mut v_msg_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19898__overap_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0);
    v___x_3559_ = l_ReaderT_instMonad___redArg(v___x_3558_);
    leanh::lean_inc_ref_n(v___x_3559_, 6);
    v___f_3560_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3560_, 0, v___x_3559_);
    v___f_3561_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3561_, 0, v___x_3559_);
    v___f_3562_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3562_, 0, v___x_3559_);
    v___f_3563_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3563_, 0, v___x_3559_);
    v___x_3564_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3564_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3564_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3564_, 2, v___x_3559_);
    v___x_3565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    leanh::lean_ctor_set(v___x_3565_, 1, v___f_3560_);
    v___x_3566_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_3566_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3566_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3566_, 2, v___x_3559_);
    v___x_3567_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3567_, 0, v___x_3565_);
    leanh::lean_ctor_set(v___x_3567_, 1, v___x_3566_);
    leanh::lean_ctor_set(v___x_3567_, 2, v___f_3561_);
    leanh::lean_ctor_set(v___x_3567_, 3, v___f_3562_);
    leanh::lean_ctor_set(v___x_3567_, 4, v___f_3563_);
    v___x_3568_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3568_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3568_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3568_, 2, v___x_3559_);
    v___x_3569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3569_, 0, v___x_3567_);
    leanh::lean_ctor_set(v___x_3569_, 1, v___x_3568_);
    v___x_3570_ = leanh::lean_box(0);
    v___x_3571_ = l_instInhabitedOfMonad___redArg(v___x_3569_, v___x_3570_);
    v___x_19898__overap_3572_ = lean_panic_fn_borrowed(v___x_3571_, v_msg_3554_);
    leanh::lean_dec(v___x_3571_);
    leanh::lean_inc_ref(v___y_3556_);
    v___x_3573_ = leanh::lean_apply_3(
        v___x_19898__overap_3572_,
        v___y_3555_,
        v___y_3556_,
        leanh::lean_box(0),
    );
    return v___x_3573_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_msg_3574_: *mut leanh::LeanObject,
    mut v___y_3575_: *mut leanh::LeanObject,
    mut v___y_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_3574_, v___y_3575_, v___y_3576_);
    leanh::lean_dec_ref(v___y_3576_);
    return v_res_3578_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2;
    v___x_3583_ = leanh::lean_unsigned_to_nat(21);
    v___x_3584_ = leanh::lean_unsigned_to_nat(65);
    v___x_3585_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1;
    v___x_3586_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0;
    v___x_3587_ = l_mkPanicMessageWithDecl(
        v___x_3586_,
        v___x_3585_,
        v___x_3584_,
        v___x_3583_,
        v___x_3582_,
    );
    return v___x_3587_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(
    mut v_preNode_3588_: *mut leanh::LeanObject,
    mut v_postNode_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
    mut v_x_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v_snd_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3617_: u8 = 0;
    let mut v_fst_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3632_: u8 = 0;
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v_a_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_unused_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_fst_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_a_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_a_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut v_unused_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3591_) {
                0 => {
                    v_i_3595_ = leanh::lean_ctor_get(v_x_3591_, 0);
                    leanh::lean_inc_ref(v_i_3595_);
                    v_t_3596_ = leanh::lean_ctor_get(v_x_3591_, 1);
                    leanh::lean_inc_ref(v_t_3596_);
                    leanh::lean_dec_ref_known(v_x_3591_, 2);
                    v___x_3597_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3595_, v_x_3590_);
                    v_x_3590_ = v___x_3597_;
                    v_x_3591_ = v_t_3596_;
                    state = 0;
                    continue;
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_3590_) == 0 {
                        leanh::lean_dec_ref_known(v_x_3591_, 2);
                        leanh::lean_dec_ref(v_postNode_3589_);
                        leanh::lean_dec_ref(v_preNode_3588_);
                        v___x_3599_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3);
                        v___x_3600_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v___x_3599_, v___y_3592_, v___y_3593_);
                        return v___x_3600_;
                    } else {
                        v_i_3601_ = leanh::lean_ctor_get(v_x_3591_, 0);
                        leanh::lean_inc_ref_n(v_i_3601_, 2);
                        v_children_3602_ = leanh::lean_ctor_get(v_x_3591_, 1);
                        leanh::lean_inc_ref_n(v_children_3602_, 2);
                        leanh::lean_dec_ref_known(v_x_3591_, 2);
                        v_val_3603_ = leanh::lean_ctor_get(v_x_3590_, 0);
                        leanh::lean_inc_n(v_val_3603_, 2);
                        leanh::lean_inc_ref(v_preNode_3588_);
                        leanh::lean_inc_ref(v___y_3593_);
                        v___x_3604_ = leanh::lean_apply_6(
                            v_preNode_3588_,
                            v_val_3603_,
                            v_i_3601_,
                            v_children_3602_,
                            v___y_3592_,
                            v___y_3593_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_3604_) == 0 {
                            v_a_3605_ = leanh::lean_ctor_get(v___x_3604_, 0);
                            leanh::lean_inc(v_a_3605_);
                            leanh::lean_dec_ref_known(v___x_3604_, 1);
                            v_fst_3606_ = leanh::lean_ctor_get(v_a_3605_, 0);
                            v___x_3607_ = (leanh::lean_unbox(v_fst_3606_) as u8);
                            if v___x_3607_ == 0 {
                                leanh::lean_dec_ref(v_preNode_3588_);
                                v_isSharedCheck_3642_ =
                                    (!leanh::lean_is_exclusive(v_x_3590_)) as u8;
                                if v_isSharedCheck_3642_ == 0 {
                                    v_unused_3643_ = leanh::lean_ctor_get(v_x_3590_, 0);
                                    leanh::lean_dec(v_unused_3643_);
                                    v___x_3609_ = v_x_3590_;
                                    v_isShared_3610_ = v_isSharedCheck_3642_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_3590_);
                                    v___x_3609_ = leanh::lean_box(0);
                                    v_isShared_3610_ = v_isSharedCheck_3642_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_snd_3644_ = leanh::lean_ctor_get(v_a_3605_, 1);
                                leanh::lean_inc(v_snd_3644_);
                                leanh::lean_dec(v_a_3605_);
                                v___x_3645_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_3590_, v_i_3601_);
                                v___x_3646_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_3602_);
                                v___x_3647_ = leanh::lean_box(0);
                                leanh::lean_inc_ref(v_postNode_3589_);
                                v___x_3648_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_3588_, v_postNode_3589_, v___x_3645_, v___x_3646_, v___x_3647_, v_snd_3644_, v___y_3593_);
                                if leanh::lean_obj_tag(v___x_3648_) == 0 {
                                    v_a_3649_ = leanh::lean_ctor_get(v___x_3648_, 0);
                                    leanh::lean_inc(v_a_3649_);
                                    leanh::lean_dec_ref_known(v___x_3648_, 1);
                                    v_fst_3650_ = leanh::lean_ctor_get(v_a_3649_, 0);
                                    leanh::lean_inc(v_fst_3650_);
                                    v_snd_3651_ = leanh::lean_ctor_get(v_a_3649_, 1);
                                    leanh::lean_inc(v_snd_3651_);
                                    leanh::lean_dec(v_a_3649_);
                                    leanh::lean_inc_ref(v___y_3593_);
                                    v___x_3652_ = leanh::lean_apply_7(
                                        v_postNode_3589_,
                                        v_val_3603_,
                                        v_i_3601_,
                                        v_children_3602_,
                                        v_fst_3650_,
                                        v_snd_3651_,
                                        v___y_3593_,
                                        leanh::lean_box(0),
                                    );
                                    if leanh::lean_obj_tag(v___x_3652_) == 0 {
                                        v_a_3653_ = leanh::lean_ctor_get(v___x_3652_, 0);
                                        v_isSharedCheck_3670_ =
                                            (!leanh::lean_is_exclusive(v___x_3652_)) as u8;
                                        if v_isSharedCheck_3670_ == 0 {
                                            v___x_3655_ = v___x_3652_;
                                            v_isShared_3656_ = v_isSharedCheck_3670_;
                                            state = 9;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3653_);
                                            leanh::lean_dec(v___x_3652_);
                                            v___x_3655_ = leanh::lean_box(0);
                                            v_isShared_3656_ = v_isSharedCheck_3670_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        v_a_3671_ = leanh::lean_ctor_get(v___x_3652_, 0);
                                        v_isSharedCheck_3678_ =
                                            (!leanh::lean_is_exclusive(v___x_3652_)) as u8;
                                        if v_isSharedCheck_3678_ == 0 {
                                            v___x_3673_ = v___x_3652_;
                                            v_isShared_3674_ = v_isSharedCheck_3678_;
                                            state = 13;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3671_);
                                            leanh::lean_dec(v___x_3652_);
                                            v___x_3673_ = leanh::lean_box(0);
                                            v_isShared_3674_ = v_isSharedCheck_3678_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3603_);
                                    leanh::lean_dec_ref(v_children_3602_);
                                    leanh::lean_dec_ref(v_i_3601_);
                                    leanh::lean_dec_ref(v_postNode_3589_);
                                    v_a_3679_ = leanh::lean_ctor_get(v___x_3648_, 0);
                                    v_isSharedCheck_3686_ =
                                        (!leanh::lean_is_exclusive(v___x_3648_)) as u8;
                                    if v_isSharedCheck_3686_ == 0 {
                                        v___x_3681_ = v___x_3648_;
                                        v_isShared_3682_ = v_isSharedCheck_3686_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3679_);
                                        leanh::lean_dec(v___x_3648_);
                                        v___x_3681_ = leanh::lean_box(0);
                                        v_isShared_3682_ = v_isSharedCheck_3686_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_3603_);
                            leanh::lean_dec_ref(v_children_3602_);
                            leanh::lean_dec_ref(v_i_3601_);
                            leanh::lean_dec_ref_known(v_x_3590_, 1);
                            leanh::lean_dec_ref(v_postNode_3589_);
                            leanh::lean_dec_ref(v_preNode_3588_);
                            v_a_3687_ = leanh::lean_ctor_get(v___x_3604_, 0);
                            v_isSharedCheck_3694_ =
                                (!leanh::lean_is_exclusive(v___x_3604_)) as u8;
                            if v_isSharedCheck_3694_ == 0 {
                                v___x_3689_ = v___x_3604_;
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3687_);
                                leanh::lean_dec(v___x_3604_);
                                v___x_3689_ = leanh::lean_box(0);
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_3590_);
                    leanh::lean_dec_ref(v_postNode_3589_);
                    leanh::lean_dec_ref(v_preNode_3588_);
                    v_isSharedCheck_3703_ = (!leanh::lean_is_exclusive(v_x_3591_)) as u8;
                    if v_isSharedCheck_3703_ == 0 {
                        v_unused_3704_ = leanh::lean_ctor_get(v_x_3591_, 0);
                        leanh::lean_dec(v_unused_3704_);
                        v___x_3696_ = v_x_3591_;
                        v_isShared_3697_ = v_isSharedCheck_3703_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3591_);
                        v___x_3696_ = leanh::lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3703_;
                        state = 19;
                        continue;
                    }
                }
            },
            1 => {
                v_snd_3611_ = leanh::lean_ctor_get(v_a_3605_, 1);
                leanh::lean_inc(v_snd_3611_);
                leanh::lean_dec(v_a_3605_);
                v___x_3612_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___y_3593_);
                v___x_3613_ = leanh::lean_apply_7(
                    v_postNode_3589_,
                    v_val_3603_,
                    v_i_3601_,
                    v_children_3602_,
                    v___x_3612_,
                    v_snd_3611_,
                    v___y_3593_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3613_) == 0 {
                    v_a_3614_ = leanh::lean_ctor_get(v___x_3613_, 0);
                    v_isSharedCheck_3633_ = (!leanh::lean_is_exclusive(v___x_3613_)) as u8;
                    if v_isSharedCheck_3633_ == 0 {
                        v___x_3616_ = v___x_3613_;
                        v_isShared_3617_ = v_isSharedCheck_3633_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3614_);
                        leanh::lean_dec(v___x_3613_);
                        v___x_3616_ = leanh::lean_box(0);
                        v_isShared_3617_ = v_isSharedCheck_3633_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3609_);
                    v_a_3634_ = leanh::lean_ctor_get(v___x_3613_, 0);
                    v_isSharedCheck_3641_ = (!leanh::lean_is_exclusive(v___x_3613_)) as u8;
                    if v_isSharedCheck_3641_ == 0 {
                        v___x_3636_ = v___x_3613_;
                        v_isShared_3637_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3634_);
                        leanh::lean_dec(v___x_3613_);
                        v___x_3636_ = leanh::lean_box(0);
                        v_isShared_3637_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3618_ = leanh::lean_ctor_get(v_a_3614_, 0);
                v_snd_3619_ = leanh::lean_ctor_get(v_a_3614_, 1);
                v_isSharedCheck_3632_ = (!leanh::lean_is_exclusive(v_a_3614_)) as u8;
                if v_isSharedCheck_3632_ == 0 {
                    v___x_3621_ = v_a_3614_;
                    v_isShared_3622_ = v_isSharedCheck_3632_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3619_);
                    leanh::lean_inc(v_fst_3618_);
                    leanh::lean_dec(v_a_3614_);
                    v___x_3621_ = leanh::lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3632_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3610_ == 0 {
                    leanh::lean_ctor_set(v___x_3609_, 0, v_fst_3618_);
                    v___x_3624_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_fst_3618_);
                    v___x_3624_ = v_reuseFailAlloc_3631_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3622_ == 0 {
                    leanh::lean_ctor_set(v___x_3621_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3621_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_snd_3619_);
                    v___x_3626_ = v_reuseFailAlloc_3630_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3617_ == 0 {
                    leanh::lean_ctor_set(v___x_3616_, 0, v___x_3626_);
                    v___x_3628_ = v___x_3616_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
                    v___x_3628_ = v_reuseFailAlloc_3629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3628_;
            }
            7 => {
                if v_isShared_3637_ == 0 {
                    v___x_3639_ = v___x_3636_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3639_;
            }
            9 => {
                v_fst_3657_ = leanh::lean_ctor_get(v_a_3653_, 0);
                v_snd_3658_ = leanh::lean_ctor_get(v_a_3653_, 1);
                v_isSharedCheck_3669_ = (!leanh::lean_is_exclusive(v_a_3653_)) as u8;
                if v_isSharedCheck_3669_ == 0 {
                    v___x_3660_ = v_a_3653_;
                    v_isShared_3661_ = v_isSharedCheck_3669_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3658_);
                    leanh::lean_inc(v_fst_3657_);
                    leanh::lean_dec(v_a_3653_);
                    v___x_3660_ = leanh::lean_box(0);
                    v_isShared_3661_ = v_isSharedCheck_3669_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3662_, 0, v_fst_3657_);
                if v_isShared_3661_ == 0 {
                    leanh::lean_ctor_set(v___x_3660_, 0, v___x_3662_);
                    v___x_3664_ = v___x_3660_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_snd_3658_);
                    v___x_3664_ = v_reuseFailAlloc_3668_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3656_ == 0 {
                    leanh::lean_ctor_set(v___x_3655_, 0, v___x_3664_);
                    v___x_3666_ = v___x_3655_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                    v___x_3666_ = v_reuseFailAlloc_3667_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3666_;
            }
            13 => {
                if v_isShared_3674_ == 0 {
                    v___x_3676_ = v___x_3673_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
                    v___x_3676_ = v_reuseFailAlloc_3677_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3676_;
            }
            15 => {
                if v_isShared_3682_ == 0 {
                    v___x_3684_ = v___x_3681_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3684_;
            }
            17 => {
                if v_isShared_3690_ == 0 {
                    v___x_3692_ = v___x_3689_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3692_;
            }
            19 => {
                v___x_3698_ = leanh::lean_box(0);
                v___x_3699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3699_, 0, v___x_3698_);
                leanh::lean_ctor_set(v___x_3699_, 1, v___y_3592_);
                if v_isShared_3697_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3696_, 0);
                    leanh::lean_ctor_set(v___x_3696_, 0, v___x_3699_);
                    v___x_3701_ = v___x_3696_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3702_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
                    v___x_3701_ = v_reuseFailAlloc_3702_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(
    mut v_preNode_3705_: *mut leanh::LeanObject,
    mut v_postNode_3706_: *mut leanh::LeanObject,
    mut v___x_3707_: *mut leanh::LeanObject,
    mut v_x_3708_: *mut leanh::LeanObject,
    mut v_x_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
    mut v___y_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3708_) == 0 {
                    leanh::lean_dec(v___x_3707_);
                    leanh::lean_dec_ref(v_postNode_3706_);
                    leanh::lean_dec_ref(v_preNode_3705_);
                    v___x_3713_ = l_List_reverse___redArg(v_x_3709_);
                    v___x_3714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3714_, 0, v___x_3713_);
                    leanh::lean_ctor_set(v___x_3714_, 1, v___y_3710_);
                    v___x_3715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3715_, 0, v___x_3714_);
                    return v___x_3715_;
                } else {
                    v_head_3716_ = leanh::lean_ctor_get(v_x_3708_, 0);
                    v_tail_3717_ = leanh::lean_ctor_get(v_x_3708_, 1);
                    v_isSharedCheck_3737_ = (!leanh::lean_is_exclusive(v_x_3708_)) as u8;
                    if v_isSharedCheck_3737_ == 0 {
                        v___x_3719_ = v_x_3708_;
                        v_isShared_3720_ = v_isSharedCheck_3737_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3717_);
                        leanh::lean_inc(v_head_3716_);
                        leanh::lean_dec(v_x_3708_);
                        v___x_3719_ = leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_3707_);
                leanh::lean_inc_ref(v_postNode_3706_);
                leanh::lean_inc_ref(v_preNode_3705_);
                v___x_3721_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_3705_, v_postNode_3706_, v___x_3707_, v_head_3716_, v___y_3710_, v___y_3711_);
                if leanh::lean_obj_tag(v___x_3721_) == 0 {
                    v_a_3722_ = leanh::lean_ctor_get(v___x_3721_, 0);
                    leanh::lean_inc(v_a_3722_);
                    leanh::lean_dec_ref_known(v___x_3721_, 1);
                    v_fst_3723_ = leanh::lean_ctor_get(v_a_3722_, 0);
                    leanh::lean_inc(v_fst_3723_);
                    v_snd_3724_ = leanh::lean_ctor_get(v_a_3722_, 1);
                    leanh::lean_inc(v_snd_3724_);
                    leanh::lean_dec(v_a_3722_);
                    if v_isShared_3720_ == 0 {
                        leanh::lean_ctor_set(v___x_3719_, 1, v_x_3709_);
                        leanh::lean_ctor_set(v___x_3719_, 0, v_fst_3723_);
                        v___x_3726_ = v___x_3719_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3728_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_fst_3723_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_x_3709_);
                        v___x_3726_ = v_reuseFailAlloc_3728_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3719_);
                    leanh::lean_dec(v_tail_3717_);
                    leanh::lean_dec(v_x_3709_);
                    leanh::lean_dec(v___x_3707_);
                    leanh::lean_dec_ref(v_postNode_3706_);
                    leanh::lean_dec_ref(v_preNode_3705_);
                    v_a_3729_ = leanh::lean_ctor_get(v___x_3721_, 0);
                    v_isSharedCheck_3736_ = (!leanh::lean_is_exclusive(v___x_3721_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3721_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3729_);
                        leanh::lean_dec(v___x_3721_);
                        v___x_3731_ = leanh::lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3708_ = v_tail_3717_;
                v_x_3709_ = v___x_3726_;
                v___y_3710_ = v_snd_3724_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(
    mut v_preNode_3738_: *mut leanh::LeanObject,
    mut v_postNode_3739_: *mut leanh::LeanObject,
    mut v___x_3740_: *mut leanh::LeanObject,
    mut v_x_3741_: *mut leanh::LeanObject,
    mut v_x_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_3738_, v_postNode_3739_, v___x_3740_, v_x_3741_, v_x_3742_, v___y_3743_, v___y_3744_);
    leanh::lean_dec_ref(v___y_3744_);
    return v_res_3746_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(
    mut v_preNode_3747_: *mut leanh::LeanObject,
    mut v_postNode_3748_: *mut leanh::LeanObject,
    mut v_x_3749_: *mut leanh::LeanObject,
    mut v_x_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_3747_, v_postNode_3748_, v_x_3749_, v_x_3750_, v___y_3751_, v___y_3752_);
    leanh::lean_dec_ref(v___y_3752_);
    return v_res_3754_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(
    mut v_postNode_3755_: *mut leanh::LeanObject,
    mut v_ci_3756_: *mut leanh::LeanObject,
    mut v_i_3757_: *mut leanh::LeanObject,
    mut v_cs_3758_: *mut leanh::LeanObject,
    mut v_x_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v___y_3761_);
    v___x_3763_ = leanh::lean_apply_6(
        v_postNode_3755_,
        v_ci_3756_,
        v_i_3757_,
        v_cs_3758_,
        v___y_3760_,
        v___y_3761_,
        leanh::lean_box(0),
    );
    return v___x_3763_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(
    mut v_postNode_3764_: *mut leanh::LeanObject,
    mut v_ci_3765_: *mut leanh::LeanObject,
    mut v_i_3766_: *mut leanh::LeanObject,
    mut v_cs_3767_: *mut leanh::LeanObject,
    mut v_x_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_3764_, v_ci_3765_, v_i_3766_, v_cs_3767_, v_x_3768_, v___y_3769_, v___y_3770_);
    leanh::lean_dec_ref(v___y_3770_);
    leanh::lean_dec(v_x_3768_);
    return v_res_3772_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(
    mut v_preNode_3773_: *mut leanh::LeanObject,
    mut v_postNode_3774_: *mut leanh::LeanObject,
    mut v_ctx_x3f_3775_: *mut leanh::LeanObject,
    mut v_t_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v_snd_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3797_: u8 = 0;
    let mut v_unused_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_a_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3780_ = leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_3780_, 0, v_postNode_3774_);
                v___x_3781_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_3773_, v___f_3780_, v_ctx_x3f_3775_, v_t_3776_, v___y_3777_, v___y_3778_);
                if leanh::lean_obj_tag(v___x_3781_) == 0 {
                    v_a_3782_ = leanh::lean_ctor_get(v___x_3781_, 0);
                    v_isSharedCheck_3799_ = (!leanh::lean_is_exclusive(v___x_3781_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3784_ = v___x_3781_;
                        v_isShared_3785_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3782_);
                        leanh::lean_dec(v___x_3781_);
                        v___x_3784_ = leanh::lean_box(0);
                        v_isShared_3785_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3800_ = leanh::lean_ctor_get(v___x_3781_, 0);
                    v_isSharedCheck_3807_ = (!leanh::lean_is_exclusive(v___x_3781_)) as u8;
                    if v_isSharedCheck_3807_ == 0 {
                        v___x_3802_ = v___x_3781_;
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3800_);
                        leanh::lean_dec(v___x_3781_);
                        v___x_3802_ = leanh::lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3786_ = leanh::lean_ctor_get(v_a_3782_, 1);
                v_isSharedCheck_3797_ = (!leanh::lean_is_exclusive(v_a_3782_)) as u8;
                if v_isSharedCheck_3797_ == 0 {
                    v_unused_3798_ = leanh::lean_ctor_get(v_a_3782_, 0);
                    leanh::lean_dec(v_unused_3798_);
                    v___x_3788_ = v_a_3782_;
                    v_isShared_3789_ = v_isSharedCheck_3797_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3786_);
                    leanh::lean_dec(v_a_3782_);
                    v___x_3788_ = leanh::lean_box(0);
                    v_isShared_3789_ = v_isSharedCheck_3797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3790_ = leanh::lean_box(0);
                if v_isShared_3789_ == 0 {
                    leanh::lean_ctor_set(v___x_3788_, 0, v___x_3790_);
                    v___x_3792_ = v___x_3788_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3796_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_snd_3786_);
                    v___x_3792_ = v_reuseFailAlloc_3796_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3785_ == 0 {
                    leanh::lean_ctor_set(v___x_3784_, 0, v___x_3792_);
                    v___x_3794_ = v___x_3784_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
                    v___x_3794_ = v_reuseFailAlloc_3795_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3794_;
            }
            5 => {
                if v_isShared_3803_ == 0 {
                    v___x_3805_ = v___x_3802_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
                    v___x_3805_ = v_reuseFailAlloc_3806_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(
    mut v_preNode_3808_: *mut leanh::LeanObject,
    mut v_postNode_3809_: *mut leanh::LeanObject,
    mut v_ctx_x3f_3810_: *mut leanh::LeanObject,
    mut v_t_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ =
        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(
            v_preNode_3808_,
            v_postNode_3809_,
            v_ctx_x3f_3810_,
            v_t_3811_,
            v___y_3812_,
            v___y_3813_,
        );
    leanh::lean_dec_ref(v___y_3813_);
    return v_res_3815_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_b_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3822_ = leanh::lean_ctor_get(v_a_3817_, 0);
                v_start_3823_ = leanh::lean_ctor_get(v_a_3817_, 1);
                v_stop_3824_ = leanh::lean_ctor_get(v_a_3817_, 2);
                v_isSharedCheck_3847_ = (!leanh::lean_is_exclusive(v_a_3817_)) as u8;
                if v_isSharedCheck_3847_ == 0 {
                    v___x_3826_ = v_a_3817_;
                    v_isShared_3827_ = v_isSharedCheck_3847_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3824_);
                    leanh::lean_inc(v_start_3823_);
                    leanh::lean_inc(v_array_3822_);
                    leanh::lean_dec(v_a_3817_);
                    v___x_3826_ = leanh::lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3847_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3828_ = lean_nat_dec_lt(v_start_3823_, v_stop_3824_);
                if v___x_3828_ == 0 {
                    leanh::lean_del_object(v___x_3826_);
                    leanh::lean_dec(v_stop_3824_);
                    leanh::lean_dec(v_start_3823_);
                    leanh::lean_dec_ref(v_array_3822_);
                    v___x_3829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3829_, 0, v_b_3818_);
                    leanh::lean_ctor_set(v___x_3829_, 1, v___y_3819_);
                    v___x_3830_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                    return v___x_3830_;
                } else {
                    v___f_3831_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0;
                    v___x_3832_ = leanh::lean_box((v___x_3828_) as usize);
                    v___f_3833_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_3833_, 0, v___x_3832_);
                    v___x_3834_ = lean_array_fget_borrowed(v_array_3822_, v_start_3823_);
                    v___x_3835_ = leanh::lean_box(0);
                    leanh::lean_inc(v___x_3834_);
                    v___x_3836_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_3834_);
                    v___x_3837_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___f_3833_, v___f_3831_, v___x_3835_, v___x_3836_, v___y_3819_, v___y_3820_);
                    if leanh::lean_obj_tag(v___x_3837_) == 0 {
                        v_a_3838_ = leanh::lean_ctor_get(v___x_3837_, 0);
                        leanh::lean_inc(v_a_3838_);
                        leanh::lean_dec_ref_known(v___x_3837_, 1);
                        v_snd_3839_ = leanh::lean_ctor_get(v_a_3838_, 1);
                        leanh::lean_inc(v_snd_3839_);
                        leanh::lean_dec(v_a_3838_);
                        v___x_3840_ = leanh::lean_box(0);
                        v___x_3841_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3842_ = lean_nat_add(v_start_3823_, v___x_3841_);
                        leanh::lean_dec(v_start_3823_);
                        if v_isShared_3827_ == 0 {
                            leanh::lean_ctor_set(v___x_3826_, 1, v___x_3842_);
                            v___x_3844_ = v___x_3826_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3846_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_array_3822_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3842_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_stop_3824_);
                            v___x_3844_ = v_reuseFailAlloc_3846_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3826_);
                        leanh::lean_dec(v_stop_3824_);
                        leanh::lean_dec(v_start_3823_);
                        leanh::lean_dec_ref(v_array_3822_);
                        return v___x_3837_;
                    }
                }
            }
            2 => {
                v_a_3817_ = v___x_3844_;
                v_b_3818_ = v___x_3840_;
                v___y_3819_ = v_snd_3839_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(
    mut v_a_3848_: *mut leanh::LeanObject,
    mut v_b_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_3848_, v_b_3849_, v___y_3850_, v___y_3851_);
    leanh::lean_dec_ref(v___y_3851_);
    return v_res_3853_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(
    mut v___x_3854_: *mut leanh::LeanObject,
    mut v_val_3855_: u8,
    mut v_as_3856_: *mut leanh::LeanObject,
    mut v_i_3857_: usize,
    mut v_stop_3858_: usize,
    mut v_b_3859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: usize = 0;
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_position_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3865_ = lean_usize_dec_eq(v_i_3857_, v_stop_3858_);
                if v___x_3865_ == 0 {
                    v___x_3866_ = lean_array_uget_borrowed(v_as_3856_, v_i_3857_);
                    v_position_3867_ = leanh::lean_ctor_get(v___x_3866_, 0);
                    v___x_3868_ =
                        l_Lean_Syntax_Range_contains(v___x_3854_, v_position_3867_, v_val_3855_);
                    if v___x_3868_ == 0 {
                        leanh::lean_inc(v___x_3866_);
                        v___x_3869_ = lean_array_push(v_b_3859_, v___x_3866_);
                        v___y_3861_ = v___x_3869_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3861_ = v_b_3859_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3859_;
                }
            }
            1 => {
                v___x_3862_ = 1usize;
                v___x_3863_ = lean_usize_add(v_i_3857_, v___x_3862_);
                v_i_3857_ = v___x_3863_;
                v_b_3859_ = v___y_3861_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(
    mut v___x_3870_: *mut leanh::LeanObject,
    mut v_val_3871_: *mut leanh::LeanObject,
    mut v_as_3872_: *mut leanh::LeanObject,
    mut v_i_3873_: *mut leanh::LeanObject,
    mut v_stop_3874_: *mut leanh::LeanObject,
    mut v_b_3875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_21106__boxed_3876_: u8 = 0;
    let mut v_i_boxed_3877_: usize = 0;
    let mut v_stop_boxed_3878_: usize = 0;
    let mut v_res_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_21106__boxed_3876_ = (leanh::lean_unbox(v_val_3871_) as u8);
    v_i_boxed_3877_ = leanh::lean_unbox_usize(v_i_3873_);
    leanh::lean_dec(v_i_3873_);
    v_stop_boxed_3878_ = leanh::lean_unbox_usize(v_stop_3874_);
    leanh::lean_dec(v_stop_3874_);
    v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_3870_, v_val_21106__boxed_3876_, v_as_3872_, v_i_boxed_3877_, v_stop_boxed_3878_, v_b_3875_);
    leanh::lean_dec_ref(v_as_3872_);
    leanh::lean_dec_ref(v___x_3870_);
    return v_res_3879_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(
    mut v___x_3880_: *mut leanh::LeanObject,
    mut v_as_3881_: *mut leanh::LeanObject,
    mut v_i_3882_: usize,
    mut v_stop_3883_: usize,
    mut v_b_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: usize = 0;
    let mut v___x_3888_: usize = 0;
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_position_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = lean_usize_dec_eq(v_i_3882_, v_stop_3883_);
                if v___x_3890_ == 0 {
                    v___x_3891_ = lean_array_uget_borrowed(v_as_3881_, v_i_3882_);
                    v_position_3892_ = leanh::lean_ctor_get(v___x_3891_, 0);
                    v___x_3893_ = 1;
                    v___x_3894_ =
                        l_Lean_Syntax_Range_contains(v___x_3880_, v_position_3892_, v___x_3893_);
                    if v___x_3894_ == 0 {
                        v___y_3886_ = v_b_3884_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_3891_);
                        v___x_3895_ = lean_array_push(v_b_3884_, v___x_3891_);
                        v___y_3886_ = v___x_3895_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3884_;
                }
            }
            1 => {
                v___x_3887_ = 1usize;
                v___x_3888_ = lean_usize_add(v_i_3882_, v___x_3887_);
                v_i_3882_ = v___x_3888_;
                v_b_3884_ = v___y_3886_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(
    mut v___x_3896_: *mut leanh::LeanObject,
    mut v_as_3897_: *mut leanh::LeanObject,
    mut v_i_3898_: *mut leanh::LeanObject,
    mut v_stop_3899_: *mut leanh::LeanObject,
    mut v_b_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3901_: usize = 0;
    let mut v_stop_boxed_3902_: usize = 0;
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3901_ = leanh::lean_unbox_usize(v_i_3898_);
    leanh::lean_dec(v_i_3898_);
    v_stop_boxed_3902_ = leanh::lean_unbox_usize(v_stop_3899_);
    leanh::lean_dec(v_stop_3899_);
    v_res_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_3896_, v_as_3897_, v_i_boxed_3901_, v_stop_boxed_3902_, v_b_3900_);
    leanh::lean_dec_ref(v_as_3897_);
    leanh::lean_dec_ref(v___x_3896_);
    return v_res_3903_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(
    mut v___x_3904_: *mut leanh::LeanObject,
    mut v_sz_3905_: usize,
    mut v_i_3906_: usize,
    mut v_bs_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: usize = 0;
    let mut v___x_3917_: usize = 0;
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3909_ = lean_usize_dec_lt(v_i_3906_, v_sz_3905_);
                if v___x_3909_ == 0 {
                    leanh::lean_dec_ref(v___x_3904_);
                    v___x_3910_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3910_, 0, v_bs_3907_);
                    return v___x_3910_;
                } else {
                    v_v_3911_ = lean_array_uget_borrowed(v_bs_3907_, v_i_3906_);
                    leanh::lean_inc(v_v_3911_);
                    leanh::lean_inc_ref(v___x_3904_);
                    v___x_3912_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_3904_, v_v_3911_);
                    if leanh::lean_obj_tag(v___x_3912_) == 0 {
                        v_a_3913_ = leanh::lean_ctor_get(v___x_3912_, 0);
                        leanh::lean_inc(v_a_3913_);
                        leanh::lean_dec_ref_known(v___x_3912_, 1);
                        v___x_3914_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3915_ = lean_array_uset(v_bs_3907_, v_i_3906_, v___x_3914_);
                        v___x_3916_ = 1usize;
                        v___x_3917_ = lean_usize_add(v_i_3906_, v___x_3916_);
                        v___x_3918_ = lean_array_uset(v_bs_x27_3915_, v_i_3906_, v_a_3913_);
                        v_i_3906_ = v___x_3917_;
                        v_bs_3907_ = v___x_3918_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3907_);
                        leanh::lean_dec_ref(v___x_3904_);
                        v_a_3920_ = leanh::lean_ctor_get(v___x_3912_, 0);
                        v_isSharedCheck_3928_ =
                            (!leanh::lean_is_exclusive(v___x_3912_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3922_ = v___x_3912_;
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3920_);
                            leanh::lean_dec(v___x_3912_);
                            v___x_3922_ = leanh::lean_box(0);
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3924_ = l_Lean_Server_RequestError_ofIoError(v_a_3920_);
                if v_isShared_3923_ == 0 {
                    leanh::lean_ctor_set(v___x_3922_, 0, v___x_3924_);
                    v___x_3926_ = v___x_3922_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
                    v___x_3926_ = v_reuseFailAlloc_3927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(
    mut v___x_3929_: *mut leanh::LeanObject,
    mut v_sz_3930_: *mut leanh::LeanObject,
    mut v_i_3931_: *mut leanh::LeanObject,
    mut v_bs_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3934_: usize = 0;
    let mut v_i_boxed_3935_: usize = 0;
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3934_ = leanh::lean_unbox_usize(v_sz_3930_);
    leanh::lean_dec(v_sz_3930_);
    v_i_boxed_3935_ = leanh::lean_unbox_usize(v_i_3931_);
    leanh::lean_dec(v_i_3931_);
    v_res_3936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_3929_, v_sz_boxed_3934_, v_i_boxed_3935_, v_bs_3932_);
    return v_res_3936_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Server_FileWorker_handleInlayHints___closed__1;
    v___x_3940_ = leanh::lean_unsigned_to_nat(2);
    v___x_3941_ = leanh::lean_unsigned_to_nat(162);
    v___x_3942_ = l_Lean_Server_FileWorker_handleInlayHints___closed__0;
    v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0;
    v___x_3944_ = l_mkPanicMessageWithDecl(
        v___x_3943_,
        v___x_3942_,
        v___x_3941_,
        v___x_3940_,
        v___x_3939_,
    );
    return v___x_3944_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleInlayHints(
    mut v_p_3945_: *mut leanh::LeanObject,
    mut v_s_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_doc_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldInlayHints_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldFinishedSnaps_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastEditTimestamp_x3f_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isFirstRequestAfterEdit_3958_: u8 = 0;
    let mut v___y_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: u8 = 0;
    let mut v___y_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3964_: usize = 0;
    let mut v___x_3965_: usize = 0;
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v_a_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3985_: u8 = 0;
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3991_: u8 = 0;
    let mut v___y_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4000_: usize = 0;
    let mut v___x_4001_: usize = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: usize = 0;
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: u8 = 0;
    let mut v___y_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v___y_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: u8 = 0;
    let mut v___y_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v___y_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4039_: u8 = 0;
    let mut v___y_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4041_: u8 = 0;
    let mut v___y_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: usize = 0;
    let mut v___x_4051_: usize = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: usize = 0;
    let mut v___x_4054_: usize = 0;
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u8 = 0;
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: u8 = 0;
    let mut v___y_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: u8 = 0;
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u32 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v_sz_4093_: usize = 0;
    let mut v___x_4094_: usize = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4099_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4107_: u8 = 0;
    let mut v_a_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4111_: u8 = 0;
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4115_: u8 = 0;
    let mut v_isSharedCheck_4116_: u8 = 0;
    let mut v_unused_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v_sz_4126_: usize = 0;
    let mut v___x_4127_: usize = 0;
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4142_: u8 = 0;
    let mut v_a_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4150_: u8 = 0;
    let mut v_isSharedCheck_4151_: u8 = 0;
    let mut v_unused_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_3949_ = leanh::lean_ctor_get(v_a_3947_, 1);
                v_toEditableDocumentCore_3950_ = leanh::lean_ctor_get(v_doc_3949_, 0);
                v_meta_3951_ = leanh::lean_ctor_get(v_toEditableDocumentCore_3950_, 0);
                v_cancelTk_3952_ = leanh::lean_ctor_get(v_a_3947_, 4);
                v_cmdSnaps_3953_ = leanh::lean_ctor_get(v_toEditableDocumentCore_3950_, 2);
                v_text_3954_ = leanh::lean_ctor_get(v_meta_3951_, 3);
                v_oldInlayHints_3955_ = leanh::lean_ctor_get(v_s_3946_, 0);
                v_oldFinishedSnaps_3956_ = leanh::lean_ctor_get(v_s_3946_, 1);
                v_lastEditTimestamp_x3f_3957_ = leanh::lean_ctor_get(v_s_3946_, 2);
                v_isFirstRequestAfterEdit_3958_ = leanh::lean_ctor_get_uint8(
                    v_s_3946_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_isFirstRequestAfterEdit_3958_ == 0 {
                    v___x_3986_ = lean_io_mono_ms_now();
                    v_range_3987_ = leanh::lean_ctor_get(v_p_3945_, 2);
                    leanh::lean_inc_ref(v_range_3987_);
                    leanh::lean_dec_ref(v_p_3945_);
                    v___x_3988_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_3954_, v_range_3987_);
                    if leanh::lean_obj_tag(v_lastEditTimestamp_x3f_3957_) == 0 {
                        leanh::lean_dec(v___x_3986_);
                        v___x_4118_ = leanh::lean_unsigned_to_nat(0);
                        v___y_4069_ = v___x_4118_;
                        state = 13;
                        continue;
                    } else {
                        v_val_4119_ = leanh::lean_ctor_get(v_lastEditTimestamp_x3f_3957_, 0);
                        v___x_4120_ = leanh::lean_unsigned_to_nat(3000);
                        v___x_4121_ = lean_nat_sub(v___x_3986_, v_val_4119_);
                        leanh::lean_dec(v___x_3986_);
                        v___x_4122_ = lean_nat_sub(v___x_4120_, v___x_4121_);
                        leanh::lean_dec(v___x_4121_);
                        v___y_4069_ = v___x_4122_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_lastEditTimestamp_x3f_3957_);
                    leanh::lean_inc(v_oldFinishedSnaps_3956_);
                    leanh::lean_inc_ref(v_oldInlayHints_3955_);
                    leanh::lean_dec_ref(v_p_3945_);
                    v_isSharedCheck_4151_ = (!leanh::lean_is_exclusive(v_s_3946_)) as u8;
                    if v_isSharedCheck_4151_ == 0 {
                        v_unused_4152_ = leanh::lean_ctor_get(v_s_3946_, 2);
                        leanh::lean_dec(v_unused_4152_);
                        v_unused_4153_ = leanh::lean_ctor_get(v_s_3946_, 1);
                        leanh::lean_dec(v_unused_4153_);
                        v_unused_4154_ = leanh::lean_ctor_get(v_s_3946_, 0);
                        leanh::lean_dec(v_unused_4154_);
                        v___x_4124_ = v_s_3946_;
                        v_isShared_4125_ = v_isSharedCheck_4151_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3946_);
                        v___x_4124_ = leanh::lean_box(0);
                        v_isShared_4125_ = v_isSharedCheck_4151_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_3964_ = lean_array_size(v___y_3963_);
                v___x_3965_ = 0usize;
                leanh::lean_inc_ref(v_text_3954_);
                v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_3954_, v_sz_3964_, v___x_3965_, v___y_3963_);
                if leanh::lean_obj_tag(v___x_3966_) == 0 {
                    v_a_3967_ = leanh::lean_ctor_get(v___x_3966_, 0);
                    v_isSharedCheck_3977_ = (!leanh::lean_is_exclusive(v___x_3966_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3969_ = v___x_3966_;
                        v_isShared_3970_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3967_);
                        leanh::lean_dec(v___x_3966_);
                        v___x_3969_ = leanh::lean_box(0);
                        v_isShared_3970_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_3961_);
                    leanh::lean_dec_ref(v___y_3960_);
                    leanh::lean_dec(v_lastEditTimestamp_x3f_3957_);
                    v_a_3978_ = leanh::lean_ctor_get(v___x_3966_, 0);
                    v_isSharedCheck_3985_ = (!leanh::lean_is_exclusive(v___x_3966_)) as u8;
                    if v_isSharedCheck_3985_ == 0 {
                        v___x_3980_ = v___x_3966_;
                        v_isShared_3981_ = v_isSharedCheck_3985_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3978_);
                        leanh::lean_dec(v___x_3966_);
                        v___x_3980_ = leanh::lean_box(0);
                        v_isShared_3981_ = v_isSharedCheck_3985_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3971_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3971_, 0, v_a_3967_);
                leanh::lean_ctor_set_uint8(
                    v___x_3971_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_3962_,
                );
                v___x_3972_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_3972_, 0, v___y_3960_);
                leanh::lean_ctor_set(v___x_3972_, 1, v___y_3961_);
                leanh::lean_ctor_set(v___x_3972_, 2, v_lastEditTimestamp_x3f_3957_);
                leanh::lean_ctor_set_uint8(
                    v___x_3972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_isFirstRequestAfterEdit_3958_,
                );
                v___x_3973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3973_, 0, v___x_3971_);
                leanh::lean_ctor_set(v___x_3973_, 1, v___x_3972_);
                if v_isShared_3970_ == 0 {
                    leanh::lean_ctor_set(v___x_3969_, 0, v___x_3973_);
                    v___x_3975_ = v___x_3969_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
                    v___x_3975_ = v_reuseFailAlloc_3976_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3975_;
            }
            4 => {
                if v_isShared_3981_ == 0 {
                    v___x_3983_ = v___x_3980_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
                    v___x_3983_ = v_reuseFailAlloc_3984_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3983_;
            }
            6 => {
                v___x_3995_ = l_Array_append___redArg(v_snd_3994_, v___y_3993_);
                leanh::lean_dec_ref(v___y_3993_);
                v___x_3996_ = lean_array_get_size(v___x_3995_);
                v___x_3997_ = lean_mk_empty_array_with_capacity(v___y_3990_);
                v___x_3998_ = lean_nat_dec_lt(v___y_3990_, v___x_3996_);
                leanh::lean_dec(v___y_3990_);
                if v___x_3998_ == 0 {
                    leanh::lean_dec_ref(v___x_3988_);
                    v___y_3960_ = v___x_3995_;
                    v___y_3961_ = v___y_3992_;
                    v___y_3962_ = v___y_3991_;
                    v___y_3963_ = v___x_3997_;
                    state = 1;
                    continue;
                } else {
                    v___x_3999_ = lean_nat_dec_le(v___x_3996_, v___x_3996_);
                    if v___x_3999_ == 0 {
                        if v___x_3998_ == 0 {
                            leanh::lean_dec_ref(v___x_3988_);
                            v___y_3960_ = v___x_3995_;
                            v___y_3961_ = v___y_3992_;
                            v___y_3962_ = v___y_3991_;
                            v___y_3963_ = v___x_3997_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4000_ = 0usize;
                            v___x_4001_ = lean_usize_of_nat(v___x_3996_);
                            v___x_4002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_3988_, v___x_3995_, v___x_4000_, v___x_4001_, v___x_3997_);
                            leanh::lean_dec_ref(v___x_3988_);
                            v___y_3960_ = v___x_3995_;
                            v___y_3961_ = v___y_3992_;
                            v___y_3962_ = v___y_3991_;
                            v___y_3963_ = v___x_4002_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4003_ = 0usize;
                        v___x_4004_ = lean_usize_of_nat(v___x_3996_);
                        v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_3988_, v___x_3995_, v___x_4003_, v___x_4004_, v___x_3997_);
                        leanh::lean_dec_ref(v___x_3988_);
                        v___y_3960_ = v___x_3995_;
                        v___y_3961_ = v___y_3992_;
                        v___y_3962_ = v___y_3991_;
                        v___y_3963_ = v___x_4005_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4014_ =
                    l_Array_toSubarray___redArg(v___y_4008_, v_lower_4012_, v_upper_4013_);
                v___x_4015_ = leanh::lean_box(0);
                v___x_4016_ = lean_mk_empty_array_with_capacity(v___y_4007_);
                v___x_4017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v___x_4014_, v___x_4015_, v___x_4016_, v_a_3947_);
                if leanh::lean_obj_tag(v___x_4017_) == 0 {
                    v_a_4018_ = leanh::lean_ctor_get(v___x_4017_, 0);
                    leanh::lean_inc(v_a_4018_);
                    leanh::lean_dec_ref_known(v___x_4017_, 1);
                    v_snd_4019_ = leanh::lean_ctor_get(v_a_4018_, 1);
                    leanh::lean_inc(v_snd_4019_);
                    leanh::lean_dec(v_a_4018_);
                    v___y_3990_ = v___y_4007_;
                    v___y_3991_ = v___y_4010_;
                    v___y_3992_ = v___y_4009_;
                    v___y_3993_ = v___y_4011_;
                    v_snd_3994_ = v_snd_4019_;
                    state = 6;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_4017_) == 0 {
                        v_a_4020_ = leanh::lean_ctor_get(v___x_4017_, 0);
                        leanh::lean_inc(v_a_4020_);
                        leanh::lean_dec_ref_known(v___x_4017_, 1);
                        v_snd_4021_ = leanh::lean_ctor_get(v_a_4020_, 1);
                        leanh::lean_inc(v_snd_4021_);
                        leanh::lean_dec(v_a_4020_);
                        v___y_3990_ = v___y_4007_;
                        v___y_3991_ = v___y_4010_;
                        v___y_3992_ = v___y_4009_;
                        v___y_3993_ = v___y_4011_;
                        v_snd_3994_ = v_snd_4021_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_4011_);
                        leanh::lean_dec(v___y_4009_);
                        leanh::lean_dec(v___y_4007_);
                        leanh::lean_dec_ref(v___x_3988_);
                        leanh::lean_dec(v_lastEditTimestamp_x3f_3957_);
                        v_a_4022_ = leanh::lean_ctor_get(v___x_4017_, 0);
                        v_isSharedCheck_4029_ =
                            (!leanh::lean_is_exclusive(v___x_4017_)) as u8;
                        if v_isSharedCheck_4029_ == 0 {
                            v___x_4024_ = v___x_4017_;
                            v_isShared_4025_ = v_isSharedCheck_4029_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4022_);
                            leanh::lean_dec(v___x_4017_);
                            v___x_4024_ = leanh::lean_box(0);
                            v_isShared_4025_ = v_isSharedCheck_4029_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_4025_ == 0 {
                    v___x_4027_ = v___x_4024_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
                    v___x_4027_ = v_reuseFailAlloc_4028_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4027_;
            }
            10 => {
                v___x_4036_ = lean_nat_dec_le(v_oldFinishedSnaps_3956_, v___y_4031_);
                if v___x_4036_ == 0 {
                    leanh::lean_inc(v___y_4033_);
                    v___y_4007_ = v___y_4031_;
                    v___y_4008_ = v___y_4032_;
                    v___y_4009_ = v___y_4033_;
                    v___y_4010_ = v___y_4034_;
                    v___y_4011_ = v___y_4035_;
                    v_lower_4012_ = v_oldFinishedSnaps_3956_;
                    v_upper_4013_ = v___y_4033_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_oldFinishedSnaps_3956_);
                    leanh::lean_inc(v___y_4033_);
                    leanh::lean_inc(v___y_4031_);
                    v___y_4007_ = v___y_4031_;
                    v___y_4008_ = v___y_4032_;
                    v___y_4009_ = v___y_4033_;
                    v___y_4010_ = v___y_4034_;
                    v___y_4011_ = v___y_4035_;
                    v_lower_4012_ = v___y_4031_;
                    v_upper_4013_ = v___y_4033_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                v___x_4044_ = leanh::lean_unsigned_to_nat(0);
                v___x_4045_ = lean_array_get_size(v_oldInlayHints_3955_);
                v___x_4046_ = l_Lean_Server_FileWorker_InlayHintState_init___closed__0;
                v___x_4047_ = lean_nat_dec_lt(v___x_4044_, v___x_4045_);
                if v___x_4047_ == 0 {
                    leanh::lean_dec(v___y_4043_);
                    leanh::lean_dec(v___y_4040_);
                    leanh::lean_dec_ref(v_oldInlayHints_3955_);
                    v___y_4031_ = v___x_4044_;
                    v___y_4032_ = v___y_4038_;
                    v___y_4033_ = v___y_4042_;
                    v___y_4034_ = v___y_4041_;
                    v___y_4035_ = v___x_4046_;
                    state = 10;
                    continue;
                } else {
                    v___x_4048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4048_, 0, v___y_4040_);
                    leanh::lean_ctor_set(v___x_4048_, 1, v___y_4043_);
                    v___x_4049_ = lean_nat_dec_le(v___x_4045_, v___x_4045_);
                    if v___x_4049_ == 0 {
                        if v___x_4047_ == 0 {
                            leanh::lean_dec_ref_known(v___x_4048_, 2);
                            leanh::lean_dec_ref(v_oldInlayHints_3955_);
                            v___y_4031_ = v___x_4044_;
                            v___y_4032_ = v___y_4038_;
                            v___y_4033_ = v___y_4042_;
                            v___y_4034_ = v___y_4041_;
                            v___y_4035_ = v___x_4046_;
                            state = 10;
                            continue;
                        } else {
                            v___x_4050_ = 0usize;
                            v___x_4051_ = lean_usize_of_nat(v___x_4045_);
                            v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_4048_, v___y_4039_, v_oldInlayHints_3955_, v___x_4050_, v___x_4051_, v___x_4046_);
                            leanh::lean_dec_ref(v_oldInlayHints_3955_);
                            leanh::lean_dec_ref_known(v___x_4048_, 2);
                            v___y_4031_ = v___x_4044_;
                            v___y_4032_ = v___y_4038_;
                            v___y_4033_ = v___y_4042_;
                            v___y_4034_ = v___y_4041_;
                            v___y_4035_ = v___x_4052_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_4053_ = 0usize;
                        v___x_4054_ = lean_usize_of_nat(v___x_4045_);
                        v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_4048_, v___y_4039_, v_oldInlayHints_3955_, v___x_4053_, v___x_4054_, v___x_4046_);
                        leanh::lean_dec_ref(v_oldInlayHints_3955_);
                        leanh::lean_dec_ref_known(v___x_4048_, 2);
                        v___y_4031_ = v___x_4044_;
                        v___y_4032_ = v___y_4038_;
                        v___y_4033_ = v___y_4042_;
                        v___y_4034_ = v___y_4041_;
                        v___y_4035_ = v___x_4055_;
                        state = 10;
                        continue;
                    }
                }
            }
            12 => {
                v___x_4063_ = lean_nat_sub(v___y_4060_, v___y_4057_);
                v___x_4064_ = lean_nat_dec_lt(v___x_4063_, v___y_4060_);
                if v___x_4064_ == 0 {
                    leanh::lean_dec(v___x_4063_);
                    v___x_4065_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4038_ = v___y_4058_;
                    v___y_4039_ = v___y_4059_;
                    v___y_4040_ = v___y_4062_;
                    v___y_4041_ = v___y_4061_;
                    v___y_4042_ = v___y_4060_;
                    v___y_4043_ = v___x_4065_;
                    state = 11;
                    continue;
                } else {
                    v___x_4066_ = lean_array_fget_borrowed(v___y_4058_, v___x_4063_);
                    leanh::lean_dec(v___x_4063_);
                    v___x_4067_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_4066_);
                    v___y_4038_ = v___y_4058_;
                    v___y_4039_ = v___y_4059_;
                    v___y_4040_ = v___y_4062_;
                    v___y_4041_ = v___y_4061_;
                    v___y_4042_ = v___y_4060_;
                    v___y_4043_ = v___x_4067_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_4070_ = lean_uint32_of_nat(v___y_4069_);
                leanh::lean_dec(v___y_4069_);
                v___x_4071_ =
                    l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3952_);
                leanh::lean_inc(v_cmdSnaps_3953_);
                v___x_4072_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(
                    v_cmdSnaps_3953_,
                    v___x_4070_,
                    v___x_4071_,
                );
                v_snd_4073_ = leanh::lean_ctor_get(v___x_4072_, 1);
                leanh::lean_inc(v_snd_4073_);
                v_fst_4074_ = leanh::lean_ctor_get(v___x_4072_, 0);
                leanh::lean_inc(v_fst_4074_);
                leanh::lean_dec_ref(v___x_4072_);
                v_snd_4075_ = leanh::lean_ctor_get(v_snd_4073_, 1);
                v_isSharedCheck_4116_ = (!leanh::lean_is_exclusive(v_snd_4073_)) as u8;
                if v_isSharedCheck_4116_ == 0 {
                    v_unused_4117_ = leanh::lean_ctor_get(v_snd_4073_, 0);
                    leanh::lean_dec(v_unused_4117_);
                    v___x_4077_ = v_snd_4073_;
                    v_isShared_4078_ = v_isSharedCheck_4116_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4075_);
                    leanh::lean_dec(v_snd_4073_);
                    v___x_4077_ = leanh::lean_box(0);
                    v_isShared_4078_ = v_isSharedCheck_4116_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4079_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_3952_);
                if v___x_4079_ == 0 {
                    leanh::lean_inc(v_lastEditTimestamp_x3f_3957_);
                    leanh::lean_inc(v_oldFinishedSnaps_3956_);
                    leanh::lean_inc_ref(v_oldInlayHints_3955_);
                    leanh::lean_del_object(v___x_4077_);
                    leanh::lean_dec_ref(v_s_3946_);
                    v___x_4080_ = lean_array_mk(v_fst_4074_);
                    v___x_4081_ = lean_array_get_size(v___x_4080_);
                    v___x_4082_ = lean_nat_dec_le(v_oldFinishedSnaps_3956_, v___x_4081_);
                    if v___x_4082_ == 0 {
                        leanh::lean_dec_ref(v___x_4080_);
                        leanh::lean_dec(v_snd_4075_);
                        leanh::lean_dec_ref(v___x_3988_);
                        leanh::lean_dec(v_lastEditTimestamp_x3f_3957_);
                        leanh::lean_dec(v_oldFinishedSnaps_3956_);
                        leanh::lean_dec_ref(v_oldInlayHints_3955_);
                        v___x_4083_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_FileWorker_handleInlayHints___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_FileWorker_handleInlayHints___closed__2_once
                            ),
                            _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2,
                        );
                        v___x_4084_ =
                            l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(
                                v___x_4083_,
                                v_a_3947_,
                            );
                        return v___x_4084_;
                    } else {
                        v___x_4085_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4086_ = lean_nat_sub(v_oldFinishedSnaps_3956_, v___x_4085_);
                        v___x_4087_ = lean_nat_dec_lt(v___x_4086_, v___x_4081_);
                        if v___x_4087_ == 0 {
                            leanh::lean_dec(v___x_4086_);
                            v___x_4088_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4089_ = (leanh::lean_unbox(v_snd_4075_) as u8);
                            leanh::lean_dec(v_snd_4075_);
                            v___y_4057_ = v___x_4085_;
                            v___y_4058_ = v___x_4080_;
                            v___y_4059_ = v___x_4079_;
                            v___y_4060_ = v___x_4081_;
                            v___y_4061_ = v___x_4089_;
                            v___y_4062_ = v___x_4088_;
                            state = 12;
                            continue;
                        } else {
                            v___x_4090_ = lean_array_fget(v___x_4080_, v___x_4086_);
                            leanh::lean_dec(v___x_4086_);
                            v___x_4091_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_4090_);
                            leanh::lean_dec(v___x_4090_);
                            v___x_4092_ = (leanh::lean_unbox(v_snd_4075_) as u8);
                            leanh::lean_dec(v_snd_4075_);
                            v___y_4057_ = v___x_4085_;
                            v___y_4058_ = v___x_4080_;
                            v___y_4059_ = v___x_4079_;
                            v___y_4060_ = v___x_4081_;
                            v___y_4061_ = v___x_4092_;
                            v___y_4062_ = v___x_4091_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_4075_);
                    leanh::lean_dec(v_fst_4074_);
                    leanh::lean_dec_ref(v___x_3988_);
                    v_sz_4093_ = lean_array_size(v_oldInlayHints_3955_);
                    v___x_4094_ = 0usize;
                    leanh::lean_inc_ref(v_oldInlayHints_3955_);
                    leanh::lean_inc_ref(v_text_3954_);
                    v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_3954_, v_sz_4093_, v___x_4094_, v_oldInlayHints_3955_);
                    if leanh::lean_obj_tag(v___x_4095_) == 0 {
                        v_a_4096_ = leanh::lean_ctor_get(v___x_4095_, 0);
                        v_isSharedCheck_4107_ =
                            (!leanh::lean_is_exclusive(v___x_4095_)) as u8;
                        if v_isSharedCheck_4107_ == 0 {
                            v___x_4098_ = v___x_4095_;
                            v_isShared_4099_ = v_isSharedCheck_4107_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4096_);
                            leanh::lean_dec(v___x_4095_);
                            v___x_4098_ = leanh::lean_box(0);
                            v_isShared_4099_ = v_isSharedCheck_4107_;
                            state = 15;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4077_);
                        leanh::lean_dec_ref(v_s_3946_);
                        v_a_4108_ = leanh::lean_ctor_get(v___x_4095_, 0);
                        v_isSharedCheck_4115_ =
                            (!leanh::lean_is_exclusive(v___x_4095_)) as u8;
                        if v_isSharedCheck_4115_ == 0 {
                            v___x_4110_ = v___x_4095_;
                            v_isShared_4111_ = v_isSharedCheck_4115_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4108_);
                            leanh::lean_dec(v___x_4095_);
                            v___x_4110_ = leanh::lean_box(0);
                            v_isShared_4111_ = v_isSharedCheck_4115_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            15 => {
                v___x_4100_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4100_, 0, v_a_4096_);
                leanh::lean_ctor_set_uint8(
                    v___x_4100_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isFirstRequestAfterEdit_3958_,
                );
                if v_isShared_4078_ == 0 {
                    leanh::lean_ctor_set(v___x_4077_, 1, v_s_3946_);
                    leanh::lean_ctor_set(v___x_4077_, 0, v___x_4100_);
                    v___x_4102_ = v___x_4077_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_s_3946_);
                    v___x_4102_ = v_reuseFailAlloc_4106_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4099_ == 0 {
                    leanh::lean_ctor_set(v___x_4098_, 0, v___x_4102_);
                    v___x_4104_ = v___x_4098_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
                    v___x_4104_ = v_reuseFailAlloc_4105_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4104_;
            }
            18 => {
                if v_isShared_4111_ == 0 {
                    v___x_4113_ = v___x_4110_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
                    v___x_4113_ = v_reuseFailAlloc_4114_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4113_;
            }
            20 => {
                v_sz_4126_ = lean_array_size(v_oldInlayHints_3955_);
                v___x_4127_ = 0usize;
                leanh::lean_inc_ref(v_oldInlayHints_3955_);
                leanh::lean_inc_ref(v_text_3954_);
                v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_3954_, v_sz_4126_, v___x_4127_, v_oldInlayHints_3955_);
                if leanh::lean_obj_tag(v___x_4128_) == 0 {
                    v_a_4129_ = leanh::lean_ctor_get(v___x_4128_, 0);
                    v_isSharedCheck_4142_ = (!leanh::lean_is_exclusive(v___x_4128_)) as u8;
                    if v_isSharedCheck_4142_ == 0 {
                        v___x_4131_ = v___x_4128_;
                        v_isShared_4132_ = v_isSharedCheck_4142_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4129_);
                        leanh::lean_dec(v___x_4128_);
                        v___x_4131_ = leanh::lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4142_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4124_);
                    leanh::lean_dec(v_lastEditTimestamp_x3f_3957_);
                    leanh::lean_dec(v_oldFinishedSnaps_3956_);
                    leanh::lean_dec_ref(v_oldInlayHints_3955_);
                    v_a_4143_ = leanh::lean_ctor_get(v___x_4128_, 0);
                    v_isSharedCheck_4150_ = (!leanh::lean_is_exclusive(v___x_4128_)) as u8;
                    if v_isSharedCheck_4150_ == 0 {
                        v___x_4145_ = v___x_4128_;
                        v_isShared_4146_ = v_isSharedCheck_4150_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4143_);
                        leanh::lean_dec(v___x_4128_);
                        v___x_4145_ = leanh::lean_box(0);
                        v_isShared_4146_ = v_isSharedCheck_4150_;
                        state = 24;
                        continue;
                    }
                }
            }
            21 => {
                v___x_4133_ = 0;
                v___x_4134_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4134_, 0, v_a_4129_);
                leanh::lean_ctor_set_uint8(
                    v___x_4134_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4133_,
                );
                if v_isShared_4125_ == 0 {
                    v___x_4136_ = v___x_4124_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4141_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_oldInlayHints_3955_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4141_,
                        1,
                        v_oldFinishedSnaps_3956_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4141_,
                        2,
                        v_lastEditTimestamp_x3f_3957_,
                    );
                    v___x_4136_ = v_reuseFailAlloc_4141_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4136_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4133_,
                );
                v___x_4137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4137_, 0, v___x_4134_);
                leanh::lean_ctor_set(v___x_4137_, 1, v___x_4136_);
                if v_isShared_4132_ == 0 {
                    leanh::lean_ctor_set(v___x_4131_, 0, v___x_4137_);
                    v___x_4139_ = v___x_4131_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4137_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4139_;
            }
            24 => {
                if v_isShared_4146_ == 0 {
                    v___x_4148_ = v___x_4145_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
                    v___x_4148_ = v_reuseFailAlloc_4149_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_handleInlayHints___boxed(
    mut v_p_4155_: *mut leanh::LeanObject,
    mut v_s_4156_: *mut leanh::LeanObject,
    mut v_a_4157_: *mut leanh::LeanObject,
    mut v_a_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_4155_, v_s_4156_, v_a_4157_);
    leanh::lean_dec_ref(v_a_4157_);
    return v_res_4159_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(
    mut v___x_4160_: *mut leanh::LeanObject,
    mut v_sz_4161_: usize,
    mut v_i_4162_: usize,
    mut v_bs_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_4160_, v_sz_4161_, v_i_4162_, v_bs_4163_);
    return v___x_4166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(
    mut v___x_4167_: *mut leanh::LeanObject,
    mut v_sz_4168_: *mut leanh::LeanObject,
    mut v_i_4169_: *mut leanh::LeanObject,
    mut v_bs_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4173_: usize = 0;
    let mut v_i_boxed_4174_: usize = 0;
    let mut v_res_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4173_ = leanh::lean_unbox_usize(v_sz_4168_);
    leanh::lean_dec(v_sz_4168_);
    v_i_boxed_4174_ = leanh::lean_unbox_usize(v_i_4169_);
    leanh::lean_dec(v_i_4169_);
    v_res_4175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_4167_, v_sz_boxed_4173_, v_i_boxed_4174_, v_bs_4170_, v___y_4171_);
    leanh::lean_dec_ref(v___y_4171_);
    return v_res_4175_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(
    mut v_inst_4176_: *mut leanh::LeanObject,
    mut v_R_4177_: *mut leanh::LeanObject,
    mut v_a_4178_: *mut leanh::LeanObject,
    mut v_b_4179_: *mut leanh::LeanObject,
    mut v_c_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_4178_, v_b_4179_, v___y_4181_, v___y_4182_);
    return v___x_4184_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(
    mut v_inst_4185_: *mut leanh::LeanObject,
    mut v_R_4186_: *mut leanh::LeanObject,
    mut v_a_4187_: *mut leanh::LeanObject,
    mut v_b_4188_: *mut leanh::LeanObject,
    mut v_c_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4193_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(
            v_inst_4185_,
            v_R_4186_,
            v_a_4187_,
            v_b_4188_,
            v_c_4189_,
            v___y_4190_,
            v___y_4191_,
        );
    leanh::lean_dec_ref(v___y_4191_);
    return v_res_4193_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(
    mut v_00_u03b1_4194_: *mut leanh::LeanObject,
    mut v_msg_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4199_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_4195_, v___y_4196_, v___y_4197_);
    return v___x_4199_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b1_4200_: *mut leanh::LeanObject,
    mut v_msg_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4205_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(v_00_u03b1_4200_, v_msg_4201_, v___y_4202_, v___y_4203_);
    leanh::lean_dec_ref(v___y_4203_);
    return v_res_4205_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(
    mut v_00_u03b1_4206_: *mut leanh::LeanObject,
    mut v_preNode_4207_: *mut leanh::LeanObject,
    mut v_postNode_4208_: *mut leanh::LeanObject,
    mut v_x_4209_: *mut leanh::LeanObject,
    mut v_x_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4214_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_4207_, v_postNode_4208_, v_x_4209_, v_x_4210_, v___y_4211_, v___y_4212_);
    return v___x_4214_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(
    mut v_00_u03b1_4215_: *mut leanh::LeanObject,
    mut v_preNode_4216_: *mut leanh::LeanObject,
    mut v_postNode_4217_: *mut leanh::LeanObject,
    mut v_x_4218_: *mut leanh::LeanObject,
    mut v_x_4219_: *mut leanh::LeanObject,
    mut v___y_4220_: *mut leanh::LeanObject,
    mut v___y_4221_: *mut leanh::LeanObject,
    mut v___y_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4223_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(v_00_u03b1_4215_, v_preNode_4216_, v_postNode_4217_, v_x_4218_, v_x_4219_, v___y_4220_, v___y_4221_);
    leanh::lean_dec_ref(v___y_4221_);
    return v_res_4223_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(
    mut v_00_u03b1_4224_: *mut leanh::LeanObject,
    mut v_preNode_4225_: *mut leanh::LeanObject,
    mut v_postNode_4226_: *mut leanh::LeanObject,
    mut v___x_4227_: *mut leanh::LeanObject,
    mut v_x_4228_: *mut leanh::LeanObject,
    mut v_x_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_4225_, v_postNode_4226_, v___x_4227_, v_x_4228_, v_x_4229_, v___y_4230_, v___y_4231_);
    return v___x_4233_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(
    mut v_00_u03b1_4234_: *mut leanh::LeanObject,
    mut v_preNode_4235_: *mut leanh::LeanObject,
    mut v_postNode_4236_: *mut leanh::LeanObject,
    mut v___x_4237_: *mut leanh::LeanObject,
    mut v_x_4238_: *mut leanh::LeanObject,
    mut v_x_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4243_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(v_00_u03b1_4234_, v_preNode_4235_, v_postNode_4236_, v___x_4237_, v_x_4238_, v_x_4239_, v___y_4240_, v___y_4241_);
    leanh::lean_dec_ref(v___y_4241_);
    return v_res_4243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(
    mut v___x_4246_: *mut leanh::LeanObject,
    mut v___x_4247_: *mut leanh::LeanObject,
    mut v_as_4248_: *mut leanh::LeanObject,
    mut v_sz_4249_: usize,
    mut v_i_4250_: usize,
    mut v_b_4251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v_fst_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v_a_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: usize = 0;
    let mut v___x_4277_: usize = 0;
    let mut v_reuseFailAlloc_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut v_unused_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4253_ = lean_usize_dec_lt(v_i_4250_, v_sz_4249_);
                if v___x_4253_ == 0 {
                    v___x_4254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4254_, 0, v_b_4251_);
                    return v___x_4254_;
                } else {
                    v_snd_4255_ = leanh::lean_ctor_get(v_b_4251_, 1);
                    v_isSharedCheck_4298_ = (!leanh::lean_is_exclusive(v_b_4251_)) as u8;
                    if v_isSharedCheck_4298_ == 0 {
                        v_unused_4299_ = leanh::lean_ctor_get(v_b_4251_, 0);
                        leanh::lean_dec(v_unused_4299_);
                        v___x_4257_ = v_b_4251_;
                        v_isShared_4258_ = v_isSharedCheck_4298_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4255_);
                        leanh::lean_dec(v_b_4251_);
                        v___x_4257_ = leanh::lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4259_ = leanh::lean_ctor_get(v_snd_4255_, 0);
                v_snd_4260_ = leanh::lean_ctor_get(v_snd_4255_, 1);
                v_isSharedCheck_4297_ = (!leanh::lean_is_exclusive(v_snd_4255_)) as u8;
                if v_isSharedCheck_4297_ == 0 {
                    v___x_4262_ = v_snd_4255_;
                    v_isShared_4263_ = v_isSharedCheck_4297_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4260_);
                    leanh::lean_inc(v_fst_4259_);
                    leanh::lean_dec(v_snd_4255_);
                    v___x_4262_ = leanh::lean_box(0);
                    v_isShared_4263_ = v_isSharedCheck_4297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4264_ = lean_array_uget_borrowed(v_as_4248_, v_i_4250_);
                if leanh::lean_obj_tag(v_a_4264_) == 0 {
                    v_range_4265_ = leanh::lean_ctor_get(v_a_4264_, 0);
                    v_text_4266_ = leanh::lean_ctor_get(v_a_4264_, 1);
                    v_mod_4267_ = leanh::lean_ctor_get(v___x_4247_, 1);
                    v___x_4268_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_range_4265_);
                    v___x_4269_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_4246_, v_range_4265_);
                    leanh::lean_inc(v_fst_4259_);
                    v___x_4270_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(
                        v_mod_4267_,
                        v_fst_4259_,
                        v___x_4269_,
                        v_text_4266_,
                    );
                    if leanh::lean_obj_tag(v___x_4270_) == 1 {
                        leanh::lean_dec(v_fst_4259_);
                        v_val_4271_ = leanh::lean_ctor_get(v___x_4270_, 0);
                        leanh::lean_inc(v_val_4271_);
                        leanh::lean_dec_ref_known(v___x_4270_, 1);
                        if v_isShared_4263_ == 0 {
                            leanh::lean_ctor_set(v___x_4262_, 0, v_val_4271_);
                            v___x_4273_ = v___x_4262_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4280_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_val_4271_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_snd_4260_);
                            v___x_4273_ = v_reuseFailAlloc_4280_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4270_);
                        leanh::lean_dec(v_snd_4260_);
                        v___x_4281_ = leanh::lean_box((v___x_4253_) as usize);
                        if v_isShared_4263_ == 0 {
                            leanh::lean_ctor_set(v___x_4262_, 1, v___x_4281_);
                            v___x_4283_ = v___x_4262_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4288_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_fst_4259_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4288_, 1, v___x_4281_);
                            v___x_4283_ = v_reuseFailAlloc_4288_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0;
                    if v_isShared_4263_ == 0 {
                        v___x_4291_ = v___x_4262_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_fst_4259_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_snd_4260_);
                        v___x_4291_ = v_reuseFailAlloc_4296_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4258_ == 0 {
                    leanh::lean_ctor_set(v___x_4257_, 1, v___x_4273_);
                    leanh::lean_ctor_set(v___x_4257_, 0, v___x_4268_);
                    v___x_4275_ = v___x_4257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 1, v___x_4273_);
                    v___x_4275_ = v_reuseFailAlloc_4279_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4276_ = 1usize;
                v___x_4277_ = lean_usize_add(v_i_4250_, v___x_4276_);
                v_i_4250_ = v___x_4277_;
                v_b_4251_ = v___x_4275_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_4258_ == 0 {
                    leanh::lean_ctor_set(v___x_4257_, 1, v___x_4283_);
                    leanh::lean_ctor_set(v___x_4257_, 0, v___x_4268_);
                    v___x_4285_ = v___x_4257_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 1, v___x_4283_);
                    v___x_4285_ = v_reuseFailAlloc_4287_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                return v___x_4286_;
            }
            7 => {
                if v_isShared_4258_ == 0 {
                    leanh::lean_ctor_set(v___x_4257_, 1, v___x_4291_);
                    leanh::lean_ctor_set(v___x_4257_, 0, v___x_4289_);
                    v___x_4293_ = v___x_4257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 1, v___x_4291_);
                    v___x_4293_ = v_reuseFailAlloc_4295_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4294_, 0, v___x_4293_);
                return v___x_4294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(
    mut v___x_4300_: *mut leanh::LeanObject,
    mut v___x_4301_: *mut leanh::LeanObject,
    mut v_as_4302_: *mut leanh::LeanObject,
    mut v_sz_4303_: *mut leanh::LeanObject,
    mut v_i_4304_: *mut leanh::LeanObject,
    mut v_b_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4307_: usize = 0;
    let mut v_i_boxed_4308_: usize = 0;
    let mut v_res_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4307_ = leanh::lean_unbox_usize(v_sz_4303_);
    leanh::lean_dec(v_sz_4303_);
    v_i_boxed_4308_ = leanh::lean_unbox_usize(v_i_4304_);
    leanh::lean_dec(v_i_4304_);
    v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_4300_, v___x_4301_, v_as_4302_, v_sz_boxed_4307_, v_i_boxed_4308_, v_b_4305_);
    leanh::lean_dec_ref(v_as_4302_);
    leanh::lean_dec_ref(v___x_4301_);
    leanh::lean_dec_ref(v___x_4300_);
    return v_res_4309_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(
    mut v_p_4310_: *mut leanh::LeanObject,
    mut v___x_4311_: *mut leanh::LeanObject,
    mut v___x_4312_: *mut leanh::LeanObject,
    mut v_as_4313_: *mut leanh::LeanObject,
    mut v_sz_4314_: usize,
    mut v_i_4315_: usize,
    mut v_b_4316_: *mut leanh::LeanObject,
    mut v___y_4317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: usize = 0;
    let mut v___x_4322_: usize = 0;
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contentChanges_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4333_: usize = 0;
    let mut v___x_4334_: usize = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4339_: u8 = 0;
    let mut v_fst_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: u8 = 0;
    let mut v_snd_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_unused_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4357_: u8 = 0;
    let mut v_snd_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_unused_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v_snd_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_unused_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_a_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4324_ = lean_usize_dec_lt(v_i_4315_, v_sz_4314_);
                if v___x_4324_ == 0 {
                    v___x_4325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4325_, 0, v_b_4316_);
                    return v___x_4325_;
                } else {
                    v_contentChanges_4326_ = leanh::lean_ctor_get(v_p_4310_, 1);
                    v___x_4327_ = leanh::lean_box(0);
                    v_a_4328_ = lean_array_uget_borrowed(v_as_4313_, v_i_4315_);
                    v___x_4329_ = 0;
                    v___x_4330_ = leanh::lean_box((v___x_4329_) as usize);
                    leanh::lean_inc(v_a_4328_);
                    v___x_4331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4331_, 0, v_a_4328_);
                    leanh::lean_ctor_set(v___x_4331_, 1, v___x_4330_);
                    v___x_4332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4332_, 0, v___x_4327_);
                    leanh::lean_ctor_set(v___x_4332_, 1, v___x_4331_);
                    v_sz_4333_ = lean_array_size(v_contentChanges_4326_);
                    v___x_4334_ = 0usize;
                    v___x_4335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_4311_, v___x_4312_, v_contentChanges_4326_, v_sz_4333_, v___x_4334_, v___x_4332_);
                    if leanh::lean_obj_tag(v___x_4335_) == 0 {
                        v_a_4336_ = leanh::lean_ctor_get(v___x_4335_, 0);
                        v_isSharedCheck_4378_ =
                            (!leanh::lean_is_exclusive(v___x_4335_)) as u8;
                        if v_isSharedCheck_4378_ == 0 {
                            v___x_4338_ = v___x_4335_;
                            v_isShared_4339_ = v_isSharedCheck_4378_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4336_);
                            leanh::lean_dec(v___x_4335_);
                            v___x_4338_ = leanh::lean_box(0);
                            v_isShared_4339_ = v_isSharedCheck_4378_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4316_);
                        v_a_4379_ = leanh::lean_ctor_get(v___x_4335_, 0);
                        v_isSharedCheck_4386_ =
                            (!leanh::lean_is_exclusive(v___x_4335_)) as u8;
                        if v_isSharedCheck_4386_ == 0 {
                            v___x_4381_ = v___x_4335_;
                            v_isShared_4382_ = v_isSharedCheck_4386_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4379_);
                            leanh::lean_dec(v___x_4335_);
                            v___x_4381_ = leanh::lean_box(0);
                            v_isShared_4382_ = v_isSharedCheck_4386_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4321_ = 1usize;
                v___x_4322_ = lean_usize_add(v_i_4315_, v___x_4321_);
                v_i_4315_ = v___x_4322_;
                v_b_4316_ = v_a_4320_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_4340_ = leanh::lean_ctor_get(v_a_4336_, 0);
                if leanh::lean_obj_tag(v_fst_4340_) == 0 {
                    leanh::lean_del_object(v___x_4338_);
                    v_snd_4341_ = leanh::lean_ctor_get(v_a_4336_, 1);
                    leanh::lean_inc(v_snd_4341_);
                    leanh::lean_dec(v_a_4336_);
                    v_snd_4342_ = leanh::lean_ctor_get(v_snd_4341_, 1);
                    v___x_4343_ = (leanh::lean_unbox(v_snd_4342_) as u8);
                    if v___x_4343_ == 0 {
                        v_snd_4344_ = leanh::lean_ctor_get(v_b_4316_, 1);
                        leanh::lean_inc(v_snd_4344_);
                        leanh::lean_dec_ref(v_b_4316_);
                        v_fst_4345_ = leanh::lean_ctor_get(v_snd_4341_, 0);
                        v_isSharedCheck_4353_ =
                            (!leanh::lean_is_exclusive(v_snd_4341_)) as u8;
                        if v_isSharedCheck_4353_ == 0 {
                            v_unused_4354_ = leanh::lean_ctor_get(v_snd_4341_, 1);
                            leanh::lean_dec(v_unused_4354_);
                            v___x_4347_ = v_snd_4341_;
                            v_isShared_4348_ = v_isSharedCheck_4353_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_4345_);
                            leanh::lean_dec(v_snd_4341_);
                            v___x_4347_ = leanh::lean_box(0);
                            v_isShared_4348_ = v_isSharedCheck_4353_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_4362_ =
                            (!leanh::lean_is_exclusive(v_snd_4341_)) as u8;
                        if v_isSharedCheck_4362_ == 0 {
                            v_unused_4363_ = leanh::lean_ctor_get(v_snd_4341_, 1);
                            leanh::lean_dec(v_unused_4363_);
                            v_unused_4364_ = leanh::lean_ctor_get(v_snd_4341_, 0);
                            leanh::lean_dec(v_unused_4364_);
                            v___x_4356_ = v_snd_4341_;
                            v_isShared_4357_ = v_isSharedCheck_4362_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_snd_4341_);
                            v___x_4356_ = leanh::lean_box(0);
                            v_isShared_4357_ = v_isSharedCheck_4362_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4340_);
                    v_isSharedCheck_4375_ = (!leanh::lean_is_exclusive(v_a_4336_)) as u8;
                    if v_isSharedCheck_4375_ == 0 {
                        v_unused_4376_ = leanh::lean_ctor_get(v_a_4336_, 1);
                        leanh::lean_dec(v_unused_4376_);
                        v_unused_4377_ = leanh::lean_ctor_get(v_a_4336_, 0);
                        leanh::lean_dec(v_unused_4377_);
                        v___x_4366_ = v_a_4336_;
                        v_isShared_4367_ = v_isSharedCheck_4375_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_4336_);
                        v___x_4366_ = leanh::lean_box(0);
                        v_isShared_4367_ = v_isSharedCheck_4375_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4349_ = lean_array_push(v_snd_4344_, v_fst_4345_);
                if v_isShared_4348_ == 0 {
                    leanh::lean_ctor_set(v___x_4347_, 1, v___x_4349_);
                    leanh::lean_ctor_set(v___x_4347_, 0, v___x_4327_);
                    v___x_4351_ = v___x_4347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___x_4349_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_4320_ = v___x_4351_;
                state = 1;
                continue;
            }
            5 => {
                v_snd_4358_ = leanh::lean_ctor_get(v_b_4316_, 1);
                leanh::lean_inc(v_snd_4358_);
                leanh::lean_dec_ref(v_b_4316_);
                if v_isShared_4357_ == 0 {
                    leanh::lean_ctor_set(v___x_4356_, 1, v_snd_4358_);
                    leanh::lean_ctor_set(v___x_4356_, 0, v___x_4327_);
                    v___x_4360_ = v___x_4356_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_snd_4358_);
                    v___x_4360_ = v_reuseFailAlloc_4361_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4320_ = v___x_4360_;
                state = 1;
                continue;
            }
            7 => {
                v_snd_4368_ = leanh::lean_ctor_get(v_b_4316_, 1);
                leanh::lean_inc(v_snd_4368_);
                leanh::lean_dec_ref(v_b_4316_);
                if v_isShared_4367_ == 0 {
                    leanh::lean_ctor_set(v___x_4366_, 1, v_snd_4368_);
                    v___x_4370_ = v___x_4366_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_fst_4340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 1, v_snd_4368_);
                    v___x_4370_ = v_reuseFailAlloc_4374_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4339_ == 0 {
                    leanh::lean_ctor_set(v___x_4338_, 0, v___x_4370_);
                    v___x_4372_ = v___x_4338_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
                    v___x_4372_ = v_reuseFailAlloc_4373_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4372_;
            }
            10 => {
                if v_isShared_4382_ == 0 {
                    v___x_4384_ = v___x_4381_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
                    v___x_4384_ = v_reuseFailAlloc_4385_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(
    mut v_p_4387_: *mut leanh::LeanObject,
    mut v___x_4388_: *mut leanh::LeanObject,
    mut v___x_4389_: *mut leanh::LeanObject,
    mut v_as_4390_: *mut leanh::LeanObject,
    mut v_sz_4391_: *mut leanh::LeanObject,
    mut v_i_4392_: *mut leanh::LeanObject,
    mut v_b_4393_: *mut leanh::LeanObject,
    mut v___y_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4396_: usize = 0;
    let mut v_i_boxed_4397_: usize = 0;
    let mut v_res_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4396_ = leanh::lean_unbox_usize(v_sz_4391_);
    leanh::lean_dec(v_sz_4391_);
    v_i_boxed_4397_ = leanh::lean_unbox_usize(v_i_4392_);
    leanh::lean_dec(v_i_4392_);
    v_res_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_4387_, v___x_4388_, v___x_4389_, v_as_4390_, v_sz_boxed_4396_, v_i_boxed_4397_, v_b_4393_, v___y_4394_);
    leanh::lean_dec_ref(v___y_4394_);
    leanh::lean_dec_ref(v_as_4390_);
    leanh::lean_dec_ref(v___x_4389_);
    leanh::lean_dec_ref(v___x_4388_);
    leanh::lean_dec_ref(v_p_4387_);
    return v_res_4398_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(
    mut v_p_4402_: *mut leanh::LeanObject,
    mut v_oldInlayHints_4403_: *mut leanh::LeanObject,
    mut v_a_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_doc_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4411_: usize = 0;
    let mut v___x_4412_: usize = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v_fst_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_a_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_4406_ = leanh::lean_ctor_get(v_a_4404_, 1);
                v_toEditableDocumentCore_4407_ = leanh::lean_ctor_get(v_doc_4406_, 0);
                v_meta_4408_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4407_, 0);
                v_text_4409_ = leanh::lean_ctor_get(v_meta_4408_, 3);
                v___x_4410_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0;
                v_sz_4411_ = lean_array_size(v_oldInlayHints_4403_);
                v___x_4412_ = 0usize;
                v___x_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_4402_, v_text_4409_, v_meta_4408_, v_oldInlayHints_4403_, v_sz_4411_, v___x_4412_, v___x_4410_, v_a_4404_);
                if leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4427_ = (!leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4416_ = v___x_4413_;
                        v_isShared_4417_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4414_);
                        leanh::lean_dec(v___x_4413_);
                        v___x_4416_ = leanh::lean_box(0);
                        v_isShared_4417_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4428_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4435_ = (!leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4435_ == 0 {
                        v___x_4430_ = v___x_4413_;
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4428_);
                        leanh::lean_dec(v___x_4413_);
                        v___x_4430_ = leanh::lean_box(0);
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4418_ = leanh::lean_ctor_get(v_a_4414_, 0);
                if leanh::lean_obj_tag(v_fst_4418_) == 0 {
                    v_snd_4419_ = leanh::lean_ctor_get(v_a_4414_, 1);
                    leanh::lean_inc(v_snd_4419_);
                    leanh::lean_dec(v_a_4414_);
                    if v_isShared_4417_ == 0 {
                        leanh::lean_ctor_set(v___x_4416_, 0, v_snd_4419_);
                        v___x_4421_ = v___x_4416_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_snd_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4418_);
                    leanh::lean_dec(v_a_4414_);
                    v_val_4423_ = leanh::lean_ctor_get(v_fst_4418_, 0);
                    leanh::lean_inc(v_val_4423_);
                    leanh::lean_dec_ref_known(v_fst_4418_, 1);
                    if v_isShared_4417_ == 0 {
                        leanh::lean_ctor_set(v___x_4416_, 0, v_val_4423_);
                        v___x_4425_ = v___x_4416_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_val_4423_);
                        v___x_4425_ = v_reuseFailAlloc_4426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4421_;
            }
            3 => {
                return v___x_4425_;
            }
            4 => {
                if v_isShared_4431_ == 0 {
                    v___x_4433_ = v___x_4430_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
                    v___x_4433_ = v_reuseFailAlloc_4434_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(
    mut v_p_4436_: *mut leanh::LeanObject,
    mut v_oldInlayHints_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4440_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_4436_, v_oldInlayHints_4437_, v_a_4438_);
    leanh::lean_dec_ref(v_a_4438_);
    leanh::lean_dec_ref(v_oldInlayHints_4437_);
    leanh::lean_dec_ref(v_p_4436_);
    return v_res_4440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(
    mut v___x_4441_: *mut leanh::LeanObject,
    mut v___x_4442_: *mut leanh::LeanObject,
    mut v_as_4443_: *mut leanh::LeanObject,
    mut v_sz_4444_: usize,
    mut v_i_4445_: usize,
    mut v_b_4446_: *mut leanh::LeanObject,
    mut v___y_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_4441_, v___x_4442_, v_as_4443_, v_sz_4444_, v_i_4445_, v_b_4446_);
    return v___x_4449_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(
    mut v___x_4450_: *mut leanh::LeanObject,
    mut v___x_4451_: *mut leanh::LeanObject,
    mut v_as_4452_: *mut leanh::LeanObject,
    mut v_sz_4453_: *mut leanh::LeanObject,
    mut v_i_4454_: *mut leanh::LeanObject,
    mut v_b_4455_: *mut leanh::LeanObject,
    mut v___y_4456_: *mut leanh::LeanObject,
    mut v___y_4457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4458_: usize = 0;
    let mut v_i_boxed_4459_: usize = 0;
    let mut v_res_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4458_ = leanh::lean_unbox_usize(v_sz_4453_);
    leanh::lean_dec(v_sz_4453_);
    v_i_boxed_4459_ = leanh::lean_unbox_usize(v_i_4454_);
    leanh::lean_dec(v_i_4454_);
    v_res_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_4450_, v___x_4451_, v_as_4452_, v_sz_boxed_4458_, v_i_boxed_4459_, v_b_4455_, v___y_4456_);
    leanh::lean_dec_ref(v___y_4456_);
    leanh::lean_dec_ref(v_as_4452_);
    leanh::lean_dec_ref(v___x_4451_);
    leanh::lean_dec_ref(v___x_4450_);
    return v_res_4460_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(
    mut v_a_4461_: *mut leanh::LeanObject,
    mut v_as_4462_: *mut leanh::LeanObject,
    mut v_i_4463_: usize,
    mut v_stop_4464_: usize,
) -> u8 {
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: usize = 0;
    let mut v___x_4469_: usize = 0;
    let mut v___x_4471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4465_ = lean_usize_dec_eq(v_i_4463_, v_stop_4464_);
                if v___x_4465_ == 0 {
                    v___x_4466_ = lean_array_uget_borrowed(v_as_4462_, v_i_4463_);
                    v___x_4467_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_4461_, v___x_4466_);
                    if v___x_4467_ == 0 {
                        v___x_4468_ = 1usize;
                        v___x_4469_ = lean_usize_add(v_i_4463_, v___x_4468_);
                        v_i_4463_ = v___x_4469_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4467_;
                    }
                } else {
                    v___x_4471_ = 0;
                    return v___x_4471_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(
    mut v_a_4472_: *mut leanh::LeanObject,
    mut v_as_4473_: *mut leanh::LeanObject,
    mut v_i_4474_: *mut leanh::LeanObject,
    mut v_stop_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4476_: usize = 0;
    let mut v_stop_boxed_4477_: usize = 0;
    let mut v_res_4478_: u8 = 0;
    let mut v_r_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4476_ = leanh::lean_unbox_usize(v_i_4474_);
    leanh::lean_dec(v_i_4474_);
    v_stop_boxed_4477_ = leanh::lean_unbox_usize(v_stop_4475_);
    leanh::lean_dec(v_stop_4475_);
    v_res_4478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_4472_, v_as_4473_, v_i_boxed_4476_, v_stop_boxed_4477_);
    leanh::lean_dec_ref(v_as_4473_);
    leanh::lean_dec_ref(v_a_4472_);
    v_r_4479_ = leanh::lean_box((v_res_4478_) as usize);
    return v_r_4479_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(
    mut v_as_4480_: *mut leanh::LeanObject,
    mut v_a_4481_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: u8 = 0;
    v___x_4482_ = leanh::lean_unsigned_to_nat(0);
    v___x_4483_ = lean_array_get_size(v_as_4480_);
    v___x_4484_ = lean_nat_dec_lt(v___x_4482_, v___x_4483_);
    if v___x_4484_ == 0 {
        return v___x_4484_;
    } else {
        if v___x_4484_ == 0 {
            return v___x_4484_;
        } else {
            let mut v___x_4485_: usize = 0;
            let mut v___x_4486_: usize = 0;
            let mut v___x_4487_: u8 = 0;
            v___x_4485_ = 0usize;
            v___x_4486_ = lean_usize_of_nat(v___x_4483_);
            v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_4481_, v_as_4480_, v___x_4485_, v___x_4486_);
            return v___x_4487_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(
    mut v_as_4488_: *mut leanh::LeanObject,
    mut v_a_4489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_4488_, v_a_4489_);
    leanh::lean_dec_ref(v_a_4489_);
    leanh::lean_dec_ref(v_as_4488_);
    v_r_4491_ = leanh::lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(
    mut v___x_4492_: *mut leanh::LeanObject,
    mut v_as_4493_: *mut leanh::LeanObject,
    mut v_i_4494_: usize,
    mut v_stop_4495_: usize,
) -> u8 {
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdits_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: usize = 0;
    let mut v___x_4501_: usize = 0;
    let mut v___x_4503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4496_ = lean_usize_dec_eq(v_i_4494_, v_stop_4495_);
                if v___x_4496_ == 0 {
                    v___x_4497_ = lean_array_uget_borrowed(v_as_4493_, v_i_4494_);
                    v_textEdits_4498_ = leanh::lean_ctor_get(v___x_4497_, 3);
                    v___x_4499_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_4498_, v___x_4492_);
                    if v___x_4499_ == 0 {
                        v___x_4500_ = 1usize;
                        v___x_4501_ = lean_usize_add(v_i_4494_, v___x_4500_);
                        v_i_4494_ = v___x_4501_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4499_;
                    }
                } else {
                    v___x_4503_ = 0;
                    return v___x_4503_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(
    mut v___x_4504_: *mut leanh::LeanObject,
    mut v_as_4505_: *mut leanh::LeanObject,
    mut v_i_4506_: *mut leanh::LeanObject,
    mut v_stop_4507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4508_: usize = 0;
    let mut v_stop_boxed_4509_: usize = 0;
    let mut v_res_4510_: u8 = 0;
    let mut v_r_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4508_ = leanh::lean_unbox_usize(v_i_4506_);
    leanh::lean_dec(v_i_4506_);
    v_stop_boxed_4509_ = leanh::lean_unbox_usize(v_stop_4507_);
    leanh::lean_dec(v_stop_4507_);
    v_res_4510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_4504_, v_as_4505_, v_i_boxed_4508_, v_stop_boxed_4509_);
    leanh::lean_dec_ref(v_as_4505_);
    leanh::lean_dec_ref(v___x_4504_);
    v_r_4511_ = leanh::lean_box((v_res_4510_) as usize);
    return v_r_4511_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(
    mut v_oldInlayHints_4512_: *mut leanh::LeanObject,
    mut v___x_4513_: *mut leanh::LeanObject,
    mut v_as_4514_: *mut leanh::LeanObject,
    mut v_i_4515_: usize,
    mut v_stop_4516_: usize,
) -> u8 {
    let mut v___x_4517_: u8 = 0;
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: usize = 0;
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v___x_4539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4517_ = lean_usize_dec_eq(v_i_4515_, v_stop_4516_);
                if v___x_4517_ == 0 {
                    v___x_4518_ = 1;
                    v___x_4519_ = lean_array_uget(v_as_4514_, v_i_4515_);
                    if leanh::lean_obj_tag(v___x_4519_) == 0 {
                        v_range_4520_ = leanh::lean_ctor_get(v___x_4519_, 0);
                        v_text_4521_ = leanh::lean_ctor_get(v___x_4519_, 1);
                        v_isSharedCheck_4538_ =
                            (!leanh::lean_is_exclusive(v___x_4519_)) as u8;
                        if v_isSharedCheck_4538_ == 0 {
                            v___x_4523_ = v___x_4519_;
                            v_isShared_4524_ = v_isSharedCheck_4538_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_text_4521_);
                            leanh::lean_inc(v_range_4520_);
                            leanh::lean_dec(v___x_4519_);
                            v___x_4523_ = leanh::lean_box(0);
                            v_isShared_4524_ = v_isSharedCheck_4538_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4519_);
                        return v___x_4518_;
                    }
                } else {
                    v___x_4539_ = 0;
                    return v___x_4539_;
                }
            }
            1 => {
                v___x_4525_ = leanh::lean_unsigned_to_nat(0);
                v___x_4526_ = lean_array_get_size(v_oldInlayHints_4512_);
                v___x_4527_ = lean_nat_dec_lt(v___x_4525_, v___x_4526_);
                if v___x_4527_ == 0 {
                    leanh::lean_del_object(v___x_4523_);
                    leanh::lean_dec_ref(v_text_4521_);
                    leanh::lean_dec_ref(v_range_4520_);
                    return v___x_4518_;
                } else {
                    if v___x_4527_ == 0 {
                        leanh::lean_del_object(v___x_4523_);
                        leanh::lean_dec_ref(v_text_4521_);
                        leanh::lean_dec_ref(v_range_4520_);
                        return v___x_4518_;
                    } else {
                        v___x_4528_ =
                            l_Lean_FileMap_lspRangeToUtf8Range(v___x_4513_, v_range_4520_);
                        if v_isShared_4524_ == 0 {
                            leanh::lean_ctor_set(v___x_4523_, 0, v___x_4528_);
                            v___x_4530_ = v___x_4523_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4537_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4528_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_text_4521_);
                            v___x_4530_ = v_reuseFailAlloc_4537_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4531_ = 0usize;
                v___x_4532_ = lean_usize_of_nat(v___x_4526_);
                v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_4530_, v_oldInlayHints_4512_, v___x_4531_, v___x_4532_);
                leanh::lean_dec_ref(v___x_4530_);
                if v___x_4533_ == 0 {
                    return v___x_4518_;
                } else {
                    if v___x_4517_ == 0 {
                        v___x_4534_ = 1usize;
                        v___x_4535_ = lean_usize_add(v_i_4515_, v___x_4534_);
                        v_i_4515_ = v___x_4535_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4518_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(
    mut v_oldInlayHints_4540_: *mut leanh::LeanObject,
    mut v___x_4541_: *mut leanh::LeanObject,
    mut v_as_4542_: *mut leanh::LeanObject,
    mut v_i_4543_: *mut leanh::LeanObject,
    mut v_stop_4544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4545_: usize = 0;
    let mut v_stop_boxed_4546_: usize = 0;
    let mut v_res_4547_: u8 = 0;
    let mut v_r_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4545_ = leanh::lean_unbox_usize(v_i_4543_);
    leanh::lean_dec(v_i_4543_);
    v_stop_boxed_4546_ = leanh::lean_unbox_usize(v_stop_4544_);
    leanh::lean_dec(v_stop_4544_);
    v_res_4547_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_4540_, v___x_4541_, v_as_4542_, v_i_boxed_4545_, v_stop_boxed_4546_);
    leanh::lean_dec_ref(v_as_4542_);
    leanh::lean_dec_ref(v___x_4541_);
    leanh::lean_dec_ref(v_oldInlayHints_4540_);
    v_r_4548_ = leanh::lean_box((v_res_4547_) as usize);
    return v_r_4548_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(
    mut v_p_4549_: *mut leanh::LeanObject,
    mut v_oldInlayHints_4550_: *mut leanh::LeanObject,
    mut v_a_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4554_: u8 = 0;
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contentChanges_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: u8 = 0;
    let mut v_doc_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: usize = 0;
    let mut v___x_4570_: usize = 0;
    let mut v___x_4571_: u8 = 0;
    let mut v___x_4572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_contentChanges_4560_ = leanh::lean_ctor_get(v_p_4549_, 1);
                v___x_4561_ = leanh::lean_unsigned_to_nat(0);
                v___x_4562_ = lean_array_get_size(v_contentChanges_4560_);
                v___x_4563_ = lean_nat_dec_lt(v___x_4561_, v___x_4562_);
                if v___x_4563_ == 0 {
                    v___x_4564_ = 1;
                    v___y_4554_ = v___x_4564_;
                    state = 1;
                    continue;
                } else {
                    if v___x_4563_ == 0 {
                        v___y_4554_ = v___x_4563_;
                        state = 1;
                        continue;
                    } else {
                        v_doc_4565_ = leanh::lean_ctor_get(v_a_4551_, 1);
                        v_toEditableDocumentCore_4566_ =
                            leanh::lean_ctor_get(v_doc_4565_, 0);
                        v_meta_4567_ =
                            leanh::lean_ctor_get(v_toEditableDocumentCore_4566_, 0);
                        v_text_4568_ = leanh::lean_ctor_get(v_meta_4567_, 3);
                        v___x_4569_ = 0usize;
                        v___x_4570_ = lean_usize_of_nat(v___x_4562_);
                        v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_4550_, v_text_4568_, v_contentChanges_4560_, v___x_4569_, v___x_4570_);
                        if v___x_4571_ == 0 {
                            v___y_4554_ = v___x_4563_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4572_ = 0;
                            v___y_4554_ = v___x_4572_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4555_ = lean_io_mono_ms_now();
                if v___y_4554_ == 0 {
                    v___x_4556_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4556_, 0, v___x_4555_);
                    v___x_4557_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4557_, 0, v___x_4556_);
                    return v___x_4557_;
                } else {
                    leanh::lean_dec(v___x_4555_);
                    v___x_4558_ = leanh::lean_box(0);
                    v___x_4559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
                    return v___x_4559_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(
    mut v_p_4573_: *mut leanh::LeanObject,
    mut v_oldInlayHints_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4577_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_4573_, v_oldInlayHints_4574_, v_a_4575_);
    leanh::lean_dec_ref(v_a_4575_);
    leanh::lean_dec_ref(v_oldInlayHints_4574_);
    leanh::lean_dec_ref(v_p_4573_);
    return v_res_4577_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleInlayHintsDidChange(
    mut v_p_4578_: *mut leanh::LeanObject,
    mut v_a_4579_: *mut leanh::LeanObject,
    mut v_a_4580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_oldInlayHints_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4592_: u8 = 0;
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v_a_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4607_: u8 = 0;
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4611_: u8 = 0;
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_unused_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_oldInlayHints_4582_ = leanh::lean_ctor_get(v_a_4579_, 0);
                v_isSharedCheck_4612_ = (!leanh::lean_is_exclusive(v_a_4579_)) as u8;
                if v_isSharedCheck_4612_ == 0 {
                    v_unused_4613_ = leanh::lean_ctor_get(v_a_4579_, 2);
                    leanh::lean_dec(v_unused_4613_);
                    v_unused_4614_ = leanh::lean_ctor_get(v_a_4579_, 1);
                    leanh::lean_dec(v_unused_4614_);
                    v___x_4584_ = v_a_4579_;
                    v_isShared_4585_ = v_isSharedCheck_4612_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_oldInlayHints_4582_);
                    leanh::lean_dec(v_a_4579_);
                    v___x_4584_ = leanh::lean_box(0);
                    v_isShared_4585_ = v_isSharedCheck_4612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4586_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_4578_, v_oldInlayHints_4582_, v_a_4580_);
                if leanh::lean_obj_tag(v___x_4586_) == 0 {
                    v_a_4587_ = leanh::lean_ctor_get(v___x_4586_, 0);
                    leanh::lean_inc(v_a_4587_);
                    leanh::lean_dec_ref_known(v___x_4586_, 1);
                    v___x_4588_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_4578_, v_oldInlayHints_4582_, v_a_4580_);
                    leanh::lean_dec_ref(v_oldInlayHints_4582_);
                    v_a_4589_ = leanh::lean_ctor_get(v___x_4588_, 0);
                    v_isSharedCheck_4603_ = (!leanh::lean_is_exclusive(v___x_4588_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4591_ = v___x_4588_;
                        v_isShared_4592_ = v_isSharedCheck_4603_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4589_);
                        leanh::lean_dec(v___x_4588_);
                        v___x_4591_ = leanh::lean_box(0);
                        v_isShared_4592_ = v_isSharedCheck_4603_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4584_);
                    leanh::lean_dec_ref(v_oldInlayHints_4582_);
                    v_a_4604_ = leanh::lean_ctor_get(v___x_4586_, 0);
                    v_isSharedCheck_4611_ = (!leanh::lean_is_exclusive(v___x_4586_)) as u8;
                    if v_isSharedCheck_4611_ == 0 {
                        v___x_4606_ = v___x_4586_;
                        v_isShared_4607_ = v_isSharedCheck_4611_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4604_);
                        leanh::lean_dec(v___x_4586_);
                        v___x_4606_ = leanh::lean_box(0);
                        v_isShared_4607_ = v_isSharedCheck_4611_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4593_ = leanh::lean_unsigned_to_nat(0);
                v___x_4594_ = 1;
                if v_isShared_4585_ == 0 {
                    leanh::lean_ctor_set(v___x_4584_, 2, v_a_4589_);
                    leanh::lean_ctor_set(v___x_4584_, 1, v___x_4593_);
                    leanh::lean_ctor_set(v___x_4584_, 0, v_a_4587_);
                    v___x_4596_ = v___x_4584_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 1, v___x_4593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_a_4589_);
                    v___x_4596_ = v_reuseFailAlloc_4602_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4596_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4594_,
                );
                v___x_4597_ = leanh::lean_box(0);
                v___x_4598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4598_, 0, v___x_4597_);
                leanh::lean_ctor_set(v___x_4598_, 1, v___x_4596_);
                if v_isShared_4592_ == 0 {
                    leanh::lean_ctor_set(v___x_4591_, 0, v___x_4598_);
                    v___x_4600_ = v___x_4591_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
                    v___x_4600_ = v_reuseFailAlloc_4601_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4600_;
            }
            5 => {
                if v_isShared_4607_ == 0 {
                    v___x_4609_ = v___x_4606_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
                    v___x_4609_ = v_reuseFailAlloc_4610_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(
    mut v_p_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
    mut v_a_4617_: *mut leanh::LeanObject,
    mut v_a_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4619_ =
        l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_4615_, v_a_4616_, v_a_4617_);
    leanh::lean_dec_ref(v_a_4617_);
    leanh::lean_dec_ref(v_p_4615_);
    return v_res_4619_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(
    mut v___x_4620_: *mut leanh::LeanObject,
    mut v_x_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    return v___x_4620_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(
    mut v___x_4622_: *mut leanh::LeanObject,
    mut v_x_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4624_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_4622_, v_x_4623_);
    leanh::lean_dec_ref(v_x_4623_);
    return v_res_4624_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(
    mut v_x_4625_: *mut leanh::LeanObject,
    mut v_x_4626_: *mut leanh::LeanObject,
    mut v_x_4627_: *mut leanh::LeanObject,
    mut v_x_4628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4629_ = leanh::lean_ctor_get(v_x_4625_, 0);
                v_vs_4630_ = leanh::lean_ctor_get(v_x_4625_, 1);
                v_isSharedCheck_4654_ = (!leanh::lean_is_exclusive(v_x_4625_)) as u8;
                if v_isSharedCheck_4654_ == 0 {
                    v___x_4632_ = v_x_4625_;
                    v_isShared_4633_ = v_isSharedCheck_4654_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4630_);
                    leanh::lean_inc(v_ks_4629_);
                    leanh::lean_dec(v_x_4625_);
                    v___x_4632_ = leanh::lean_box(0);
                    v_isShared_4633_ = v_isSharedCheck_4654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4634_ = lean_array_get_size(v_ks_4629_);
                v___x_4635_ = lean_nat_dec_lt(v_x_4626_, v___x_4634_);
                if v___x_4635_ == 0 {
                    leanh::lean_dec(v_x_4626_);
                    v___x_4636_ = lean_array_push(v_ks_4629_, v_x_4627_);
                    v___x_4637_ = lean_array_push(v_vs_4630_, v_x_4628_);
                    if v_isShared_4633_ == 0 {
                        leanh::lean_ctor_set(v___x_4632_, 1, v___x_4637_);
                        leanh::lean_ctor_set(v___x_4632_, 0, v___x_4636_);
                        v___x_4639_ = v___x_4632_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4640_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4636_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 1, v___x_4637_);
                        v___x_4639_ = v_reuseFailAlloc_4640_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4641_ = lean_array_fget_borrowed(v_ks_4629_, v_x_4626_);
                    v___x_4642_ = lean_string_dec_eq(v_x_4627_, v_k_x27_4641_);
                    if v___x_4642_ == 0 {
                        if v_isShared_4633_ == 0 {
                            v___x_4644_ = v___x_4632_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4648_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_ks_4629_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_vs_4630_);
                            v___x_4644_ = v_reuseFailAlloc_4648_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4649_ = lean_array_fset(v_ks_4629_, v_x_4626_, v_x_4627_);
                        v___x_4650_ = lean_array_fset(v_vs_4630_, v_x_4626_, v_x_4628_);
                        leanh::lean_dec(v_x_4626_);
                        if v_isShared_4633_ == 0 {
                            leanh::lean_ctor_set(v___x_4632_, 1, v___x_4650_);
                            leanh::lean_ctor_set(v___x_4632_, 0, v___x_4649_);
                            v___x_4652_ = v___x_4632_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4653_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4649_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4650_);
                            v___x_4652_ = v_reuseFailAlloc_4653_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4639_;
            }
            3 => {
                v___x_4645_ = leanh::lean_unsigned_to_nat(1);
                v___x_4646_ = lean_nat_add(v_x_4626_, v___x_4645_);
                leanh::lean_dec(v_x_4626_);
                v_x_4625_ = v___x_4644_;
                v_x_4626_ = v___x_4646_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(
    mut v_n_4655_: *mut leanh::LeanObject,
    mut v_k_4656_: *mut leanh::LeanObject,
    mut v_v_4657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4658_ = leanh::lean_unsigned_to_nat(0);
    v___x_4659_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_4655_, v___x_4658_, v_k_4656_, v_v_4657_);
    return v___x_4659_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0()
-> usize {
    let mut v___x_4660_: usize = 0;
    let mut v___x_4661_: usize = 0;
    let mut v___x_4662_: usize = 0;
    v___x_4660_ = 5usize;
    v___x_4661_ = 1usize;
    v___x_4662_ = lean_usize_shift_left(v___x_4661_, v___x_4660_);
    return v___x_4662_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1()
-> usize {
    let mut v___x_4663_: usize = 0;
    let mut v___x_4664_: usize = 0;
    let mut v___x_4665_: usize = 0;
    v___x_4663_ = 1usize;
    v___x_4664_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
    v___x_4665_ = lean_usize_sub(v___x_4664_, v___x_4663_);
    return v___x_4665_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4666_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(
    mut v_x_4667_: *mut leanh::LeanObject,
    mut v_x_4668_: usize,
    mut v_x_4669_: usize,
    mut v_x_4670_: *mut leanh::LeanObject,
    mut v_x_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: usize = 0;
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: usize = 0;
    let mut v___x_4676_: usize = 0;
    let mut v_j_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: u8 = 0;
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v_v_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4697_: u8 = 0;
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v_node_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4707_: u8 = 0;
    let mut v___x_4708_: usize = 0;
    let mut v___x_4709_: usize = 0;
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4716_: u8 = 0;
    let mut v_unused_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4722_: u8 = 0;
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4727_: u8 = 0;
    let mut v_ks_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: usize = 0;
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: u8 = 0;
    let mut v_reuseFailAlloc_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4667_) == 0 {
                    v_es_4672_ = leanh::lean_ctor_get(v_x_4667_, 0);
                    v___x_4673_ = 5usize;
                    v___x_4674_ = 1usize;
                    v___x_4675_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1);
                    v___x_4676_ = lean_usize_land(v_x_4668_, v___x_4675_);
                    v_j_4677_ = lean_usize_to_nat(v___x_4676_);
                    v___x_4678_ = lean_array_get_size(v_es_4672_);
                    v___x_4679_ = lean_nat_dec_lt(v_j_4677_, v___x_4678_);
                    if v___x_4679_ == 0 {
                        leanh::lean_dec(v_j_4677_);
                        leanh::lean_dec(v_x_4671_);
                        leanh::lean_dec_ref(v_x_4670_);
                        return v_x_4667_;
                    } else {
                        leanh::lean_inc_ref(v_es_4672_);
                        v_isSharedCheck_4716_ = (!leanh::lean_is_exclusive(v_x_4667_)) as u8;
                        if v_isSharedCheck_4716_ == 0 {
                            v_unused_4717_ = leanh::lean_ctor_get(v_x_4667_, 0);
                            leanh::lean_dec(v_unused_4717_);
                            v___x_4681_ = v_x_4667_;
                            v_isShared_4682_ = v_isSharedCheck_4716_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4667_);
                            v___x_4681_ = leanh::lean_box(0);
                            v_isShared_4682_ = v_isSharedCheck_4716_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4718_ = leanh::lean_ctor_get(v_x_4667_, 0);
                    v_vs_4719_ = leanh::lean_ctor_get(v_x_4667_, 1);
                    v_isSharedCheck_4739_ = (!leanh::lean_is_exclusive(v_x_4667_)) as u8;
                    if v_isSharedCheck_4739_ == 0 {
                        v___x_4721_ = v_x_4667_;
                        v_isShared_4722_ = v_isSharedCheck_4739_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4719_);
                        leanh::lean_inc(v_ks_4718_);
                        leanh::lean_dec(v_x_4667_);
                        v___x_4721_ = leanh::lean_box(0);
                        v_isShared_4722_ = v_isSharedCheck_4739_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4683_ = lean_array_fget(v_es_4672_, v_j_4677_);
                v___x_4684_ = leanh::lean_box(0);
                v_xs_x27_4685_ = lean_array_fset(v_es_4672_, v_j_4677_, v___x_4684_);
                match leanh::lean_obj_tag(v_v_4683_) {
                    0 => {
                        v_key_4692_ = leanh::lean_ctor_get(v_v_4683_, 0);
                        v_val_4693_ = leanh::lean_ctor_get(v_v_4683_, 1);
                        v_isSharedCheck_4703_ = (!leanh::lean_is_exclusive(v_v_4683_)) as u8;
                        if v_isSharedCheck_4703_ == 0 {
                            v___x_4695_ = v_v_4683_;
                            v_isShared_4696_ = v_isSharedCheck_4703_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4693_);
                            leanh::lean_inc(v_key_4692_);
                            leanh::lean_dec(v_v_4683_);
                            v___x_4695_ = leanh::lean_box(0);
                            v_isShared_4696_ = v_isSharedCheck_4703_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4704_ = leanh::lean_ctor_get(v_v_4683_, 0);
                        v_isSharedCheck_4714_ = (!leanh::lean_is_exclusive(v_v_4683_)) as u8;
                        if v_isSharedCheck_4714_ == 0 {
                            v___x_4706_ = v_v_4683_;
                            v_isShared_4707_ = v_isSharedCheck_4714_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4704_);
                            leanh::lean_dec(v_v_4683_);
                            v___x_4706_ = leanh::lean_box(0);
                            v_isShared_4707_ = v_isSharedCheck_4714_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4715_, 0, v_x_4670_);
                        leanh::lean_ctor_set(v___x_4715_, 1, v_x_4671_);
                        v___y_4687_ = v___x_4715_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4688_ = lean_array_fset(v_xs_x27_4685_, v_j_4677_, v___y_4687_);
                leanh::lean_dec(v_j_4677_);
                if v_isShared_4682_ == 0 {
                    leanh::lean_ctor_set(v___x_4681_, 0, v___x_4688_);
                    v___x_4690_ = v___x_4681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
                    v___x_4690_ = v_reuseFailAlloc_4691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4690_;
            }
            4 => {
                v___x_4697_ = lean_string_dec_eq(v_x_4670_, v_key_4692_);
                if v___x_4697_ == 0 {
                    leanh::lean_del_object(v___x_4695_);
                    v___x_4698_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4692_,
                        v_val_4693_,
                        v_x_4670_,
                        v_x_4671_,
                    );
                    v___x_4699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4699_, 0, v___x_4698_);
                    v___y_4687_ = v___x_4699_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4693_);
                    leanh::lean_dec(v_key_4692_);
                    if v_isShared_4696_ == 0 {
                        leanh::lean_ctor_set(v___x_4695_, 1, v_x_4671_);
                        leanh::lean_ctor_set(v___x_4695_, 0, v_x_4670_);
                        v___x_4701_ = v___x_4695_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_x_4670_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 1, v_x_4671_);
                        v___x_4701_ = v_reuseFailAlloc_4702_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4687_ = v___x_4701_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4708_ = lean_usize_shift_right(v_x_4668_, v___x_4673_);
                v___x_4709_ = lean_usize_add(v_x_4669_, v___x_4674_);
                v___x_4710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_4704_, v___x_4708_, v___x_4709_, v_x_4670_, v_x_4671_);
                if v_isShared_4707_ == 0 {
                    leanh::lean_ctor_set(v___x_4706_, 0, v___x_4710_);
                    v___x_4712_ = v___x_4706_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4687_ = v___x_4712_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4722_ == 0 {
                    v___x_4724_ = v___x_4721_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4738_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_ks_4718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_vs_4719_);
                    v___x_4724_ = v_reuseFailAlloc_4738_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4725_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_4724_, v_x_4670_, v_x_4671_);
                v___x_4733_ = 7usize;
                v___x_4734_ = lean_usize_dec_le(v___x_4733_, v_x_4669_);
                if v___x_4734_ == 0 {
                    v___x_4735_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4725_);
                    v___x_4736_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4737_ = lean_nat_dec_lt(v___x_4735_, v___x_4736_);
                    leanh::lean_dec(v___x_4735_);
                    v___y_4727_ = v___x_4737_;
                    state = 10;
                    continue;
                } else {
                    v___y_4727_ = v___x_4734_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4727_ == 0 {
                    v_ks_4728_ = leanh::lean_ctor_get(v_newNode_4725_, 0);
                    leanh::lean_inc_ref(v_ks_4728_);
                    v_vs_4729_ = leanh::lean_ctor_get(v_newNode_4725_, 1);
                    leanh::lean_inc_ref(v_vs_4729_);
                    leanh::lean_dec_ref(v_newNode_4725_);
                    v___x_4730_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4731_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__2);
                    v___x_4732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_4669_, v_ks_4728_, v_vs_4729_, v___x_4730_, v___x_4731_);
                    leanh::lean_dec_ref(v_vs_4729_);
                    leanh::lean_dec_ref(v_ks_4728_);
                    return v___x_4732_;
                } else {
                    return v_newNode_4725_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(
    mut v_depth_4740_: usize,
    mut v_keys_4741_: *mut leanh::LeanObject,
    mut v_vals_4742_: *mut leanh::LeanObject,
    mut v_i_4743_: *mut leanh::LeanObject,
    mut v_entries_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v_k_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: u64 = 0;
    let mut v_h_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v_h_4756_: usize = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4745_ = lean_array_get_size(v_keys_4741_);
                v___x_4746_ = lean_nat_dec_lt(v_i_4743_, v___x_4745_);
                if v___x_4746_ == 0 {
                    leanh::lean_dec(v_i_4743_);
                    return v_entries_4744_;
                } else {
                    v_k_4747_ = lean_array_fget_borrowed(v_keys_4741_, v_i_4743_);
                    v_v_4748_ = lean_array_fget_borrowed(v_vals_4742_, v_i_4743_);
                    v___x_4749_ = lean_string_hash(v_k_4747_);
                    v_h_4750_ = lean_uint64_to_usize(v___x_4749_);
                    v___x_4751_ = 5usize;
                    v___x_4752_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4753_ = 1usize;
                    v___x_4754_ = lean_usize_sub(v_depth_4740_, v___x_4753_);
                    v___x_4755_ = lean_usize_mul(v___x_4751_, v___x_4754_);
                    v_h_4756_ = lean_usize_shift_right(v_h_4750_, v___x_4755_);
                    v___x_4757_ = lean_nat_add(v_i_4743_, v___x_4752_);
                    leanh::lean_dec(v_i_4743_);
                    leanh::lean_inc(v_v_4748_);
                    leanh::lean_inc(v_k_4747_);
                    v___x_4758_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_4744_, v_h_4756_, v_depth_4740_, v_k_4747_, v_v_4748_);
                    v_i_4743_ = v___x_4757_;
                    v_entries_4744_ = v___x_4758_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(
    mut v_depth_4760_: *mut leanh::LeanObject,
    mut v_keys_4761_: *mut leanh::LeanObject,
    mut v_vals_4762_: *mut leanh::LeanObject,
    mut v_i_4763_: *mut leanh::LeanObject,
    mut v_entries_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4765_: usize = 0;
    let mut v_res_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4765_ = leanh::lean_unbox_usize(v_depth_4760_);
    leanh::lean_dec(v_depth_4760_);
    v_res_4766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_4765_, v_keys_4761_, v_vals_4762_, v_i_4763_, v_entries_4764_);
    leanh::lean_dec_ref(v_vals_4762_);
    leanh::lean_dec_ref(v_keys_4761_);
    return v_res_4766_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(
    mut v_x_4767_: *mut leanh::LeanObject,
    mut v_x_4768_: *mut leanh::LeanObject,
    mut v_x_4769_: *mut leanh::LeanObject,
    mut v_x_4770_: *mut leanh::LeanObject,
    mut v_x_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2371__boxed_4772_: usize = 0;
    let mut v_x_2372__boxed_4773_: usize = 0;
    let mut v_res_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2371__boxed_4772_ = leanh::lean_unbox_usize(v_x_4768_);
    leanh::lean_dec(v_x_4768_);
    v_x_2372__boxed_4773_ = leanh::lean_unbox_usize(v_x_4769_);
    leanh::lean_dec(v_x_4769_);
    v_res_4774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_4767_, v_x_2371__boxed_4772_, v_x_2372__boxed_4773_, v_x_4770_, v_x_4771_);
    return v_res_4774_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(
    mut v_x_4775_: *mut leanh::LeanObject,
    mut v_x_4776_: *mut leanh::LeanObject,
    mut v_x_4777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4778_: u64 = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = lean_string_hash(v_x_4776_);
    v___x_4779_ = lean_uint64_to_usize(v___x_4778_);
    v___x_4780_ = 1usize;
    v___x_4781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_4775_, v___x_4779_, v___x_4780_, v_x_4776_, v_x_4777_);
    return v___x_4781_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(
    mut v_mutex_4782_: *mut leanh::LeanObject,
    mut v_a_x3f_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = lean_io_basemutex_unlock(v_mutex_4782_);
    v___x_4786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4786_, 0, v___x_4785_);
    return v___x_4786_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(
    mut v_mutex_4787_: *mut leanh::LeanObject,
    mut v_a_x3f_4788_: *mut leanh::LeanObject,
    mut v___y_4789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_4787_, v_a_x3f_4788_);
    leanh::lean_dec(v_a_x3f_4788_);
    leanh::lean_dec(v_mutex_4787_);
    return v_res_4790_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(
    mut v_mutex_4791_: *mut leanh::LeanObject,
    mut v_k_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_unused_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4821_: u8 = 0;
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v_unused_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4795_ = leanh::lean_ctor_get(v_mutex_4791_, 0);
                leanh::lean_inc(v_ref_4795_);
                v_mutex_4796_ = leanh::lean_ctor_get(v_mutex_4791_, 1);
                leanh::lean_inc(v_mutex_4796_);
                leanh::lean_dec_ref(v_mutex_4791_);
                v___x_4797_ = lean_io_basemutex_lock(v_mutex_4796_);
                leanh::lean_inc_ref(v___y_4793_);
                v___x_4798_ = leanh::lean_apply_3(
                    v_k_4792_,
                    v_ref_4795_,
                    v___y_4793_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4798_) == 0 {
                    v_a_4799_ = leanh::lean_ctor_get(v___x_4798_, 0);
                    v_isSharedCheck_4815_ = (!leanh::lean_is_exclusive(v___x_4798_)) as u8;
                    if v_isSharedCheck_4815_ == 0 {
                        v___x_4801_ = v___x_4798_;
                        v_isShared_4802_ = v_isSharedCheck_4815_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4799_);
                        leanh::lean_dec(v___x_4798_);
                        v___x_4801_ = leanh::lean_box(0);
                        v_isShared_4802_ = v_isSharedCheck_4815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4816_ = leanh::lean_ctor_get(v___x_4798_, 0);
                    leanh::lean_inc(v_a_4816_);
                    leanh::lean_dec_ref_known(v___x_4798_, 1);
                    v___x_4817_ = leanh::lean_box(0);
                    v___x_4818_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_4796_, v___x_4817_);
                    leanh::lean_dec(v_mutex_4796_);
                    v_isSharedCheck_4825_ = (!leanh::lean_is_exclusive(v___x_4818_)) as u8;
                    if v_isSharedCheck_4825_ == 0 {
                        v_unused_4826_ = leanh::lean_ctor_get(v___x_4818_, 0);
                        leanh::lean_dec(v_unused_4826_);
                        v___x_4820_ = v___x_4818_;
                        v_isShared_4821_ = v_isSharedCheck_4825_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4818_);
                        v___x_4820_ = leanh::lean_box(0);
                        v_isShared_4821_ = v_isSharedCheck_4825_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_4799_);
                if v_isShared_4802_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4801_, 1);
                    v___x_4804_ = v___x_4801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4799_);
                    v___x_4804_ = v_reuseFailAlloc_4814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4805_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_4796_, v___x_4804_);
                leanh::lean_dec_ref(v___x_4804_);
                leanh::lean_dec(v_mutex_4796_);
                v_isSharedCheck_4812_ = (!leanh::lean_is_exclusive(v___x_4805_)) as u8;
                if v_isSharedCheck_4812_ == 0 {
                    v_unused_4813_ = leanh::lean_ctor_get(v___x_4805_, 0);
                    leanh::lean_dec(v_unused_4813_);
                    v___x_4807_ = v___x_4805_;
                    v_isShared_4808_ = v_isSharedCheck_4812_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4805_);
                    v___x_4807_ = leanh::lean_box(0);
                    v_isShared_4808_ = v_isSharedCheck_4812_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4808_ == 0 {
                    leanh::lean_ctor_set(v___x_4807_, 0, v_a_4799_);
                    v___x_4810_ = v___x_4807_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4799_);
                    v___x_4810_ = v_reuseFailAlloc_4811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4810_;
            }
            5 => {
                if v_isShared_4821_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4820_, 1);
                    leanh::lean_ctor_set(v___x_4820_, 0, v_a_4816_);
                    v___x_4823_ = v___x_4820_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4824_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4816_);
                    v___x_4823_ = v_reuseFailAlloc_4824_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(
    mut v_mutex_4827_: *mut leanh::LeanObject,
    mut v_k_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_4827_, v_k_4828_, v___y_4829_);
    leanh::lean_dec_ref(v___y_4829_);
    return v_res_4831_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(
    mut v_val_4832_: *mut leanh::LeanObject,
    mut v___f_4833_: *mut leanh::LeanObject,
    mut v_param_4834_: *mut leanh::LeanObject,
    mut v_x_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v_snd_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4838_ = lean_st_ref_get(v_val_4832_);
                leanh::lean_inc_ref(v___y_4836_);
                v___x_4839_ = leanh::lean_apply_4(
                    v___f_4833_,
                    v_param_4834_,
                    v___x_4838_,
                    v___y_4836_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4839_) == 0 {
                    v_a_4840_ = leanh::lean_ctor_get(v___x_4839_, 0);
                    v_isSharedCheck_4849_ = (!leanh::lean_is_exclusive(v___x_4839_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4842_ = v___x_4839_;
                        v_isShared_4843_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4840_);
                        leanh::lean_dec(v___x_4839_);
                        v___x_4842_ = leanh::lean_box(0);
                        v_isShared_4843_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4850_ = leanh::lean_ctor_get(v___x_4839_, 0);
                    v_isSharedCheck_4857_ = (!leanh::lean_is_exclusive(v___x_4839_)) as u8;
                    if v_isSharedCheck_4857_ == 0 {
                        v___x_4852_ = v___x_4839_;
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4850_);
                        leanh::lean_dec(v___x_4839_);
                        v___x_4852_ = leanh::lean_box(0);
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4844_ = leanh::lean_ctor_get(v_a_4840_, 1);
                leanh::lean_inc(v_snd_4844_);
                leanh::lean_dec(v_a_4840_);
                v___x_4845_ = lean_st_ref_set(v_val_4832_, v_snd_4844_);
                if v_isShared_4843_ == 0 {
                    leanh::lean_ctor_set(v___x_4842_, 0, v___x_4845_);
                    v___x_4847_ = v___x_4842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4847_;
            }
            3 => {
                if v_isShared_4853_ == 0 {
                    v___x_4855_ = v___x_4852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
                    v___x_4855_ = v_reuseFailAlloc_4856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(
    mut v_val_4858_: *mut leanh::LeanObject,
    mut v___f_4859_: *mut leanh::LeanObject,
    mut v_param_4860_: *mut leanh::LeanObject,
    mut v_x_4861_: *mut leanh::LeanObject,
    mut v___y_4862_: *mut leanh::LeanObject,
    mut v___y_4863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4864_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_4858_, v___f_4859_, v_param_4860_, v_x_4861_, v___y_4862_);
    leanh::lean_dec_ref(v___y_4862_);
    leanh::lean_dec(v_val_4858_);
    return v_res_4864_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(
    mut v___f_4865_: *mut leanh::LeanObject,
    mut v___f_4866_: *mut leanh::LeanObject,
    mut v___y_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut v_a_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4885_: u8 = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4870_ = lean_st_ref_get(v___y_4867_);
                v___x_4871_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(
                    v___x_4870_,
                    v___f_4865_,
                    v___y_4868_,
                );
                if leanh::lean_obj_tag(v___x_4871_) == 0 {
                    v_a_4872_ = leanh::lean_ctor_get(v___x_4871_, 0);
                    v_isSharedCheck_4881_ = (!leanh::lean_is_exclusive(v___x_4871_)) as u8;
                    if v_isSharedCheck_4881_ == 0 {
                        v___x_4874_ = v___x_4871_;
                        v_isShared_4875_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4872_);
                        leanh::lean_dec(v___x_4871_);
                        v___x_4874_ = leanh::lean_box(0);
                        v_isShared_4875_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_4866_);
                    v_a_4882_ = leanh::lean_ctor_get(v___x_4871_, 0);
                    v_isSharedCheck_4889_ = (!leanh::lean_is_exclusive(v___x_4871_)) as u8;
                    if v_isSharedCheck_4889_ == 0 {
                        v___x_4884_ = v___x_4871_;
                        v_isShared_4885_ = v_isSharedCheck_4889_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4882_);
                        leanh::lean_dec(v___x_4871_);
                        v___x_4884_ = leanh::lean_box(0);
                        v_isShared_4885_ = v_isSharedCheck_4889_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4876_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4866_, v_a_4872_);
                v___x_4877_ = lean_st_ref_set(v___y_4867_, v___x_4876_);
                if v_isShared_4875_ == 0 {
                    leanh::lean_ctor_set(v___x_4874_, 0, v___x_4877_);
                    v___x_4879_ = v___x_4874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4880_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
                    v___x_4879_ = v_reuseFailAlloc_4880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4879_;
            }
            3 => {
                if v_isShared_4885_ == 0 {
                    v___x_4887_ = v___x_4884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4888_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
                    v___x_4887_ = v_reuseFailAlloc_4888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(
    mut v___f_4890_: *mut leanh::LeanObject,
    mut v___f_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4895_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_4890_, v___f_4891_, v___y_4892_, v___y_4893_);
    leanh::lean_dec_ref(v___y_4893_);
    leanh::lean_dec(v___y_4892_);
    return v_res_4895_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(
    mut v_val_4896_: *mut leanh::LeanObject,
    mut v___f_4897_: *mut leanh::LeanObject,
    mut v___f_4898_: *mut leanh::LeanObject,
    mut v_val_4899_: *mut leanh::LeanObject,
    mut v_param_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4903_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___f_4903_, 0, v_val_4896_);
    leanh::lean_closure_set(v___f_4903_, 1, v___f_4897_);
    leanh::lean_closure_set(v___f_4903_, 2, v_param_4900_);
    v___f_4904_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed as *mut core::ffi::c_void, 5, 2);
    leanh::lean_closure_set(v___f_4904_, 0, v___f_4903_);
    leanh::lean_closure_set(v___f_4904_, 1, v___f_4898_);
    v___x_4905_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_4899_, v___f_4904_, v___y_4901_);
    return v___x_4905_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(
    mut v_val_4906_: *mut leanh::LeanObject,
    mut v___f_4907_: *mut leanh::LeanObject,
    mut v___f_4908_: *mut leanh::LeanObject,
    mut v_val_4909_: *mut leanh::LeanObject,
    mut v_param_4910_: *mut leanh::LeanObject,
    mut v___y_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_4906_, v___f_4907_, v___f_4908_, v_val_4909_, v_param_4910_, v___y_4911_);
    leanh::lean_dec_ref(v___y_4911_);
    return v_res_4913_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(
    mut v___x_4914_: *mut leanh::LeanObject,
    mut v_x_4915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    return v___x_4914_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(
    mut v___x_4916_: *mut leanh::LeanObject,
    mut v_x_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(v___x_4916_, v_x_4917_);
    leanh::lean_dec_ref(v_x_4917_);
    return v_res_4918_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(
    mut v_params_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4926_: u8 = 0;
    let mut v___x_4927_: u8 = 0;
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_params_4921_);
                v___x_4922_ = l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(v_params_4921_);
                if leanh::lean_obj_tag(v___x_4922_) == 0 {
                    v_a_4923_ = leanh::lean_ctor_get(v___x_4922_, 0);
                    v_isSharedCheck_4938_ = (!leanh::lean_is_exclusive(v___x_4922_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4925_ = v___x_4922_;
                        v_isShared_4926_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4923_);
                        leanh::lean_dec(v___x_4922_);
                        v___x_4925_ = leanh::lean_box(0);
                        v_isShared_4926_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_params_4921_);
                    v_a_4939_ = leanh::lean_ctor_get(v___x_4922_, 0);
                    v_isSharedCheck_4946_ = (!leanh::lean_is_exclusive(v___x_4922_)) as u8;
                    if v_isSharedCheck_4946_ == 0 {
                        v___x_4941_ = v___x_4922_;
                        v_isShared_4942_ = v_isSharedCheck_4946_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4939_);
                        leanh::lean_dec(v___x_4922_);
                        v___x_4941_ = leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4946_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4927_ = 3;
                v___x_4928_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0;
                v___x_4929_ = l_Lean_Json_compress(v_params_4921_);
                v___x_4930_ = lean_string_append(v___x_4928_, v___x_4929_);
                leanh::lean_dec_ref(v___x_4929_);
                v___x_4931_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1;
                v___x_4932_ = lean_string_append(v___x_4930_, v___x_4931_);
                v___x_4933_ = lean_string_append(v___x_4932_, v_a_4923_);
                leanh::lean_dec(v_a_4923_);
                v___x_4934_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4934_, 0, v___x_4933_);
                leanh::lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4927_,
                );
                if v_isShared_4926_ == 0 {
                    leanh::lean_ctor_set(v___x_4925_, 0, v___x_4934_);
                    v___x_4936_ = v___x_4925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4936_;
            }
            3 => {
                if v_isShared_4942_ == 0 {
                    v___x_4944_ = v___x_4941_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
                    v___x_4944_ = v_reuseFailAlloc_4945_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(
    mut v_j_4947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v_a_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4960_: u8 = 0;
    let mut v_textDocument_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4948_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_j_4947_);
                if leanh::lean_obj_tag(v___x_4948_) == 0 {
                    v_a_4949_ = leanh::lean_ctor_get(v___x_4948_, 0);
                    v_isSharedCheck_4956_ = (!leanh::lean_is_exclusive(v___x_4948_)) as u8;
                    if v_isSharedCheck_4956_ == 0 {
                        v___x_4951_ = v___x_4948_;
                        v_isShared_4952_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4949_);
                        leanh::lean_dec(v___x_4948_);
                        v___x_4951_ = leanh::lean_box(0);
                        v_isShared_4952_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4957_ = leanh::lean_ctor_get(v___x_4948_, 0);
                    v_isSharedCheck_4965_ = (!leanh::lean_is_exclusive(v___x_4948_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v___x_4959_ = v___x_4948_;
                        v_isShared_4960_ = v_isSharedCheck_4965_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4957_);
                        leanh::lean_dec(v___x_4948_);
                        v___x_4959_ = leanh::lean_box(0);
                        v_isShared_4960_ = v_isSharedCheck_4965_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4952_ == 0 {
                    v___x_4954_ = v___x_4951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4954_;
            }
            3 => {
                v_textDocument_4961_ = leanh::lean_ctor_get(v_a_4957_, 1);
                leanh::lean_inc_ref(v_textDocument_4961_);
                leanh::lean_dec(v_a_4957_);
                if v_isShared_4960_ == 0 {
                    leanh::lean_ctor_set(v___x_4959_, 0, v_textDocument_4961_);
                    v___x_4963_ = v___x_4959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_textDocument_4961_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(
    mut v_method_4966_: *mut leanh::LeanObject,
    mut v_inst_4967_: *mut leanh::LeanObject,
    mut v_onDidChange_4968_: *mut leanh::LeanObject,
    mut v_param_4969_: *mut leanh::LeanObject,
    mut v___y_4970_: *mut leanh::LeanObject,
    mut v___y_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_snd_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4983_: u8 = 0;
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_unused_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut v_a_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut v_a_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4973_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(
                    v_method_4966_,
                    v___y_4970_,
                    leanh::lean_box(0),
                    v_inst_4967_,
                    v___y_4971_,
                );
                if leanh::lean_obj_tag(v___x_4973_) == 0 {
                    v_a_4974_ = leanh::lean_ctor_get(v___x_4973_, 0);
                    leanh::lean_inc(v_a_4974_);
                    leanh::lean_dec_ref_known(v___x_4973_, 1);
                    leanh::lean_inc_ref(v___y_4971_);
                    v___x_4975_ = leanh::lean_apply_4(
                        v_onDidChange_4968_,
                        v_param_4969_,
                        v_a_4974_,
                        v___y_4971_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4975_) == 0 {
                        v_a_4976_ = leanh::lean_ctor_get(v___x_4975_, 0);
                        v_isSharedCheck_4994_ =
                            (!leanh::lean_is_exclusive(v___x_4975_)) as u8;
                        if v_isSharedCheck_4994_ == 0 {
                            v___x_4978_ = v___x_4975_;
                            v_isShared_4979_ = v_isSharedCheck_4994_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4976_);
                            leanh::lean_dec(v___x_4975_);
                            v___x_4978_ = leanh::lean_box(0);
                            v_isShared_4979_ = v_isSharedCheck_4994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_inst_4967_);
                        v_a_4995_ = leanh::lean_ctor_get(v___x_4975_, 0);
                        v_isSharedCheck_5002_ =
                            (!leanh::lean_is_exclusive(v___x_4975_)) as u8;
                        if v_isSharedCheck_5002_ == 0 {
                            v___x_4997_ = v___x_4975_;
                            v_isShared_4998_ = v_isSharedCheck_5002_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4995_);
                            leanh::lean_dec(v___x_4975_);
                            v___x_4997_ = leanh::lean_box(0);
                            v_isShared_4998_ = v_isSharedCheck_5002_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_param_4969_);
                    leanh::lean_dec_ref(v_onDidChange_4968_);
                    leanh::lean_dec(v_inst_4967_);
                    v_a_5003_ = leanh::lean_ctor_get(v___x_4973_, 0);
                    v_isSharedCheck_5010_ = (!leanh::lean_is_exclusive(v___x_4973_)) as u8;
                    if v_isSharedCheck_5010_ == 0 {
                        v___x_5005_ = v___x_4973_;
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5003_);
                        leanh::lean_dec(v___x_4973_);
                        v___x_5005_ = leanh::lean_box(0);
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4980_ = leanh::lean_ctor_get(v_a_4976_, 1);
                v_isSharedCheck_4992_ = (!leanh::lean_is_exclusive(v_a_4976_)) as u8;
                if v_isSharedCheck_4992_ == 0 {
                    v_unused_4993_ = leanh::lean_ctor_get(v_a_4976_, 0);
                    leanh::lean_dec(v_unused_4993_);
                    v___x_4982_ = v_a_4976_;
                    v_isShared_4983_ = v_isSharedCheck_4992_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4980_);
                    leanh::lean_dec(v_a_4976_);
                    v___x_4982_ = leanh::lean_box(0);
                    v_isShared_4983_ = v_isSharedCheck_4992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4983_ == 0 {
                    leanh::lean_ctor_set(v___x_4982_, 0, v_inst_4967_);
                    v___x_4985_ = v___x_4982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_inst_4967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_snd_4980_);
                    v___x_4985_ = v_reuseFailAlloc_4991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4986_ = leanh::lean_box(0);
                v___x_4987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4987_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_4987_, 1, v___x_4985_);
                if v_isShared_4979_ == 0 {
                    leanh::lean_ctor_set(v___x_4978_, 0, v___x_4987_);
                    v___x_4989_ = v___x_4978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
                    v___x_4989_ = v_reuseFailAlloc_4990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4989_;
            }
            5 => {
                if v_isShared_4998_ == 0 {
                    v___x_5000_ = v___x_4997_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5000_;
            }
            7 => {
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(
    mut v_method_5011_: *mut leanh::LeanObject,
    mut v_inst_5012_: *mut leanh::LeanObject,
    mut v_onDidChange_5013_: *mut leanh::LeanObject,
    mut v_param_5014_: *mut leanh::LeanObject,
    mut v___y_5015_: *mut leanh::LeanObject,
    mut v___y_5016_: *mut leanh::LeanObject,
    mut v___y_5017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_5011_, v_inst_5012_, v_onDidChange_5013_, v_param_5014_, v___y_5015_, v___y_5016_);
    leanh::lean_dec_ref(v___y_5016_);
    leanh::lean_dec(v___y_5015_);
    leanh::lean_dec_ref(v_method_5011_);
    return v_res_5018_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_params_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5025_: u8 = 0;
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut v_a_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5033_: u8 = 0;
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5021_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_params_5019_);
                if leanh::lean_obj_tag(v___x_5021_) == 0 {
                    v_a_5022_ = leanh::lean_ctor_get(v___x_5021_, 0);
                    v_isSharedCheck_5029_ = (!leanh::lean_is_exclusive(v___x_5021_)) as u8;
                    if v_isSharedCheck_5029_ == 0 {
                        v___x_5024_ = v___x_5021_;
                        v_isShared_5025_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5022_);
                        leanh::lean_dec(v___x_5021_);
                        v___x_5024_ = leanh::lean_box(0);
                        v_isShared_5025_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5030_ = leanh::lean_ctor_get(v___x_5021_, 0);
                    v_isSharedCheck_5037_ = (!leanh::lean_is_exclusive(v___x_5021_)) as u8;
                    if v_isSharedCheck_5037_ == 0 {
                        v___x_5032_ = v___x_5021_;
                        v_isShared_5033_ = v_isSharedCheck_5037_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5030_);
                        leanh::lean_dec(v___x_5021_);
                        v___x_5032_ = leanh::lean_box(0);
                        v_isShared_5033_ = v_isSharedCheck_5037_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5025_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5024_, 1);
                    v___x_5027_ = v___x_5024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
                    v___x_5027_ = v_reuseFailAlloc_5028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5027_;
            }
            3 => {
                if v_isShared_5033_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5032_, 0);
                    v___x_5035_ = v___x_5032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
                    v___x_5035_ = v_reuseFailAlloc_5036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_params_5038_: *mut leanh::LeanObject,
    mut v_a_5039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5040_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_5038_);
    return v_res_5040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(
    mut v_sz_5041_: usize,
    mut v_i_5042_: usize,
    mut v_bs_5043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5044_: u8 = 0;
    let mut v_v_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: usize = 0;
    let mut v___x_5050_: usize = 0;
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5044_ = lean_usize_dec_lt(v_i_5042_, v_sz_5041_);
                if v___x_5044_ == 0 {
                    return v_bs_5043_;
                } else {
                    v_v_5045_ = lean_array_uget(v_bs_5043_, v_i_5042_);
                    v___x_5046_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5047_ = lean_array_uset(v_bs_5043_, v_i_5042_, v___x_5046_);
                    v___x_5048_ = l_Lean_Lsp_instToJsonInlayHint_toJson(v_v_5045_);
                    v___x_5049_ = 1usize;
                    v___x_5050_ = lean_usize_add(v_i_5042_, v___x_5049_);
                    v___x_5051_ = lean_array_uset(v_bs_x27_5047_, v_i_5042_, v___x_5048_);
                    v_i_5042_ = v___x_5050_;
                    v_bs_5043_ = v___x_5051_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(
    mut v_sz_5053_: *mut leanh::LeanObject,
    mut v_i_5054_: *mut leanh::LeanObject,
    mut v_bs_5055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5056_: usize = 0;
    let mut v_i_boxed_5057_: usize = 0;
    let mut v_res_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5056_ = leanh::lean_unbox_usize(v_sz_5053_);
    leanh::lean_dec(v_sz_5053_);
    v_i_boxed_5057_ = leanh::lean_unbox_usize(v_i_5054_);
    leanh::lean_dec(v_i_5054_);
    v_res_5058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_boxed_5056_, v_i_boxed_5057_, v_bs_5055_);
    return v_res_5058_;
}
pub unsafe fn l_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(
    mut v_a_5059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_5060_: usize = 0;
    let mut v___x_5061_: usize = 0;
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_5060_ = lean_array_size(v_a_5059_);
    v___x_5061_ = 0usize;
    v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_5060_, v___x_5061_, v_a_5059_);
    v___x_5063_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5063_, 0, v___x_5062_);
    return v___x_5063_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(
    mut v_method_5064_: *mut leanh::LeanObject,
    mut v_inst_5065_: *mut leanh::LeanObject,
    mut v_handler_5066_: *mut leanh::LeanObject,
    mut v_param_5067_: *mut leanh::LeanObject,
    mut v_state_5068_: *mut leanh::LeanObject,
    mut v___y_5069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5079_: u8 = 0;
    let mut v_fst_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v_response_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isComplete_5086_: u8 = 0;
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v_a_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_a_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5115_: u8 = 0;
    let mut v_a_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5119_: u8 = 0;
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5071_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_param_5067_);
                if leanh::lean_obj_tag(v___x_5071_) == 0 {
                    v_a_5072_ = leanh::lean_ctor_get(v___x_5071_, 0);
                    leanh::lean_inc(v_a_5072_);
                    leanh::lean_dec_ref_known(v___x_5071_, 1);
                    v___x_5073_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(
                        v_method_5064_,
                        v_state_5068_,
                        leanh::lean_box(0),
                        v_inst_5065_,
                        v___y_5069_,
                    );
                    if leanh::lean_obj_tag(v___x_5073_) == 0 {
                        v_a_5074_ = leanh::lean_ctor_get(v___x_5073_, 0);
                        leanh::lean_inc(v_a_5074_);
                        leanh::lean_dec_ref_known(v___x_5073_, 1);
                        leanh::lean_inc_ref(v___y_5069_);
                        v___x_5075_ = leanh::lean_apply_4(
                            v_handler_5066_,
                            v_a_5072_,
                            v_a_5074_,
                            v___y_5069_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_5075_) == 0 {
                            v_a_5076_ = leanh::lean_ctor_get(v___x_5075_, 0);
                            v_isSharedCheck_5099_ =
                                (!leanh::lean_is_exclusive(v___x_5075_)) as u8;
                            if v_isSharedCheck_5099_ == 0 {
                                v___x_5078_ = v___x_5075_;
                                v_isShared_5079_ = v_isSharedCheck_5099_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5076_);
                                leanh::lean_dec(v___x_5075_);
                                v___x_5078_ = leanh::lean_box(0);
                                v_isShared_5079_ = v_isSharedCheck_5099_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_inst_5065_);
                            v_a_5100_ = leanh::lean_ctor_get(v___x_5075_, 0);
                            v_isSharedCheck_5107_ =
                                (!leanh::lean_is_exclusive(v___x_5075_)) as u8;
                            if v_isSharedCheck_5107_ == 0 {
                                v___x_5102_ = v___x_5075_;
                                v_isShared_5103_ = v_isSharedCheck_5107_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5100_);
                                leanh::lean_dec(v___x_5075_);
                                v___x_5102_ = leanh::lean_box(0);
                                v_isShared_5103_ = v_isSharedCheck_5107_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5072_);
                        leanh::lean_dec_ref(v_handler_5066_);
                        leanh::lean_dec(v_inst_5065_);
                        v_a_5108_ = leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5115_ =
                            (!leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5115_ == 0 {
                            v___x_5110_ = v___x_5073_;
                            v_isShared_5111_ = v_isSharedCheck_5115_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5108_);
                            leanh::lean_dec(v___x_5073_);
                            v___x_5110_ = leanh::lean_box(0);
                            v_isShared_5111_ = v_isSharedCheck_5115_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_handler_5066_);
                    leanh::lean_dec(v_inst_5065_);
                    v_a_5116_ = leanh::lean_ctor_get(v___x_5071_, 0);
                    v_isSharedCheck_5123_ = (!leanh::lean_is_exclusive(v___x_5071_)) as u8;
                    if v_isSharedCheck_5123_ == 0 {
                        v___x_5118_ = v___x_5071_;
                        v_isShared_5119_ = v_isSharedCheck_5123_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5116_);
                        leanh::lean_dec(v___x_5071_);
                        v___x_5118_ = leanh::lean_box(0);
                        v_isShared_5119_ = v_isSharedCheck_5123_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5080_ = leanh::lean_ctor_get(v_a_5076_, 0);
                v_snd_5081_ = leanh::lean_ctor_get(v_a_5076_, 1);
                v_isSharedCheck_5098_ = (!leanh::lean_is_exclusive(v_a_5076_)) as u8;
                if v_isSharedCheck_5098_ == 0 {
                    v___x_5083_ = v_a_5076_;
                    v_isShared_5084_ = v_isSharedCheck_5098_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5081_);
                    leanh::lean_inc(v_fst_5080_);
                    leanh::lean_dec(v_a_5076_);
                    v___x_5083_ = leanh::lean_box(0);
                    v_isShared_5084_ = v_isSharedCheck_5098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_response_5085_ = leanh::lean_ctor_get(v_fst_5080_, 0);
                leanh::lean_inc(v_response_5085_);
                v_isComplete_5086_ = leanh::lean_ctor_get_uint8(
                    v_fst_5080_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec(v_fst_5080_);
                v___x_5087_ = l_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_response_5085_);
                leanh::lean_inc(v___x_5087_);
                v___x_5088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5088_, 0, v___x_5087_);
                v___x_5089_ = l_Lean_Json_compress(v___x_5087_);
                v___x_5090_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5090_, 0, v___x_5088_);
                leanh::lean_ctor_set(v___x_5090_, 1, v___x_5089_);
                leanh::lean_ctor_set_uint8(
                    v___x_5090_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_isComplete_5086_,
                );
                if v_isShared_5084_ == 0 {
                    leanh::lean_ctor_set(v___x_5083_, 0, v_inst_5065_);
                    v___x_5092_ = v___x_5083_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_inst_5065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 1, v_snd_5081_);
                    v___x_5092_ = v_reuseFailAlloc_5097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5093_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5093_, 0, v___x_5090_);
                leanh::lean_ctor_set(v___x_5093_, 1, v___x_5092_);
                if v_isShared_5079_ == 0 {
                    leanh::lean_ctor_set(v___x_5078_, 0, v___x_5093_);
                    v___x_5095_ = v___x_5078_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
                    v___x_5095_ = v_reuseFailAlloc_5096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5095_;
            }
            5 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5105_;
            }
            7 => {
                if v_isShared_5111_ == 0 {
                    v___x_5113_ = v___x_5110_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
                    v___x_5113_ = v_reuseFailAlloc_5114_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5113_;
            }
            9 => {
                if v_isShared_5119_ == 0 {
                    v___x_5121_ = v___x_5118_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
                    v___x_5121_ = v_reuseFailAlloc_5122_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(
    mut v_method_5124_: *mut leanh::LeanObject,
    mut v_inst_5125_: *mut leanh::LeanObject,
    mut v_handler_5126_: *mut leanh::LeanObject,
    mut v_param_5127_: *mut leanh::LeanObject,
    mut v_state_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
    mut v___y_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5131_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_5124_, v_inst_5125_, v_handler_5126_, v_param_5127_, v_state_5128_, v___y_5129_);
    leanh::lean_dec_ref(v___y_5129_);
    leanh::lean_dec(v_state_5128_);
    leanh::lean_dec_ref(v_method_5124_);
    return v_res_5131_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(
    mut v___f_5132_: *mut leanh::LeanObject,
    mut v___f_5133_: *mut leanh::LeanObject,
    mut v___y_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5137_ = lean_st_ref_get(v___y_5134_);
                v___x_5138_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(
                    v___x_5137_,
                    v___f_5132_,
                    v___y_5135_,
                );
                if leanh::lean_obj_tag(v___x_5138_) == 0 {
                    v_a_5139_ = leanh::lean_ctor_get(v___x_5138_, 0);
                    v_isSharedCheck_5148_ = (!leanh::lean_is_exclusive(v___x_5138_)) as u8;
                    if v_isSharedCheck_5148_ == 0 {
                        v___x_5141_ = v___x_5138_;
                        v_isShared_5142_ = v_isSharedCheck_5148_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5139_);
                        leanh::lean_dec(v___x_5138_);
                        v___x_5141_ = leanh::lean_box(0);
                        v_isShared_5142_ = v_isSharedCheck_5148_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_5133_);
                    return v___x_5138_;
                }
            }
            1 => {
                leanh::lean_inc(v_a_5139_);
                v___x_5143_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5133_, v_a_5139_);
                v___x_5144_ = lean_st_ref_set(v___y_5134_, v___x_5143_);
                if v_isShared_5142_ == 0 {
                    v___x_5146_ = v___x_5141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5139_);
                    v___x_5146_ = v_reuseFailAlloc_5147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(
    mut v___f_5149_: *mut leanh::LeanObject,
    mut v___f_5150_: *mut leanh::LeanObject,
    mut v___y_5151_: *mut leanh::LeanObject,
    mut v___y_5152_: *mut leanh::LeanObject,
    mut v___y_5153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5154_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_5149_, v___f_5150_, v___y_5151_, v___y_5152_);
    leanh::lean_dec_ref(v___y_5152_);
    leanh::lean_dec(v___y_5151_);
    return v_res_5154_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(
    mut v_val_5155_: *mut leanh::LeanObject,
    mut v___f_5156_: *mut leanh::LeanObject,
    mut v_param_5157_: *mut leanh::LeanObject,
    mut v_x_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v_fst_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_a_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5177_: u8 = 0;
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5161_ = lean_st_ref_get(v_val_5155_);
                leanh::lean_inc_ref(v___y_5159_);
                v___x_5162_ = leanh::lean_apply_4(
                    v___f_5156_,
                    v_param_5157_,
                    v___x_5161_,
                    v___y_5159_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5162_) == 0 {
                    v_a_5163_ = leanh::lean_ctor_get(v___x_5162_, 0);
                    v_isSharedCheck_5173_ = (!leanh::lean_is_exclusive(v___x_5162_)) as u8;
                    if v_isSharedCheck_5173_ == 0 {
                        v___x_5165_ = v___x_5162_;
                        v_isShared_5166_ = v_isSharedCheck_5173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5163_);
                        leanh::lean_dec(v___x_5162_);
                        v___x_5165_ = leanh::lean_box(0);
                        v_isShared_5166_ = v_isSharedCheck_5173_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5174_ = leanh::lean_ctor_get(v___x_5162_, 0);
                    v_isSharedCheck_5181_ = (!leanh::lean_is_exclusive(v___x_5162_)) as u8;
                    if v_isSharedCheck_5181_ == 0 {
                        v___x_5176_ = v___x_5162_;
                        v_isShared_5177_ = v_isSharedCheck_5181_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5174_);
                        leanh::lean_dec(v___x_5162_);
                        v___x_5176_ = leanh::lean_box(0);
                        v_isShared_5177_ = v_isSharedCheck_5181_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5167_ = leanh::lean_ctor_get(v_a_5163_, 0);
                leanh::lean_inc(v_fst_5167_);
                v_snd_5168_ = leanh::lean_ctor_get(v_a_5163_, 1);
                leanh::lean_inc(v_snd_5168_);
                leanh::lean_dec(v_a_5163_);
                v___x_5169_ = lean_st_ref_set(v_val_5155_, v_snd_5168_);
                if v_isShared_5166_ == 0 {
                    leanh::lean_ctor_set(v___x_5165_, 0, v_fst_5167_);
                    v___x_5171_ = v___x_5165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_fst_5167_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5171_;
            }
            3 => {
                if v_isShared_5177_ == 0 {
                    v___x_5179_ = v___x_5176_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
                    v___x_5179_ = v_reuseFailAlloc_5180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(
    mut v_val_5182_: *mut leanh::LeanObject,
    mut v___f_5183_: *mut leanh::LeanObject,
    mut v_param_5184_: *mut leanh::LeanObject,
    mut v_x_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5188_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_5182_, v___f_5183_, v_param_5184_, v_x_5185_, v___y_5186_);
    leanh::lean_dec_ref(v___y_5186_);
    leanh::lean_dec(v_val_5182_);
    return v_res_5188_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(
    mut v_val_5189_: *mut leanh::LeanObject,
    mut v___f_5190_: *mut leanh::LeanObject,
    mut v___f_5191_: *mut leanh::LeanObject,
    mut v_val_5192_: *mut leanh::LeanObject,
    mut v_param_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5196_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___f_5196_, 0, v_val_5189_);
    leanh::lean_closure_set(v___f_5196_, 1, v___f_5190_);
    leanh::lean_closure_set(v___f_5196_, 2, v_param_5193_);
    v___f_5197_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed as *mut core::ffi::c_void, 5, 2);
    leanh::lean_closure_set(v___f_5197_, 0, v___f_5196_);
    leanh::lean_closure_set(v___f_5197_, 1, v___f_5191_);
    v___x_5198_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_5192_, v___f_5197_, v___y_5194_);
    return v___x_5198_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(
    mut v_val_5199_: *mut leanh::LeanObject,
    mut v___f_5200_: *mut leanh::LeanObject,
    mut v___f_5201_: *mut leanh::LeanObject,
    mut v_val_5202_: *mut leanh::LeanObject,
    mut v_param_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5206_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_5199_, v___f_5200_, v___f_5201_, v_val_5202_, v_param_5203_, v___y_5204_);
    leanh::lean_dec_ref(v___y_5204_);
    return v_res_5206_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5209_ = leanh::lean_box(0);
    v___x_5210_ = lean_task_pure(v___x_5209_);
    return v___x_5210_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_method_5216_: *mut leanh::LeanObject,
    mut v_completeness_5217_: *mut leanh::LeanObject,
    mut v_inst_5218_: *mut leanh::LeanObject,
    mut v_initState_5219_: *mut leanh::LeanObject,
    mut v_handler_5220_: *mut leanh::LeanObject,
    mut v_onDidChange_5221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___x_5228_: u8 = 0;
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5256_: u8 = 0;
    let mut v_a_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = l_Lean_initializing();
                if leanh::lean_obj_tag(v___x_5223_) == 0 {
                    v_a_5224_ = leanh::lean_ctor_get(v___x_5223_, 0);
                    v_isSharedCheck_5256_ = (!leanh::lean_is_exclusive(v___x_5223_)) as u8;
                    if v_isSharedCheck_5256_ == 0 {
                        v___x_5226_ = v___x_5223_;
                        v_isShared_5227_ = v_isSharedCheck_5256_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5224_);
                        leanh::lean_dec(v___x_5223_);
                        v___x_5226_ = leanh::lean_box(0);
                        v_isShared_5227_ = v_isSharedCheck_5256_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_onDidChange_5221_);
                    leanh::lean_dec_ref(v_handler_5220_);
                    leanh::lean_dec(v_initState_5219_);
                    leanh::lean_dec(v_inst_5218_);
                    leanh::lean_dec(v_completeness_5217_);
                    leanh::lean_dec_ref(v_method_5216_);
                    v_a_5257_ = leanh::lean_ctor_get(v___x_5223_, 0);
                    v_isSharedCheck_5264_ = (!leanh::lean_is_exclusive(v___x_5223_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5259_ = v___x_5223_;
                        v_isShared_5260_ = v_isSharedCheck_5264_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5257_);
                        leanh::lean_dec(v___x_5223_);
                        v___x_5259_ = leanh::lean_box(0);
                        v_isShared_5260_ = v_isSharedCheck_5264_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5228_ = (leanh::lean_unbox(v_a_5224_) as u8);
                leanh::lean_dec(v_a_5224_);
                if v___x_5228_ == 0 {
                    leanh::lean_dec_ref(v_onDidChange_5221_);
                    leanh::lean_dec_ref(v_handler_5220_);
                    leanh::lean_dec(v_initState_5219_);
                    leanh::lean_dec(v_inst_5218_);
                    leanh::lean_dec(v_completeness_5217_);
                    v___x_5229_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
                    v___x_5230_ = lean_string_append(v___x_5229_, v_method_5216_);
                    leanh::lean_dec_ref(v_method_5216_);
                    v___x_5231_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1;
                    v___x_5232_ = lean_string_append(v___x_5230_, v___x_5231_);
                    v___x_5233_ = lean_mk_io_user_error(v___x_5232_);
                    if v_isShared_5227_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5226_, 1);
                        leanh::lean_ctor_set(v___x_5226_, 0, v___x_5233_);
                        v___x_5235_ = v___x_5226_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5233_);
                        v___x_5235_ = v_reuseFailAlloc_5236_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5237_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_5238_ = l_Std_Mutex_new___redArg(v___x_5237_);
                    leanh::lean_inc_n(v_inst_5218_, 2);
                    v___x_5239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5239_, 0, v_inst_5218_);
                    leanh::lean_ctor_set(v___x_5239_, 1, v_initState_5219_);
                    leanh::lean_inc_ref(v___x_5239_);
                    v___x_5240_ = lean_st_mk_ref(v___x_5239_);
                    v___x_5241_ = l_Lean_Server_statefulRequestHandlers;
                    v___x_5242_ = lean_st_ref_take(v___x_5241_);
                    v___f_5243_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3;
                    leanh::lean_inc_ref_n(v_method_5216_, 2);
                    v___f_5244_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 3);
                    leanh::lean_closure_set(v___f_5244_, 0, v_method_5216_);
                    leanh::lean_closure_set(v___f_5244_, 1, v_inst_5218_);
                    leanh::lean_closure_set(v___f_5244_, 2, v_handler_5220_);
                    v___f_5245_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed as *mut core::ffi::c_void, 7, 3);
                    leanh::lean_closure_set(v___f_5245_, 0, v_method_5216_);
                    leanh::lean_closure_set(v___f_5245_, 1, v_inst_5218_);
                    leanh::lean_closure_set(v___f_5245_, 2, v_onDidChange_5221_);
                    v___f_5246_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4;
                    v___f_5247_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5;
                    leanh::lean_inc_ref_n(v___x_5238_, 2);
                    leanh::lean_inc_ref(v___f_5244_);
                    leanh::lean_inc_n(v___x_5240_, 2);
                    v___f_5248_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed as *mut core::ffi::c_void, 7, 4);
                    leanh::lean_closure_set(v___f_5248_, 0, v___x_5240_);
                    leanh::lean_closure_set(v___f_5248_, 1, v___f_5244_);
                    leanh::lean_closure_set(v___f_5248_, 2, v___f_5246_);
                    leanh::lean_closure_set(v___f_5248_, 3, v___x_5238_);
                    leanh::lean_inc_ref(v___f_5245_);
                    v___f_5249_ = leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed as *mut core::ffi::c_void, 7, 4);
                    leanh::lean_closure_set(v___f_5249_, 0, v___x_5240_);
                    leanh::lean_closure_set(v___f_5249_, 1, v___f_5245_);
                    leanh::lean_closure_set(v___f_5249_, 2, v___f_5247_);
                    leanh::lean_closure_set(v___f_5249_, 3, v___x_5238_);
                    v___x_5250_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v___x_5250_, 0, v___f_5243_);
                    leanh::lean_ctor_set(v___x_5250_, 1, v___f_5244_);
                    leanh::lean_ctor_set(v___x_5250_, 2, v___f_5248_);
                    leanh::lean_ctor_set(v___x_5250_, 3, v___f_5245_);
                    leanh::lean_ctor_set(v___x_5250_, 4, v___f_5249_);
                    leanh::lean_ctor_set(v___x_5250_, 5, v___x_5238_);
                    leanh::lean_ctor_set(v___x_5250_, 6, v___x_5239_);
                    leanh::lean_ctor_set(v___x_5250_, 7, v___x_5240_);
                    leanh::lean_ctor_set(v___x_5250_, 8, v_completeness_5217_);
                    v___x_5251_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_5242_, v_method_5216_, v___x_5250_);
                    v___x_5252_ = lean_st_ref_set(v___x_5241_, v___x_5251_);
                    if v_isShared_5227_ == 0 {
                        leanh::lean_ctor_set(v___x_5226_, 0, v___x_5252_);
                        v___x_5254_ = v___x_5226_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5255_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5252_);
                        v___x_5254_ = v_reuseFailAlloc_5255_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5235_;
            }
            3 => {
                return v___x_5254_;
            }
            4 => {
                if v_isShared_5260_ == 0 {
                    v___x_5262_ = v___x_5259_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(
    mut v_method_5265_: *mut leanh::LeanObject,
    mut v_completeness_5266_: *mut leanh::LeanObject,
    mut v_inst_5267_: *mut leanh::LeanObject,
    mut v_initState_5268_: *mut leanh::LeanObject,
    mut v_handler_5269_: *mut leanh::LeanObject,
    mut v_onDidChange_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_5265_, v_completeness_5266_, v_inst_5267_, v_initState_5268_, v_handler_5269_, v_onDidChange_5270_);
    return v_res_5272_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_keys_5273_: *mut leanh::LeanObject,
    mut v_i_5274_: *mut leanh::LeanObject,
    mut v_k_5275_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    let mut v_k_x27_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5276_ = lean_array_get_size(v_keys_5273_);
                v___x_5277_ = lean_nat_dec_lt(v_i_5274_, v___x_5276_);
                if v___x_5277_ == 0 {
                    leanh::lean_dec(v_i_5274_);
                    return v___x_5277_;
                } else {
                    v_k_x27_5278_ = lean_array_fget_borrowed(v_keys_5273_, v_i_5274_);
                    v___x_5279_ = lean_string_dec_eq(v_k_5275_, v_k_x27_5278_);
                    if v___x_5279_ == 0 {
                        v___x_5280_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5281_ = lean_nat_add(v_i_5274_, v___x_5280_);
                        leanh::lean_dec(v_i_5274_);
                        v_i_5274_ = v___x_5281_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_5274_);
                        return v___x_5279_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_5283_: *mut leanh::LeanObject,
    mut v_i_5284_: *mut leanh::LeanObject,
    mut v_k_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5286_: u8 = 0;
    let mut v_r_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5286_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_5283_, v_i_5284_, v_k_5285_);
    leanh::lean_dec_ref(v_k_5285_);
    leanh::lean_dec_ref(v_keys_5283_);
    v_r_5287_ = leanh::lean_box((v_res_5286_) as usize);
    return v_r_5287_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_5288_: *mut leanh::LeanObject,
    mut v_x_5289_: usize,
    mut v_x_5290_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: usize = 0;
    let mut v___x_5294_: usize = 0;
    let mut v___x_5295_: usize = 0;
    let mut v_j_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: u8 = 0;
    let mut v_node_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: usize = 0;
    let mut v___x_5303_: u8 = 0;
    let mut v_ks_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5288_) == 0 {
                    v_es_5291_ = leanh::lean_ctor_get(v_x_5288_, 0);
                    v___x_5292_ = leanh::lean_box(2);
                    v___x_5293_ = 5usize;
                    v___x_5294_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__1);
                    v___x_5295_ = lean_usize_land(v_x_5289_, v___x_5294_);
                    v_j_5296_ = lean_usize_to_nat(v___x_5295_);
                    v___x_5297_ = lean_array_get_borrowed(v___x_5292_, v_es_5291_, v_j_5296_);
                    leanh::lean_dec(v_j_5296_);
                    match leanh::lean_obj_tag(v___x_5297_) {
                        0 => {
                            v_key_5298_ = leanh::lean_ctor_get(v___x_5297_, 0);
                            v___x_5299_ = lean_string_dec_eq(v_x_5290_, v_key_5298_);
                            return v___x_5299_;
                        }
                        1 => {
                            v_node_5300_ = leanh::lean_ctor_get(v___x_5297_, 0);
                            v___x_5301_ = lean_usize_shift_right(v_x_5289_, v___x_5293_);
                            v_x_5288_ = v_node_5300_;
                            v_x_5289_ = v___x_5301_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5303_ = 0;
                            return v___x_5303_;
                        }
                    }
                } else {
                    v_ks_5304_ = leanh::lean_ctor_get(v_x_5288_, 0);
                    v___x_5305_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5306_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_5304_, v___x_5305_, v_x_5290_);
                    return v___x_5306_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_5307_: *mut leanh::LeanObject,
    mut v_x_5308_: *mut leanh::LeanObject,
    mut v_x_5309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3368__boxed_5310_: usize = 0;
    let mut v_res_5311_: u8 = 0;
    let mut v_r_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3368__boxed_5310_ = leanh::lean_unbox_usize(v_x_5308_);
    leanh::lean_dec(v_x_5308_);
    v_res_5311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_5307_, v_x_3368__boxed_5310_, v_x_5309_);
    leanh::lean_dec_ref(v_x_5309_);
    leanh::lean_dec_ref(v_x_5307_);
    v_r_5312_ = leanh::lean_box((v_res_5311_) as usize);
    return v_r_5312_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_5313_: *mut leanh::LeanObject,
    mut v_x_5314_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5315_: u64 = 0;
    let mut v___x_5316_: usize = 0;
    let mut v___x_5317_: u8 = 0;
    v___x_5315_ = lean_string_hash(v_x_5314_);
    v___x_5316_ = lean_uint64_to_usize(v___x_5315_);
    v___x_5317_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_5313_, v___x_5316_, v_x_5314_);
    return v___x_5317_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_5318_: *mut leanh::LeanObject,
    mut v_x_5319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5320_: u8 = 0;
    let mut v_r_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5318_, v_x_5319_);
    leanh::lean_dec_ref(v_x_5319_);
    leanh::lean_dec_ref(v_x_5318_);
    v_r_5321_ = leanh::lean_box((v_res_5320_) as usize);
    return v_r_5321_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_method_5323_: *mut leanh::LeanObject,
    mut v_completeness_5324_: *mut leanh::LeanObject,
    mut v_inst_5325_: *mut leanh::LeanObject,
    mut v_initState_5326_: *mut leanh::LeanObject,
    mut v_handler_5327_: *mut leanh::LeanObject,
    mut v_onDidChange_5328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: u8 = 0;
    v___x_5330_ = l_Lean_Server_requestHandlers;
    v___x_5331_ = lean_st_ref_get(v___x_5330_);
    v___x_5332_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_5331_, v_method_5323_);
    leanh::lean_dec(v___x_5331_);
    if v___x_5332_ == 0 {
        let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5333_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_5323_, v_completeness_5324_, v_inst_5325_, v_initState_5326_, v_handler_5327_, v_onDidChange_5328_);
        return v___x_5333_;
    } else {
        let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_onDidChange_5328_);
        leanh::lean_dec_ref(v_handler_5327_);
        leanh::lean_dec(v_initState_5326_);
        leanh::lean_dec(v_inst_5325_);
        leanh::lean_dec(v_completeness_5324_);
        v___x_5334_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
        v___x_5335_ = lean_string_append(v___x_5334_, v_method_5323_);
        leanh::lean_dec_ref(v_method_5323_);
        v___x_5336_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
        v___x_5337_ = lean_string_append(v___x_5335_, v___x_5336_);
        v___x_5338_ = lean_mk_io_user_error(v___x_5337_);
        v___x_5339_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5339_, 0, v___x_5338_);
        return v___x_5339_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_method_5340_: *mut leanh::LeanObject,
    mut v_completeness_5341_: *mut leanh::LeanObject,
    mut v_inst_5342_: *mut leanh::LeanObject,
    mut v_initState_5343_: *mut leanh::LeanObject,
    mut v_handler_5344_: *mut leanh::LeanObject,
    mut v_onDidChange_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5347_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_5340_, v_completeness_5341_, v_inst_5342_, v_initState_5343_, v_handler_5344_, v_onDidChange_5345_);
    return v_res_5347_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(
    mut v_method_5348_: *mut leanh::LeanObject,
    mut v_refreshMethod_5349_: *mut leanh::LeanObject,
    mut v_refreshIntervalMs_5350_: *mut leanh::LeanObject,
    mut v_inst_5351_: *mut leanh::LeanObject,
    mut v_initState_5352_: *mut leanh::LeanObject,
    mut v_handler_5353_: *mut leanh::LeanObject,
    mut v_onDidChange_5354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5356_, 0, v_refreshMethod_5349_);
    leanh::lean_ctor_set(v___x_5356_, 1, v_refreshIntervalMs_5350_);
    v___x_5357_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_5348_, v___x_5356_, v_inst_5351_, v_initState_5352_, v_handler_5353_, v_onDidChange_5354_);
    return v___x_5357_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_method_5358_: *mut leanh::LeanObject,
    mut v_refreshMethod_5359_: *mut leanh::LeanObject,
    mut v_refreshIntervalMs_5360_: *mut leanh::LeanObject,
    mut v_inst_5361_: *mut leanh::LeanObject,
    mut v_initState_5362_: *mut leanh::LeanObject,
    mut v_handler_5363_: *mut leanh::LeanObject,
    mut v_onDidChange_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_5358_, v_refreshMethod_5359_, v_refreshIntervalMs_5360_, v_inst_5361_, v_initState_5362_, v_handler_5363_, v_onDidChange_5364_);
    return v_res_5366_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5372_ = l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_;
    v___x_5373_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_;
    v___x_5374_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_;
    v___x_5375_ = leanh::lean_unsigned_to_nat(500);
    v___x_5376_ = l_Lean_Server_FileWorker_InlayHintState_init;
    v___x_5377_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_;
    v___x_5378_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_;
    v___x_5379_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_5373_, v___x_5374_, v___x_5375_, v___x_5372_, v___x_5376_, v___x_5377_, v___x_5378_);
    return v___x_5379_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(
    mut v_a_5380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
    return v_res_5381_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(
    mut v_method_5382_: *mut leanh::LeanObject,
    mut v_refreshMethod_5383_: *mut leanh::LeanObject,
    mut v_refreshIntervalMs_5384_: *mut leanh::LeanObject,
    mut v_stateType_5385_: *mut leanh::LeanObject,
    mut v_inst_5386_: *mut leanh::LeanObject,
    mut v_initState_5387_: *mut leanh::LeanObject,
    mut v_handler_5388_: *mut leanh::LeanObject,
    mut v_onDidChange_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5391_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_5382_, v_refreshMethod_5383_, v_refreshIntervalMs_5384_, v_inst_5386_, v_initState_5387_, v_handler_5388_, v_onDidChange_5389_);
    return v___x_5391_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(
    mut v_method_5392_: *mut leanh::LeanObject,
    mut v_refreshMethod_5393_: *mut leanh::LeanObject,
    mut v_refreshIntervalMs_5394_: *mut leanh::LeanObject,
    mut v_stateType_5395_: *mut leanh::LeanObject,
    mut v_inst_5396_: *mut leanh::LeanObject,
    mut v_initState_5397_: *mut leanh::LeanObject,
    mut v_handler_5398_: *mut leanh::LeanObject,
    mut v_onDidChange_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5401_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_5392_, v_refreshMethod_5393_, v_refreshIntervalMs_5394_, v_stateType_5395_, v_inst_5396_, v_initState_5397_, v_handler_5398_, v_onDidChange_5399_);
    return v_res_5401_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(
    mut v_method_5402_: *mut leanh::LeanObject,
    mut v_completeness_5403_: *mut leanh::LeanObject,
    mut v_stateType_5404_: *mut leanh::LeanObject,
    mut v_inst_5405_: *mut leanh::LeanObject,
    mut v_initState_5406_: *mut leanh::LeanObject,
    mut v_handler_5407_: *mut leanh::LeanObject,
    mut v_onDidChange_5408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5410_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_5402_, v_completeness_5403_, v_inst_5405_, v_initState_5406_, v_handler_5407_, v_onDidChange_5408_);
    return v___x_5410_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_method_5411_: *mut leanh::LeanObject,
    mut v_completeness_5412_: *mut leanh::LeanObject,
    mut v_stateType_5413_: *mut leanh::LeanObject,
    mut v_inst_5414_: *mut leanh::LeanObject,
    mut v_initState_5415_: *mut leanh::LeanObject,
    mut v_handler_5416_: *mut leanh::LeanObject,
    mut v_onDidChange_5417_: *mut leanh::LeanObject,
    mut v_a_5418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5419_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_5411_, v_completeness_5412_, v_stateType_5413_, v_inst_5414_, v_initState_5415_, v_handler_5416_, v_onDidChange_5417_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_5420_: *mut leanh::LeanObject,
    mut v_x_5421_: *mut leanh::LeanObject,
    mut v_x_5422_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5423_: u8 = 0;
    v___x_5423_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5421_, v_x_5422_);
    return v___x_5423_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5424_: *mut leanh::LeanObject,
    mut v_x_5425_: *mut leanh::LeanObject,
    mut v_x_5426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5427_: u8 = 0;
    let mut v_r_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5427_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5424_, v_x_5425_, v_x_5426_);
    leanh::lean_dec_ref(v_x_5426_);
    leanh::lean_dec_ref(v_x_5425_);
    v_r_5428_ = leanh::lean_box((v_res_5427_) as usize);
    return v_r_5428_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(
    mut v_00_u03b1_5429_: *mut leanh::LeanObject,
    mut v_00_u03b2_5430_: *mut leanh::LeanObject,
    mut v_mutex_5431_: *mut leanh::LeanObject,
    mut v_k_5432_: *mut leanh::LeanObject,
    mut v___y_5433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5435_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_5431_, v_k_5432_, v___y_5433_);
    return v___x_5435_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_00_u03b1_5436_: *mut leanh::LeanObject,
    mut v_00_u03b2_5437_: *mut leanh::LeanObject,
    mut v_mutex_5438_: *mut leanh::LeanObject,
    mut v_k_5439_: *mut leanh::LeanObject,
    mut v___y_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5442_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_5436_, v_00_u03b2_5437_, v_mutex_5438_, v_k_5439_, v___y_5440_);
    leanh::lean_dec_ref(v___y_5440_);
    return v_res_5442_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_method_5443_: *mut leanh::LeanObject,
    mut v_completeness_5444_: *mut leanh::LeanObject,
    mut v_stateType_5445_: *mut leanh::LeanObject,
    mut v_inst_5446_: *mut leanh::LeanObject,
    mut v_initState_5447_: *mut leanh::LeanObject,
    mut v_handler_5448_: *mut leanh::LeanObject,
    mut v_onDidChange_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5451_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_5443_, v_completeness_5444_, v_inst_5446_, v_initState_5447_, v_handler_5448_, v_onDidChange_5449_);
    return v___x_5451_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_method_5452_: *mut leanh::LeanObject,
    mut v_completeness_5453_: *mut leanh::LeanObject,
    mut v_stateType_5454_: *mut leanh::LeanObject,
    mut v_inst_5455_: *mut leanh::LeanObject,
    mut v_initState_5456_: *mut leanh::LeanObject,
    mut v_handler_5457_: *mut leanh::LeanObject,
    mut v_onDidChange_5458_: *mut leanh::LeanObject,
    mut v_a_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5460_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_5452_, v_completeness_5453_, v_stateType_5454_, v_inst_5455_, v_initState_5456_, v_handler_5457_, v_onDidChange_5458_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5461_: *mut leanh::LeanObject,
    mut v_x_5462_: *mut leanh::LeanObject,
    mut v_x_5463_: usize,
    mut v_x_5464_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5465_: u8 = 0;
    v___x_5465_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_5462_, v_x_5463_, v_x_5464_);
    return v___x_5465_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_5466_: *mut leanh::LeanObject,
    mut v_x_5467_: *mut leanh::LeanObject,
    mut v_x_5468_: *mut leanh::LeanObject,
    mut v_x_5469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3534__boxed_5470_: usize = 0;
    let mut v_res_5471_: u8 = 0;
    let mut v_r_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3534__boxed_5470_ = leanh::lean_unbox_usize(v_x_5468_);
    leanh::lean_dec(v_x_5468_);
    v_res_5471_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5466_, v_x_5467_, v_x_3534__boxed_5470_, v_x_5469_);
    leanh::lean_dec_ref(v_x_5469_);
    leanh::lean_dec_ref(v_x_5467_);
    v_r_5472_ = leanh::lean_box((v_res_5471_) as usize);
    return v_r_5472_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(
    mut v_params_5473_: *mut leanh::LeanObject,
    mut v_a_5474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5476_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_5473_);
    return v___x_5476_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_params_5477_: *mut leanh::LeanObject,
    mut v_a_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_5477_, v_a_5478_);
    leanh::lean_dec_ref(v_a_5478_);
    return v_res_5480_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(
    mut v_00_u03b2_5481_: *mut leanh::LeanObject,
    mut v_x_5482_: *mut leanh::LeanObject,
    mut v_x_5483_: *mut leanh::LeanObject,
    mut v_x_5484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5485_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_5482_, v_x_5483_, v_x_5484_);
    return v___x_5485_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5486_: *mut leanh::LeanObject,
    mut v_keys_5487_: *mut leanh::LeanObject,
    mut v_vals_5488_: *mut leanh::LeanObject,
    mut v_heq_5489_: *mut leanh::LeanObject,
    mut v_i_5490_: *mut leanh::LeanObject,
    mut v_k_5491_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5492_: u8 = 0;
    v___x_5492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_5487_, v_i_5490_, v_k_5491_);
    return v___x_5492_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_5493_: *mut leanh::LeanObject,
    mut v_keys_5494_: *mut leanh::LeanObject,
    mut v_vals_5495_: *mut leanh::LeanObject,
    mut v_heq_5496_: *mut leanh::LeanObject,
    mut v_i_5497_: *mut leanh::LeanObject,
    mut v_k_5498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5499_: u8 = 0;
    let mut v_r_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5499_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_5493_, v_keys_5494_, v_vals_5495_, v_heq_5496_, v_i_5497_, v_k_5498_);
    leanh::lean_dec_ref(v_k_5498_);
    leanh::lean_dec_ref(v_vals_5495_);
    leanh::lean_dec_ref(v_keys_5494_);
    v_r_5500_ = leanh::lean_box((v_res_5499_) as usize);
    return v_r_5500_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(
    mut v_00_u03b2_5501_: *mut leanh::LeanObject,
    mut v_x_5502_: *mut leanh::LeanObject,
    mut v_x_5503_: usize,
    mut v_x_5504_: usize,
    mut v_x_5505_: *mut leanh::LeanObject,
    mut v_x_5506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5507_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_5502_, v_x_5503_, v_x_5504_, v_x_5505_, v_x_5506_);
    return v___x_5507_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(
    mut v_00_u03b2_5508_: *mut leanh::LeanObject,
    mut v_x_5509_: *mut leanh::LeanObject,
    mut v_x_5510_: *mut leanh::LeanObject,
    mut v_x_5511_: *mut leanh::LeanObject,
    mut v_x_5512_: *mut leanh::LeanObject,
    mut v_x_5513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3560__boxed_5514_: usize = 0;
    let mut v_x_3561__boxed_5515_: usize = 0;
    let mut v_res_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3560__boxed_5514_ = leanh::lean_unbox_usize(v_x_5510_);
    leanh::lean_dec(v_x_5510_);
    v_x_3561__boxed_5515_ = leanh::lean_unbox_usize(v_x_5511_);
    leanh::lean_dec(v_x_5511_);
    v_res_5516_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_5508_, v_x_5509_, v_x_3560__boxed_5514_, v_x_3561__boxed_5515_, v_x_5512_, v_x_5513_);
    return v_res_5516_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(
    mut v_00_u03b2_5517_: *mut leanh::LeanObject,
    mut v_n_5518_: *mut leanh::LeanObject,
    mut v_k_5519_: *mut leanh::LeanObject,
    mut v_v_5520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_5518_, v_k_5519_, v_v_5520_);
    return v___x_5521_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(
    mut v_00_u03b2_5522_: *mut leanh::LeanObject,
    mut v_depth_5523_: usize,
    mut v_keys_5524_: *mut leanh::LeanObject,
    mut v_vals_5525_: *mut leanh::LeanObject,
    mut v_heq_5526_: *mut leanh::LeanObject,
    mut v_i_5527_: *mut leanh::LeanObject,
    mut v_entries_5528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5529_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_5523_, v_keys_5524_, v_vals_5525_, v_i_5527_, v_entries_5528_);
    return v___x_5529_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(
    mut v_00_u03b2_5530_: *mut leanh::LeanObject,
    mut v_depth_5531_: *mut leanh::LeanObject,
    mut v_keys_5532_: *mut leanh::LeanObject,
    mut v_vals_5533_: *mut leanh::LeanObject,
    mut v_heq_5534_: *mut leanh::LeanObject,
    mut v_i_5535_: *mut leanh::LeanObject,
    mut v_entries_5536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5537_: usize = 0;
    let mut v_res_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5537_ = leanh::lean_unbox_usize(v_depth_5531_);
    leanh::lean_dec(v_depth_5531_);
    v_res_5538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_5530_, v_depth_boxed_5537_, v_keys_5532_, v_vals_5533_, v_heq_5534_, v_i_5535_, v_entries_5536_);
    leanh::lean_dec_ref(v_vals_5533_);
    leanh::lean_dec_ref(v_keys_5532_);
    return v_res_5538_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(
    mut v_00_u03b2_5539_: *mut leanh::LeanObject,
    mut v_x_5540_: *mut leanh::LeanObject,
    mut v_x_5541_: *mut leanh::LeanObject,
    mut v_x_5542_: *mut leanh::LeanObject,
    mut v_x_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_5540_, v_x_5541_, v_x_5542_, v_x_5543_);
    return v___x_5544_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_InlayHints(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_GoTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Requests(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_InlayHints(
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
pub unsafe fn initialize_Lean_Server_FileWorker_InlayHints(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_GoTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_Requests(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_InlayHints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_InlayHints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_InlayHints(builtin);
}