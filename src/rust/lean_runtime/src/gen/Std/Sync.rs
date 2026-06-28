// Lean compiler output
// Module: Std.Sync
// Imports: Std.Sync.Basic Std.Sync.Channel Std.Sync.Mutex Std.Sync.RecursiveMutex Std.Sync.Barrier Std.Sync.Semaphore Std.Sync.SharedMutex Std.Sync.Notify Std.Sync.Broadcast Std.Sync.StreamMap Std.Sync.CancellationToken Std.Sync.CancellationContext
use crate::r#gen::Std::Sync::Barrier::{
    initialize_Std_Sync_Barrier, runtime_initialize_Std_Sync_Barrier,
};
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
use crate::r#gen::Std::Sync::Broadcast::{
    initialize_Std_Sync_Broadcast, runtime_initialize_Std_Sync_Broadcast,
};
use crate::r#gen::Std::Sync::CancellationContext::{
    initialize_Std_Sync_CancellationContext, runtime_initialize_Std_Sync_CancellationContext,
};
use crate::r#gen::Std::Sync::CancellationToken::{
    initialize_Std_Sync_CancellationToken, runtime_initialize_Std_Sync_CancellationToken,
};
use crate::r#gen::Std::Sync::Channel::{
    initialize_Std_Sync_Channel, runtime_initialize_Std_Sync_Channel,
};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, runtime_initialize_Std_Sync_Mutex,
};
use crate::r#gen::Std::Sync::Notify::{
    initialize_Std_Sync_Notify, runtime_initialize_Std_Sync_Notify,
};
use crate::r#gen::Std::Sync::RecursiveMutex::{
    initialize_Std_Sync_RecursiveMutex, runtime_initialize_Std_Sync_RecursiveMutex,
};
use crate::r#gen::Std::Sync::Semaphore::{
    initialize_Std_Sync_Semaphore, runtime_initialize_Std_Sync_Semaphore,
};
use crate::r#gen::Std::Sync::SharedMutex::{
    initialize_Std_Sync_SharedMutex, runtime_initialize_Std_Sync_SharedMutex,
};
use crate::r#gen::Std::Sync::StreamMap::{
    initialize_Std_Sync_StreamMap, runtime_initialize_Std_Sync_StreamMap,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Channel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_RecursiveMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Barrier(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Semaphore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_SharedMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Notify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Broadcast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_StreamMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Channel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_RecursiveMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Barrier(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Semaphore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_SharedMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Notify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Broadcast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_StreamMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync(builtin);
}
