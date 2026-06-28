// Lean compiler output
// Module: Lake.Util
// Imports: Lake.Util.Binder Lake.Util.Casing Lake.Util.Cli Lake.Util.Cycle Lake.Util.Date Lake.Util.EquipT Lake.Util.Error Lake.Util.EStateT Lake.Util.Exit Lake.Util.Family Lake.Util.FilePath Lake.Util.Git Lake.Util.IO Lake.Util.JsonObject Lake.Util.Lift Lake.Util.Lock Lake.Util.Log Lake.Util.MainM Lake.Util.Message Lake.Util.Name Lake.Util.NativeLib Lake.Util.Opaque Lake.Util.OrderedTagAttribute Lake.Util.OrdHashSet Lake.Util.Proc Lake.Util.RBArray Lake.Util.Reservoir Lake.Util.Store Lake.Util.StoreInsts Lake.Util.String Lake.Util.Task Lake.Util.Url Lake.Util.Version
use crate::r#gen::Lake::Util::Binder::{
    initialize_Lake_Util_Binder, runtime_initialize_Lake_Util_Binder,
};
use crate::r#gen::Lake::Util::Casing::{
    initialize_Lake_Util_Casing, runtime_initialize_Lake_Util_Casing,
};
use crate::r#gen::Lake::Util::Cli::{initialize_Lake_Util_Cli, runtime_initialize_Lake_Util_Cli};
use crate::r#gen::Lake::Util::Cycle::{
    initialize_Lake_Util_Cycle, runtime_initialize_Lake_Util_Cycle,
};
use crate::r#gen::Lake::Util::Date::{
    initialize_Lake_Util_Date, runtime_initialize_Lake_Util_Date,
};
use crate::r#gen::Lake::Util::EStateT::{
    initialize_Lake_Util_EStateT, runtime_initialize_Lake_Util_EStateT,
};
use crate::r#gen::Lake::Util::EquipT::{
    initialize_Lake_Util_EquipT, runtime_initialize_Lake_Util_EquipT,
};
use crate::r#gen::Lake::Util::Error::{
    initialize_Lake_Util_Error, runtime_initialize_Lake_Util_Error,
};
use crate::r#gen::Lake::Util::Exit::{
    initialize_Lake_Util_Exit, runtime_initialize_Lake_Util_Exit,
};
use crate::r#gen::Lake::Util::Family::{
    initialize_Lake_Util_Family, runtime_initialize_Lake_Util_Family,
};
use crate::r#gen::Lake::Util::FilePath::{
    initialize_Lake_Util_FilePath, runtime_initialize_Lake_Util_FilePath,
};
use crate::r#gen::Lake::Util::Git::{initialize_Lake_Util_Git, runtime_initialize_Lake_Util_Git};
use crate::r#gen::Lake::Util::IO::{initialize_Lake_Util_IO, runtime_initialize_Lake_Util_IO};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::Lift::{
    initialize_Lake_Util_Lift, runtime_initialize_Lake_Util_Lift,
};
use crate::r#gen::Lake::Util::Lock::{
    initialize_Lake_Util_Lock, runtime_initialize_Lake_Util_Lock,
};
use crate::r#gen::Lake::Util::Log::{initialize_Lake_Util_Log, runtime_initialize_Lake_Util_Log};
use crate::r#gen::Lake::Util::MainM::{
    initialize_Lake_Util_MainM, runtime_initialize_Lake_Util_MainM,
};
use crate::r#gen::Lake::Util::Message::{
    initialize_Lake_Util_Message, runtime_initialize_Lake_Util_Message,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lake::Util::NativeLib::{
    initialize_Lake_Util_NativeLib, runtime_initialize_Lake_Util_NativeLib,
};
use crate::r#gen::Lake::Util::Opaque::{
    initialize_Lake_Util_Opaque, runtime_initialize_Lake_Util_Opaque,
};
use crate::r#gen::Lake::Util::OrdHashSet::{
    initialize_Lake_Util_OrdHashSet, runtime_initialize_Lake_Util_OrdHashSet,
};
use crate::r#gen::Lake::Util::OrderedTagAttribute::{
    initialize_Lake_Util_OrderedTagAttribute, runtime_initialize_Lake_Util_OrderedTagAttribute,
};
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lake::Util::RBArray::{
    initialize_Lake_Util_RBArray, runtime_initialize_Lake_Util_RBArray,
};
use crate::r#gen::Lake::Util::Reservoir::{
    initialize_Lake_Util_Reservoir, runtime_initialize_Lake_Util_Reservoir,
};
use crate::r#gen::Lake::Util::Store::{
    initialize_Lake_Util_Store, runtime_initialize_Lake_Util_Store,
};
use crate::r#gen::Lake::Util::StoreInsts::{
    initialize_Lake_Util_StoreInsts, runtime_initialize_Lake_Util_StoreInsts,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, runtime_initialize_Lake_Util_String,
};
use crate::r#gen::Lake::Util::Task::{
    initialize_Lake_Util_Task, runtime_initialize_Lake_Util_Task,
};
use crate::r#gen::Lake::Util::Url::{initialize_Lake_Util_Url, runtime_initialize_Lake_Util_Url};
use crate::r#gen::Lake::Util::Version::{
    initialize_Lake_Util_Version, runtime_initialize_Lake_Util_Version,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Binder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Casing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cli(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Family(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lock(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_MainM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_RBArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_StoreInsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Url(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Binder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Casing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Cli(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Family(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Lock(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_MainM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_OrdHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_RBArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_StoreInsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Url(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util(builtin);
}
