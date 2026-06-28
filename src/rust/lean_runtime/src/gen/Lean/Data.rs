// Lean compiler output
// Module: Lean.Data
// Imports: Lean.Data.AssocList Lean.Data.Format Lean.Data.Json Lean.Data.JsonRpc Lean.Data.KVMap Lean.Data.LBool Lean.Data.LOption Lean.Data.Lsp Lean.Data.Name Lean.Data.NameMap Lean.Data.OpenDecl Lean.Data.Options Lean.Data.PersistentArray Lean.Data.PersistentHashMap Lean.Data.PersistentHashSet Lean.Data.Position Lean.Data.PrefixTree Lean.Data.SMap Lean.Data.Trie Lean.Data.NameTrie Lean.Data.RBTree Lean.Data.RBMap Lean.Data.RArray Lean.Data.Iterators
use crate::r#gen::Lean::Data::AssocList::{
    initialize_Lean_Data_AssocList, runtime_initialize_Lean_Data_AssocList,
};
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, runtime_initialize_Lean_Data_Format,
};
use crate::r#gen::Lean::Data::Iterators::{
    initialize_Lean_Data_Iterators, runtime_initialize_Lean_Data_Iterators,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::r#gen::Lean::Data::JsonRpc::{
    initialize_Lean_Data_JsonRpc, runtime_initialize_Lean_Data_JsonRpc,
};
use crate::r#gen::Lean::Data::KVMap::{
    initialize_Lean_Data_KVMap, runtime_initialize_Lean_Data_KVMap,
};
use crate::r#gen::Lean::Data::LBool::{
    initialize_Lean_Data_LBool, runtime_initialize_Lean_Data_LBool,
};
use crate::r#gen::Lean::Data::LOption::{
    initialize_Lean_Data_LOption, runtime_initialize_Lean_Data_LOption,
};
use crate::r#gen::Lean::Data::Lsp::{initialize_Lean_Data_Lsp, runtime_initialize_Lean_Data_Lsp};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, runtime_initialize_Lean_Data_Name,
};
use crate::r#gen::Lean::Data::NameMap::{
    initialize_Lean_Data_NameMap, runtime_initialize_Lean_Data_NameMap,
};
use crate::r#gen::Lean::Data::NameTrie::{
    initialize_Lean_Data_NameTrie, runtime_initialize_Lean_Data_NameTrie,
};
use crate::r#gen::Lean::Data::OpenDecl::{
    initialize_Lean_Data_OpenDecl, runtime_initialize_Lean_Data_OpenDecl,
};
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, runtime_initialize_Lean_Data_Options,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    initialize_Lean_Data_PersistentArray, runtime_initialize_Lean_Data_PersistentArray,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    initialize_Lean_Data_PersistentHashMap, runtime_initialize_Lean_Data_PersistentHashMap,
};
use crate::r#gen::Lean::Data::PersistentHashSet::{
    initialize_Lean_Data_PersistentHashSet, runtime_initialize_Lean_Data_PersistentHashSet,
};
use crate::r#gen::Lean::Data::Position::{
    initialize_Lean_Data_Position, runtime_initialize_Lean_Data_Position,
};
use crate::r#gen::Lean::Data::PrefixTree::{
    initialize_Lean_Data_PrefixTree, runtime_initialize_Lean_Data_PrefixTree,
};
use crate::r#gen::Lean::Data::RArray::{
    initialize_Lean_Data_RArray, runtime_initialize_Lean_Data_RArray,
};
use crate::r#gen::Lean::Data::RBMap::{
    initialize_Lean_Data_RBMap, runtime_initialize_Lean_Data_RBMap,
};
use crate::r#gen::Lean::Data::RBTree::{
    initialize_Lean_Data_RBTree, runtime_initialize_Lean_Data_RBTree,
};
use crate::r#gen::Lean::Data::SMap::{
    initialize_Lean_Data_SMap, runtime_initialize_Lean_Data_SMap,
};
use crate::r#gen::Lean::Data::Trie::{
    initialize_Lean_Data_Trie, runtime_initialize_Lean_Data_Trie,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_LBool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_LOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_OpenDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Position(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PrefixTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_SMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameTrie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RBTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RBMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_JsonRpc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_LBool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_LOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_OpenDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Position(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_PrefixTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_SMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_NameTrie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_RBTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_RBMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data(builtin);
}
