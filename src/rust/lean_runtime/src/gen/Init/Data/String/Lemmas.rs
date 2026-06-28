// Lean compiler output
// Module: Init.Data.String.Lemmas
// Imports: Init.Data.String.Lemmas.Splits Init.Data.String.Lemmas.Modify Init.Data.String.Lemmas.Search Init.Data.String.Lemmas.FindPos Init.Data.String.Lemmas.Basic Init.Data.String.Lemmas.Order Init.Data.String.Lemmas.IsEmpty Init.Data.String.Lemmas.Pattern Init.Data.String.Lemmas.Slice Init.Data.String.Lemmas.Iterate Init.Data.String.Lemmas.Intercalate Init.Data.String.Lemmas.Iter Init.Data.String.Lemmas.Hashable Init.Data.String.Lemmas.TakeDrop Init.Data.String.Lemmas.StringOrder Init.Data.String.Lemmas.Length
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Hashable::{
    initialize_Init_Data_String_Lemmas_Hashable,
    runtime_initialize_Init_Data_String_Lemmas_Hashable,
};
use crate::r#gen::Init::Data::String::Lemmas::Intercalate::{
    initialize_Init_Data_String_Lemmas_Intercalate,
    runtime_initialize_Init_Data_String_Lemmas_Intercalate,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Iter::{
    initialize_Init_Data_String_Lemmas_Iter, runtime_initialize_Init_Data_String_Lemmas_Iter,
};
use crate::r#gen::Init::Data::String::Lemmas::Iterate::{
    initialize_Init_Data_String_Lemmas_Iterate, runtime_initialize_Init_Data_String_Lemmas_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Length::{
    initialize_Init_Data_String_Lemmas_Length, runtime_initialize_Init_Data_String_Lemmas_Length,
};
use crate::r#gen::Init::Data::String::Lemmas::Modify::{
    initialize_Init_Data_String_Lemmas_Modify, runtime_initialize_Init_Data_String_Lemmas_Modify,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::{
    initialize_Init_Data_String_Lemmas_Pattern, runtime_initialize_Init_Data_String_Lemmas_Pattern,
};
use crate::r#gen::Init::Data::String::Lemmas::Search::{
    initialize_Init_Data_String_Lemmas_Search, runtime_initialize_Init_Data_String_Lemmas_Search,
};
use crate::r#gen::Init::Data::String::Lemmas::Slice::{
    initialize_Init_Data_String_Lemmas_Slice, runtime_initialize_Init_Data_String_Lemmas_Slice,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Data::String::Lemmas::StringOrder::{
    initialize_Init_Data_String_Lemmas_StringOrder,
    runtime_initialize_Init_Data_String_Lemmas_StringOrder,
};
use crate::r#gen::Init::Data::String::Lemmas::TakeDrop::{
    initialize_Init_Data_String_Lemmas_TakeDrop,
    runtime_initialize_Init_Data_String_Lemmas_TakeDrop,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_StringOrder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas(
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
pub unsafe fn initialize_Init_Data_String_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Iter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_StringOrder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas(builtin);
}
