// Lean compiler output
// Module: Lean.Meta.Hint
// Imports: Lean.Meta.TryThis Lean.Util.Diff
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::Split::{
    l_Subarray_drop___redArg, l_Subarray_split___redArg, l_Subarray_take___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::{
    l_Array_toSubarray___redArg, l_Subarray_get___redArg,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_mkObj;
use crate::r#gen::Lean::Data::Lsp::BasicAux::l_Lean_Lsp_instToJsonRange_toJson;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_format, l_Lean_MessageData_nestD, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::TryThis::{
    initialize_Lean_Meta_TryThis, l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit,
    l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_,
    runtime_initialize_Lean_Meta_TryThis,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_includes, l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_ofRange,
};
use crate::r#gen::Lean::Util::Diff::{
    initialize_Lean_Util_Diff, l_Lean_Diff_instBEqAction_beq, runtime_initialize_Lean_Util_Diff,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_data, lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Length::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_to_uint64, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_string_hash, lean_string_mk, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Meta_Hint_textInsertionWidget___closed__0_value: crate::leanh::LeanStringObject<
    1770,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1770,
    m_capacity: 1770,
    m_length: 1769,
    m_data: [
        10, 105, 109, 112, 111, 114, 116, 32, 42, 32, 97, 115, 32, 82, 101, 97, 99, 116, 32, 102,
        114, 111, 109, 32, 39, 114, 101, 97, 99, 116, 39, 59, 10, 105, 109, 112, 111, 114, 116, 32,
        123, 32, 69, 100, 105, 116, 111, 114, 67, 111, 110, 116, 101, 120, 116, 44, 32, 69, 110,
        118, 80, 111, 115, 67, 111, 110, 116, 101, 120, 116, 32, 125, 32, 102, 114, 111, 109, 32,
        39, 64, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 105, 110, 102, 111, 118, 105,
        101, 119, 39, 59, 10, 10, 99, 111, 110, 115, 116, 32, 101, 32, 61, 32, 82, 101, 97, 99,
        116, 46, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109, 101, 110, 116, 59, 10, 101, 120,
        112, 111, 114, 116, 32, 100, 101, 102, 97, 117, 108, 116, 32, 102, 117, 110, 99, 116, 105,
        111, 110, 32, 40, 123, 32, 114, 97, 110, 103, 101, 44, 32, 115, 117, 103, 103, 101, 115,
        116, 105, 111, 110, 44, 32, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116,
        105, 111, 110, 80, 114, 111, 112, 115, 32, 125, 41, 32, 123, 10, 32, 32, 99, 111, 110, 115,
        116, 32, 112, 111, 115, 32, 61, 32, 82, 101, 97, 99, 116, 46, 117, 115, 101, 67, 111, 110,
        116, 101, 120, 116, 40, 69, 110, 118, 80, 111, 115, 67, 111, 110, 116, 101, 120, 116, 41,
        10, 32, 32, 99, 111, 110, 115, 116, 32, 101, 100, 105, 116, 111, 114, 67, 111, 110, 110,
        101, 99, 116, 105, 111, 110, 32, 61, 32, 82, 101, 97, 99, 116, 46, 117, 115, 101, 67, 111,
        110, 116, 101, 120, 116, 40, 69, 100, 105, 116, 111, 114, 67, 111, 110, 116, 101, 120, 116,
        41, 10, 32, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 111, 110, 67, 108, 105, 99, 107,
        40, 41, 32, 123, 10, 32, 32, 32, 32, 101, 100, 105, 116, 111, 114, 67, 111, 110, 110, 101,
        99, 116, 105, 111, 110, 46, 97, 112, 105, 46, 97, 112, 112, 108, 121, 69, 100, 105, 116,
        40, 123, 10, 32, 32, 32, 32, 32, 32, 99, 104, 97, 110, 103, 101, 115, 58, 32, 123, 32, 91,
        112, 111, 115, 46, 117, 114, 105, 93, 58, 32, 91, 123, 32, 114, 97, 110, 103, 101, 44, 32,
        110, 101, 119, 84, 101, 120, 116, 58, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110,
        32, 125, 93, 32, 125, 10, 32, 32, 32, 32, 125, 41, 10, 32, 32, 125, 10, 10, 32, 32, 105,
        102, 32, 40, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110,
        80, 114, 111, 112, 115, 46, 107, 105, 110, 100, 32, 61, 61, 61, 32, 39, 116, 101, 120, 116,
        39, 41, 32, 123, 10, 32, 32, 32, 32, 114, 101, 116, 117, 114, 110, 32, 101, 40, 39, 115,
        112, 97, 110, 39, 44, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 111, 110, 67, 108, 105,
        99, 107, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 116, 105, 116, 108, 101, 58, 32, 97, 99,
        99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115,
        46, 104, 111, 118, 101, 114, 84, 101, 120, 116, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 99,
        108, 97, 115, 115, 78, 97, 109, 101, 58, 32, 39, 108, 105, 110, 107, 32, 112, 111, 105,
        110, 116, 101, 114, 32, 100, 105, 109, 32, 102, 111, 110, 116, 45, 99, 111, 100, 101, 39,
        44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 115, 116, 121, 108, 101, 58, 32, 123, 32, 99, 111,
        108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118, 115, 99, 111, 100, 101, 45, 116,
        101, 120, 116, 76, 105, 110, 107, 45, 102, 111, 114, 101, 103, 114, 111, 117, 110, 100, 41,
        39, 32, 125, 10, 32, 32, 32, 32, 32, 32, 125, 44, 10, 32, 32, 32, 32, 32, 32, 97, 99, 99,
        101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115, 46,
        108, 105, 110, 107, 84, 101, 120, 116, 41, 10, 32, 32, 125, 32, 101, 108, 115, 101, 32,
        105, 102, 32, 40, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111,
        110, 80, 114, 111, 112, 115, 46, 107, 105, 110, 100, 32, 61, 61, 61, 32, 39, 105, 99, 111,
        110, 39, 41, 32, 123, 10, 32, 32, 32, 32, 105, 102, 32, 40, 97, 99, 99, 101, 112, 116, 83,
        117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115, 46, 103, 97, 112, 115,
        41, 32, 123, 10, 32, 32, 32, 32, 32, 32, 99, 111, 110, 115, 116, 32, 105, 99, 111, 110, 32,
        61, 32, 101, 40, 39, 115, 112, 97, 110, 39, 44, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32,
        32, 99, 108, 97, 115, 115, 78, 97, 109, 101, 58, 32, 96, 99, 111, 100, 105, 99, 111, 110,
        32, 99, 111, 100, 105, 99, 111, 110, 45, 36, 123, 97, 99, 99, 101, 112, 116, 83, 117, 103,
        103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115, 46, 99, 111, 100, 105, 99, 111,
        110, 78, 97, 109, 101, 125, 96, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 115, 116, 121, 108,
        101, 58, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 118, 101, 114, 116, 105, 99,
        97, 108, 65, 108, 105, 103, 110, 58, 32, 39, 115, 117, 98, 39, 44, 10, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 32, 102, 111, 110, 116, 83, 105, 122, 101, 58, 32, 39, 118, 97, 114, 40,
        45, 45, 118, 115, 99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 45, 102, 111, 110,
        116, 45, 115, 105, 122, 101, 41, 39, 10, 32, 32, 32, 32, 32, 32, 32, 32, 125, 10, 32, 32,
        32, 32, 32, 32, 125, 41, 10, 32, 32, 32, 32, 32, 32, 114, 101, 116, 117, 114, 110, 32, 101,
        40, 39, 115, 112, 97, 110, 39, 44, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 111, 110,
        67, 108, 105, 99, 107, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 116, 105, 116, 108, 101, 58,
        32, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114,
        111, 112, 115, 46, 104, 111, 118, 101, 114, 84, 101, 120, 116, 44, 10, 32, 32, 32, 32, 32,
        32, 32, 32, 99, 108, 97, 115, 115, 78, 97, 109, 101, 58, 32, 96, 108, 105, 110, 107, 32,
        112, 111, 105, 110, 116, 101, 114, 32, 100, 105, 109, 32, 102, 111, 110, 116, 45, 99, 111,
        100, 101, 96, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 115, 116, 121, 108, 101, 58, 32, 123,
        32, 99, 111, 108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118, 115, 99, 111, 100,
        101, 45, 116, 101, 120, 116, 76, 105, 110, 107, 45, 102, 111, 114, 101, 103, 114, 111, 117,
        110, 100, 41, 39, 32, 125, 10, 32, 32, 32, 32, 32, 32, 125, 44, 32, 39, 32, 39, 44, 32,
        105, 99, 111, 110, 44, 32, 39, 32, 39, 41, 10, 32, 32, 32, 32, 125, 32, 101, 108, 115, 101,
        32, 123, 10, 32, 32, 32, 32, 32, 32, 114, 101, 116, 117, 114, 110, 32, 101, 40, 39, 115,
        112, 97, 110, 39, 44, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 111, 110, 67, 108, 105,
        99, 107, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 116, 105, 116, 108, 101, 58, 32, 97, 99,
        99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115,
        46, 104, 111, 118, 101, 114, 84, 101, 120, 116, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 99,
        108, 97, 115, 115, 78, 97, 109, 101, 58, 32, 96, 108, 105, 110, 107, 32, 112, 111, 105,
        110, 116, 101, 114, 32, 100, 105, 109, 32, 102, 111, 110, 116, 45, 99, 111, 100, 101, 32,
        99, 111, 100, 105, 99, 111, 110, 32, 99, 111, 100, 105, 99, 111, 110, 45, 36, 123, 97, 99,
        99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115,
        46, 99, 111, 100, 105, 99, 111, 110, 78, 97, 109, 101, 125, 96, 44, 10, 32, 32, 32, 32, 32,
        32, 32, 32, 115, 116, 121, 108, 101, 58, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 99, 111, 108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118, 115, 99, 111, 100,
        101, 45, 116, 101, 120, 116, 76, 105, 110, 107, 45, 102, 111, 114, 101, 103, 114, 111, 117,
        110, 100, 41, 39, 44, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 118, 101, 114, 116, 105,
        99, 97, 108, 65, 108, 105, 103, 110, 58, 32, 39, 115, 117, 98, 39, 44, 10, 32, 32, 32, 32,
        32, 32, 32, 32, 32, 32, 102, 111, 110, 116, 83, 105, 122, 101, 58, 32, 39, 118, 97, 114,
        40, 45, 45, 118, 115, 99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 45, 102, 111,
        110, 116, 45, 115, 105, 122, 101, 41, 39, 10, 32, 32, 32, 32, 32, 32, 32, 32, 125, 10, 32,
        32, 32, 32, 32, 32, 125, 41, 10, 32, 32, 32, 32, 125, 10, 10, 32, 32, 125, 10, 32, 32, 116,
        104, 114, 111, 119, 32, 110, 101, 119, 32, 69, 114, 114, 111, 114, 40, 39, 85, 110, 101,
        120, 112, 101, 99, 116, 101, 100, 32, 96, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103,
        101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115, 96, 32, 107, 105, 110, 100, 58, 32,
        39, 32, 43, 32, 97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110,
        80, 114, 111, 112, 115, 46, 107, 105, 110, 100, 41, 10, 125, 0,
    ],
};
static mut l_Lean_Meta_Hint_textInsertionWidget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_textInsertionWidget___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Hint_textInsertionWidget___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Hint_textInsertionWidget___closed__1: u64 = 0;
static mut l_Lean_Meta_Hint_textInsertionWidget___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Hint_textInsertionWidget___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Hint_textInsertionWidget: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value: crate::leanh::LeanStringObject<
    1142,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1142,
    m_capacity: 1142,
    m_length: 1141,
    m_data: [
        10, 105, 109, 112, 111, 114, 116, 32, 42, 32, 97, 115, 32, 82, 101, 97, 99, 116, 32, 102,
        114, 111, 109, 32, 39, 114, 101, 97, 99, 116, 39, 59, 10, 105, 109, 112, 111, 114, 116, 32,
        123, 32, 69, 100, 105, 116, 111, 114, 67, 111, 110, 116, 101, 120, 116, 44, 32, 69, 110,
        118, 80, 111, 115, 67, 111, 110, 116, 101, 120, 116, 32, 125, 32, 102, 114, 111, 109, 32,
        39, 64, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 105, 110, 102, 111, 118, 105,
        101, 119, 39, 59, 10, 10, 99, 111, 110, 115, 116, 32, 101, 32, 61, 32, 82, 101, 97, 99,
        116, 46, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109, 101, 110, 116, 59, 10, 101, 120,
        112, 111, 114, 116, 32, 100, 101, 102, 97, 117, 108, 116, 32, 102, 117, 110, 99, 116, 105,
        111, 110, 32, 40, 123, 32, 100, 105, 102, 102, 44, 32, 114, 97, 110, 103, 101, 44, 32, 115,
        117, 103, 103, 101, 115, 116, 105, 111, 110, 32, 125, 41, 32, 123, 10, 32, 32, 99, 111,
        110, 115, 116, 32, 112, 111, 115, 32, 61, 32, 82, 101, 97, 99, 116, 46, 117, 115, 101, 67,
        111, 110, 116, 101, 120, 116, 40, 69, 110, 118, 80, 111, 115, 67, 111, 110, 116, 101, 120,
        116, 41, 10, 32, 32, 99, 111, 110, 115, 116, 32, 101, 100, 105, 116, 111, 114, 67, 111,
        110, 110, 101, 99, 116, 105, 111, 110, 32, 61, 32, 82, 101, 97, 99, 116, 46, 117, 115, 101,
        67, 111, 110, 116, 101, 120, 116, 40, 69, 100, 105, 116, 111, 114, 67, 111, 110, 116, 101,
        120, 116, 41, 10, 32, 32, 99, 111, 110, 115, 116, 32, 105, 110, 115, 83, 116, 121, 108,
        101, 32, 61, 32, 123, 10, 32, 32, 32, 32, 115, 116, 121, 108, 101, 58, 32, 123, 32, 99,
        111, 108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118, 115, 99, 111, 100, 101, 45,
        116, 101, 120, 116, 76, 105, 110, 107, 45, 102, 111, 114, 101, 103, 114, 111, 117, 110,
        100, 41, 39, 32, 125, 10, 32, 32, 125, 10, 32, 32, 99, 111, 110, 115, 116, 32, 100, 101,
        108, 83, 116, 121, 108, 101, 32, 61, 32, 123, 10, 32, 32, 32, 32, 115, 116, 121, 108, 101,
        58, 32, 123, 32, 99, 111, 108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118, 115,
        99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 69, 114, 114, 111, 114, 45, 102, 111,
        114, 101, 103, 114, 111, 117, 110, 100, 41, 39, 44, 32, 116, 101, 120, 116, 68, 101, 99,
        111, 114, 97, 116, 105, 111, 110, 58, 32, 39, 108, 105, 110, 101, 45, 116, 104, 114, 111,
        117, 103, 104, 39, 32, 125, 10, 32, 32, 125, 10, 32, 32, 99, 111, 110, 115, 116, 32, 100,
        101, 102, 83, 116, 121, 108, 101, 32, 61, 32, 123, 10, 32, 32, 32, 32, 115, 116, 121, 108,
        101, 58, 32, 123, 32, 99, 111, 108, 111, 114, 58, 32, 39, 118, 97, 114, 40, 45, 45, 118,
        115, 99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 45, 102, 111, 114, 101, 103, 114,
        111, 117, 110, 100, 41, 39, 32, 125, 10, 32, 32, 125, 10, 32, 32, 102, 117, 110, 99, 116,
        105, 111, 110, 32, 111, 110, 67, 108, 105, 99, 107, 40, 41, 32, 123, 10, 32, 32, 32, 32,
        101, 100, 105, 116, 111, 114, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 46, 97, 112,
        105, 46, 97, 112, 112, 108, 121, 69, 100, 105, 116, 40, 123, 10, 32, 32, 32, 32, 32, 32,
        99, 104, 97, 110, 103, 101, 115, 58, 32, 123, 32, 91, 112, 111, 115, 46, 117, 114, 105, 93,
        58, 32, 91, 123, 32, 114, 97, 110, 103, 101, 44, 32, 110, 101, 119, 84, 101, 120, 116, 58,
        32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 32, 125, 93, 32, 125, 10, 32, 32, 32,
        32, 125, 41, 10, 32, 32, 125, 10, 10, 32, 32, 99, 111, 110, 115, 116, 32, 115, 112, 97,
        110, 115, 32, 61, 32, 100, 105, 102, 102, 46, 109, 97, 112, 32, 40, 99, 111, 109, 112, 32,
        61, 62, 10, 32, 32, 32, 32, 99, 111, 109, 112, 46, 116, 121, 112, 101, 32, 61, 61, 61, 32,
        39, 100, 101, 108, 101, 116, 105, 111, 110, 39, 32, 63, 32, 101, 40, 39, 115, 112, 97, 110,
        39, 44, 32, 100, 101, 108, 83, 116, 121, 108, 101, 44, 32, 99, 111, 109, 112, 46, 116, 101,
        120, 116, 41, 32, 58, 10, 32, 32, 32, 32, 99, 111, 109, 112, 46, 116, 121, 112, 101, 32,
        61, 61, 61, 32, 39, 105, 110, 115, 101, 114, 116, 105, 111, 110, 39, 32, 63, 32, 101, 40,
        39, 115, 112, 97, 110, 39, 44, 32, 105, 110, 115, 83, 116, 121, 108, 101, 44, 32, 99, 111,
        109, 112, 46, 116, 101, 120, 116, 41, 32, 58, 10, 32, 32, 32, 32, 32, 32, 101, 40, 39, 115,
        112, 97, 110, 39, 44, 32, 100, 101, 102, 83, 116, 121, 108, 101, 44, 32, 99, 111, 109, 112,
        46, 116, 101, 120, 116, 41, 10, 32, 32, 41, 10, 32, 32, 99, 111, 110, 115, 116, 32, 102,
        117, 108, 108, 68, 105, 102, 102, 32, 61, 32, 101, 40, 39, 115, 112, 97, 110, 39, 44, 10,
        32, 32, 32, 32, 123, 32, 111, 110, 67, 108, 105, 99, 107, 44, 10, 32, 32, 32, 32, 32, 32,
        116, 105, 116, 108, 101, 58, 32, 39, 65, 112, 112, 108, 121, 32, 115, 117, 103, 103, 101,
        115, 116, 105, 111, 110, 39, 44, 10, 32, 32, 32, 32, 32, 32, 99, 108, 97, 115, 115, 78, 97,
        109, 101, 58, 32, 39, 108, 105, 110, 107, 32, 112, 111, 105, 110, 116, 101, 114, 32, 100,
        105, 109, 32, 102, 111, 110, 116, 45, 99, 111, 100, 101, 39, 44, 10, 32, 32, 32, 32, 32,
        32, 115, 116, 121, 108, 101, 58, 32, 123, 32, 100, 105, 115, 112, 108, 97, 121, 58, 32, 39,
        105, 110, 108, 105, 110, 101, 45, 98, 108, 111, 99, 107, 39, 44, 32, 118, 101, 114, 116,
        105, 99, 97, 108, 65, 108, 105, 103, 110, 58, 32, 39, 116, 101, 120, 116, 45, 116, 111,
        112, 39, 32, 125, 32, 125, 44, 10, 32, 32, 32, 32, 115, 112, 97, 110, 115, 41, 10, 32, 32,
        114, 101, 116, 117, 114, 110, 32, 102, 117, 108, 108, 68, 105, 102, 102, 10, 125, 0,
    ],
};
static mut l_Lean_Meta_Hint_tryThisDiffWidget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Hint_tryThisDiffWidget___closed__1: u64 = 0;
static mut l_Lean_Meta_Hint_tryThisDiffWidget___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Hint_tryThisDiffWidget___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Hint_tryThisDiffWidget: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 101, 108, 101, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 99, 104, 97, 110, 103, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0_value:
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
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value:
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
    m_fun: l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value:
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
    m_fun: l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Hint_instToMessageDataSuggestion: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value:
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
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 128, 162, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 105, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 114, 121, 84, 104, 105, 115, 68, 105, 102, 102, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value) as *mut crate::leanh::LeanObject,15479558908960879501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value) as *mut crate::leanh::LeanObject,647364315083554222 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 102, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 97, 110, 103, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 105, 110, 107, 84, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [91, 97, 112, 112, 108, 121, 93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 101, 120, 116, 73, 110, 115, 101, 114, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value) as *mut crate::leanh::LeanObject,15479558908960879501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value) as *mut crate::leanh::LeanObject,6343280674608731273 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [97, 99, 99, 101, 112, 116, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 80, 114, 111, 112, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [107, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [104, 111, 118, 101, 114, 84, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [65, 112, 112, 108, 121, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_hint___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [104, 105, 110, 116, 0],
    };
static mut l_Lean_MessageData_hint___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_hint___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MessageData_hint___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MessageData_hint___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7665372338342887846 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MessageData_hint___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_hint___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MessageData_hint___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [10, 10, 72, 105, 110, 116, 58, 32, 0],
    };
static mut l_Lean_MessageData_hint___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_hint___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_MessageData_hint___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_hint___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Hint_textInsertionWidget___closed__1() -> u64 {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: u64 = 0;
    v___x_3727_ = l_Lean_Meta_Hint_textInsertionWidget___closed__0;
    v___x_3728_ = lean_string_hash(v___x_3727_);
    return v___x_3728_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_textInsertionWidget___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3729_: u64 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_textInsertionWidget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_textInsertionWidget___closed__1_once),
        _init_l_Lean_Meta_Hint_textInsertionWidget___closed__1,
    );
    v___x_3730_ = l_Lean_Meta_Hint_textInsertionWidget___closed__0;
    v___x_3731_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3731_, 0, v___x_3730_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3731_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3729_,
    );
    return v___x_3731_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_textInsertionWidget() -> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_textInsertionWidget___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_textInsertionWidget___closed__2_once),
        _init_l_Lean_Meta_Hint_textInsertionWidget___closed__2,
    );
    return v___x_3732_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__1() -> u64 {
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u64 = 0;
    v___x_3734_ = l_Lean_Meta_Hint_tryThisDiffWidget___closed__0;
    v___x_3735_ = lean_string_hash(v___x_3734_);
    return v___x_3735_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3736_: u64 = 0;
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_tryThisDiffWidget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_once),
        _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__1,
    );
    v___x_3737_ = l_Lean_Meta_Hint_tryThisDiffWidget___closed__0;
    v___x_3738_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3738_, 0, v___x_3737_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3738_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3736_,
    );
    return v___x_3738_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_tryThisDiffWidget() -> *mut crate::leanh::LeanObject {
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3739_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_tryThisDiffWidget___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_tryThisDiffWidget___closed__2_once),
        _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__2,
    );
    return v___x_3739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(
    mut v_sz_3740_: usize,
    mut v_i_3741_: usize,
    mut v_bs_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3743_: u8 = 0;
    let mut v_v_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: usize = 0;
    let mut v___x_3748_: usize = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3743_ = lean_usize_dec_lt(v_i_3741_, v_sz_3740_);
                if v___x_3743_ == 0 {
                    return v_bs_3742_;
                } else {
                    v_v_3744_ = lean_array_uget(v_bs_3742_, v_i_3741_);
                    v___x_3745_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3746_ = lean_array_uset(v_bs_3742_, v_i_3741_, v___x_3745_);
                    v___x_3747_ = 1usize;
                    v___x_3748_ = lean_usize_add(v_i_3741_, v___x_3747_);
                    v___x_3749_ = lean_array_uset(v_bs_x27_3746_, v_i_3741_, v_v_3744_);
                    v_i_3741_ = v___x_3748_;
                    v_bs_3742_ = v___x_3749_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(
    mut v_sz_3751_: *mut crate::leanh::LeanObject,
    mut v_i_3752_: *mut crate::leanh::LeanObject,
    mut v_bs_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3754_: usize = 0;
    let mut v_i_boxed_3755_: usize = 0;
    let mut v_res_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3754_ = crate::leanh::lean_unbox_usize(v_sz_3751_);
    crate::leanh::lean_dec(v_sz_3751_);
    v_i_boxed_3755_ = crate::leanh::lean_unbox_usize(v_i_3752_);
    crate::leanh::lean_dec(v_i_3752_);
    v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_boxed_3754_, v_i_boxed_3755_, v_bs_3753_);
    return v_res_3756_;
}
pub unsafe fn l_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(
    mut v_a_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3758_: usize = 0;
    let mut v___x_3759_: usize = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_3758_ = lean_array_size(v_a_3757_);
    v___x_3759_ = 0usize;
    v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_3758_, v___x_3759_, v_a_3757_);
    v___x_3761_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3761_, 0, v___x_3760_);
    return v___x_3761_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(
    mut v_sz_3782_: usize,
    mut v_i_3783_: usize,
    mut v_bs_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: u8 = 0;
    let mut v_v_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3785_ = lean_usize_dec_lt(v_i_3783_, v_sz_3782_);
                if v___x_3785_ == 0 {
                    return v_bs_3784_;
                } else {
                    v_v_3786_ = lean_array_uget(v_bs_3784_, v_i_3783_);
                    v_fst_3787_ = crate::leanh::lean_ctor_get(v_v_3786_, 0);
                    v_snd_3788_ = crate::leanh::lean_ctor_get(v_v_3786_, 1);
                    v_isSharedCheck_3831_ = (!crate::leanh::lean_is_exclusive(v_v_3786_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3790_ = v_v_3786_;
                        v_isShared_3791_ = v_isSharedCheck_3831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3788_);
                        crate::leanh::lean_inc(v_fst_3787_);
                        crate::leanh::lean_dec(v_v_3786_);
                        v___x_3790_ = crate::leanh::lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3831_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3792_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3793_ = lean_array_uset(v_bs_3784_, v_i_3783_, v___x_3792_);
                v___x_3800_ = (crate::leanh::lean_unbox(v_fst_3787_) as u8);
                crate::leanh::lean_dec(v_fst_3787_);
                match v___x_3800_ {
                    0 => {
                        v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3;
                        v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4;
                        v___x_3803_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3803_, 0, v_snd_3788_);
                        if v_isShared_3791_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3803_);
                            crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3802_);
                            v___x_3805_ = v___x_3790_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3810_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3802_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3803_);
                            v___x_3805_ = v_reuseFailAlloc_3810_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7;
                        v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4;
                        v___x_3813_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3813_, 0, v_snd_3788_);
                        if v_isShared_3791_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3813_);
                            crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3812_);
                            v___x_3815_ = v___x_3790_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3820_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3812_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3813_);
                            v___x_3815_ = v_reuseFailAlloc_3820_;
                            state = 4;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10;
                        v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4;
                        v___x_3823_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3823_, 0, v_snd_3788_);
                        if v_isShared_3791_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3823_);
                            crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3822_);
                            v___x_3825_ = v___x_3790_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3830_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3822_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3823_);
                            v___x_3825_ = v_reuseFailAlloc_3830_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3796_ = 1usize;
                v___x_3797_ = lean_usize_add(v_i_3783_, v___x_3796_);
                v___x_3798_ = lean_array_uset(v_bs_x27_3793_, v_i_3783_, v___y_3795_);
                v_i_3783_ = v___x_3797_;
                v_bs_3784_ = v___x_3798_;
                state = 0;
                continue;
            }
            3 => {
                v___x_3806_ = crate::leanh::lean_box(0);
                v___x_3807_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3807_, 0, v___x_3805_);
                crate::leanh::lean_ctor_set(v___x_3807_, 1, v___x_3806_);
                v___x_3808_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3801_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                v___x_3809_ = l_Lean_Json_mkObj(v___x_3808_);
                crate::leanh::lean_dec_ref_known(v___x_3808_, 2);
                v___y_3795_ = v___x_3809_;
                state = 2;
                continue;
            }
            4 => {
                v___x_3816_ = crate::leanh::lean_box(0);
                v___x_3817_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3815_);
                crate::leanh::lean_ctor_set(v___x_3817_, 1, v___x_3816_);
                v___x_3818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3811_);
                crate::leanh::lean_ctor_set(v___x_3818_, 1, v___x_3817_);
                v___x_3819_ = l_Lean_Json_mkObj(v___x_3818_);
                crate::leanh::lean_dec_ref_known(v___x_3818_, 2);
                v___y_3795_ = v___x_3819_;
                state = 2;
                continue;
            }
            5 => {
                v___x_3826_ = crate::leanh::lean_box(0);
                v___x_3827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3827_, 0, v___x_3825_);
                crate::leanh::lean_ctor_set(v___x_3827_, 1, v___x_3826_);
                v___x_3828_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3828_, 0, v___x_3821_);
                crate::leanh::lean_ctor_set(v___x_3828_, 1, v___x_3827_);
                v___x_3829_ = l_Lean_Json_mkObj(v___x_3828_);
                crate::leanh::lean_dec_ref_known(v___x_3828_, 2);
                v___y_3795_ = v___x_3829_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___boxed(
    mut v_sz_3832_: *mut crate::leanh::LeanObject,
    mut v_i_3833_: *mut crate::leanh::LeanObject,
    mut v_bs_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3835_: usize = 0;
    let mut v_i_boxed_3836_: usize = 0;
    let mut v_res_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3835_ = crate::leanh::lean_unbox_usize(v_sz_3832_);
    crate::leanh::lean_dec(v_sz_3832_);
    v_i_boxed_3836_ = crate::leanh::lean_unbox_usize(v_i_3833_);
    crate::leanh::lean_dec(v_i_3833_);
    v_res_3837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_boxed_3835_, v_i_boxed_3836_, v_bs_3834_);
    return v_res_3837_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(
    mut v_ds_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3839_: usize = 0;
    let mut v___x_3840_: usize = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_3839_ = lean_array_size(v_ds_3838_);
    v___x_3840_ = 0usize;
    v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_3839_, v___x_3840_, v_ds_3838_);
    v___x_3842_ =
        l_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(
            v___x_3841_,
        );
    return v___x_3842_;
}
pub unsafe fn _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: u32 = 0;
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = 821;
    v___x_3844_ = crate::leanh::lean_box_uint32(v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = crate::leanh::lean_box(0);
    v___x_3846_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1;
    v___x_3847_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3847_, 0, v___x_3846_);
    crate::leanh::lean_ctor_set(v___x_3847_, 1, v___x_3845_);
    return v___x_3847_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3848_) == 0 {
                    v___x_3850_ = lean_array_to_list(v_a_3849_);
                    return v___x_3850_;
                } else {
                    v_head_3851_ = crate::leanh::lean_ctor_get(v_a_3848_, 0);
                    v_tail_3852_ = crate::leanh::lean_ctor_get(v_a_3848_, 1);
                    v_isSharedCheck_3862_ = (!crate::leanh::lean_is_exclusive(v_a_3848_)) as u8;
                    if v_isSharedCheck_3862_ == 0 {
                        v___x_3854_ = v_a_3848_;
                        v_isShared_3855_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3852_);
                        crate::leanh::lean_inc(v_head_3851_);
                        crate::leanh::lean_dec(v_a_3848_);
                        v___x_3854_ = crate::leanh::lean_box(0);
                        v_isShared_3855_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once), _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0);
                if v_isShared_3855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3854_, 1, v___x_3856_);
                    v___x_3858_ = v___x_3854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_head_3851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3856_);
                    v___x_3858_ = v_reuseFailAlloc_3861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3859_ =
                    l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3849_, v___x_3858_);
                v_a_3848_ = v_tail_3852_;
                v_a_3849_ = v___x_3859_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3863_: u32 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = 818;
    v___x_3864_ = crate::leanh::lean_box_uint32(v___x_3863_);
    return v___x_3864_;
}
pub unsafe fn _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3865_ = crate::leanh::lean_box(0);
    v___x_3866_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1;
    v___x_3867_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
    crate::leanh::lean_ctor_set(v___x_3867_, 1, v___x_3865_);
    return v___x_3867_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(
    mut v_a_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3868_) == 0 {
                    v___x_3870_ = lean_array_to_list(v_a_3869_);
                    return v___x_3870_;
                } else {
                    v_head_3871_ = crate::leanh::lean_ctor_get(v_a_3868_, 0);
                    v_tail_3872_ = crate::leanh::lean_ctor_get(v_a_3868_, 1);
                    v_isSharedCheck_3882_ = (!crate::leanh::lean_is_exclusive(v_a_3868_)) as u8;
                    if v_isSharedCheck_3882_ == 0 {
                        v___x_3874_ = v_a_3868_;
                        v_isShared_3875_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3872_);
                        crate::leanh::lean_inc(v_head_3871_);
                        crate::leanh::lean_dec(v_a_3868_);
                        v___x_3874_ = crate::leanh::lean_box(0);
                        v_isShared_3875_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once), _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0);
                if v_isShared_3875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3874_, 1, v___x_3876_);
                    v___x_3878_ = v___x_3874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_head_3871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3876_);
                    v___x_3878_ = v_reuseFailAlloc_3881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3879_ =
                    l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3869_, v___x_3878_);
                v_a_3868_ = v_tail_3872_;
                v_a_3869_ = v___x_3879_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(
    mut v_sz_3885_: usize,
    mut v_i_3886_: usize,
    mut v_bs_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3888_: u8 = 0;
    let mut v_v_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: usize = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: u8 = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3888_ = lean_usize_dec_lt(v_i_3886_, v_sz_3885_);
                if v___x_3888_ == 0 {
                    return v_bs_3887_;
                } else {
                    v_v_3889_ = lean_array_uget_borrowed(v_bs_3887_, v_i_3886_);
                    v_fst_3890_ = crate::leanh::lean_ctor_get(v_v_3889_, 0);
                    crate::leanh::lean_inc(v_fst_3890_);
                    v_snd_3891_ = crate::leanh::lean_ctor_get(v_v_3889_, 1);
                    crate::leanh::lean_inc(v_snd_3891_);
                    v___x_3892_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3893_ = lean_array_uset(v_bs_3887_, v_i_3886_, v___x_3892_);
                    v___x_3900_ = (crate::leanh::lean_unbox(v_fst_3890_) as u8);
                    crate::leanh::lean_dec(v_fst_3890_);
                    match v___x_3900_ {
                        0 => {
                            v___x_3901_ = lean_string_data(v_snd_3891_);
                            v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0;
                            v___x_3903_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(v___x_3901_, v___x_3902_);
                            v___x_3904_ = lean_string_mk(v___x_3903_);
                            v___y_3895_ = v___x_3904_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_3905_ = lean_string_data(v_snd_3891_);
                            v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0;
                            v___x_3907_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(v___x_3905_, v___x_3906_);
                            v___x_3908_ = lean_string_mk(v___x_3907_);
                            v___y_3895_ = v___x_3908_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3895_ = v_snd_3891_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3896_ = 1usize;
                v___x_3897_ = lean_usize_add(v_i_3886_, v___x_3896_);
                v___x_3898_ = lean_array_uset(v_bs_x27_3893_, v_i_3886_, v___y_3895_);
                v_i_3886_ = v___x_3897_;
                v_bs_3887_ = v___x_3898_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___boxed(
    mut v_sz_3909_: *mut crate::leanh::LeanObject,
    mut v_i_3910_: *mut crate::leanh::LeanObject,
    mut v_bs_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3912_: usize = 0;
    let mut v_i_boxed_3913_: usize = 0;
    let mut v_res_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3912_ = crate::leanh::lean_unbox_usize(v_sz_3909_);
    crate::leanh::lean_dec(v_sz_3909_);
    v_i_boxed_3913_ = crate::leanh::lean_unbox_usize(v_i_3910_);
    crate::leanh::lean_dec(v_i_3910_);
    v_res_3914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_boxed_3912_, v_i_boxed_3913_, v_bs_3911_);
    return v_res_3914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(
    mut v_as_3915_: *mut crate::leanh::LeanObject,
    mut v_i_3916_: usize,
    mut v_stop_3917_: usize,
    mut v_b_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: usize = 0;
    let mut v___x_3923_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3919_ = lean_usize_dec_eq(v_i_3916_, v_stop_3917_);
                if v___x_3919_ == 0 {
                    v___x_3920_ = lean_array_uget_borrowed(v_as_3915_, v_i_3916_);
                    v___x_3921_ = lean_string_append(v_b_3918_, v___x_3920_);
                    v___x_3922_ = 1usize;
                    v___x_3923_ = lean_usize_add(v_i_3916_, v___x_3922_);
                    v_i_3916_ = v___x_3923_;
                    v_b_3918_ = v___x_3921_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3918_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3___boxed(
    mut v_as_3925_: *mut crate::leanh::LeanObject,
    mut v_i_3926_: *mut crate::leanh::LeanObject,
    mut v_stop_3927_: *mut crate::leanh::LeanObject,
    mut v_b_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3929_: usize = 0;
    let mut v_stop_boxed_3930_: usize = 0;
    let mut v_res_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3929_ = crate::leanh::lean_unbox_usize(v_i_3926_);
    crate::leanh::lean_dec(v_i_3926_);
    v_stop_boxed_3930_ = crate::leanh::lean_unbox_usize(v_stop_3927_);
    crate::leanh::lean_dec(v_stop_3927_);
    v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_as_3925_, v_i_boxed_3929_, v_stop_boxed_3930_, v_b_3928_);
    crate::leanh::lean_dec_ref(v_as_3925_);
    return v_res_3931_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(
    mut v_ds_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3934_: usize = 0;
    let mut v___x_3935_: usize = 0;
    let mut v_rangeStrs_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: u8 = 0;
    v_sz_3934_ = lean_array_size(v_ds_3933_);
    v___x_3935_ = 0usize;
    v_rangeStrs_3936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_3934_, v___x_3935_, v_ds_3933_);
    v___x_3937_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
    v___x_3938_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3939_ = lean_array_get_size(v_rangeStrs_3936_);
    v___x_3940_ = lean_nat_dec_lt(v___x_3938_, v___x_3939_);
    if v___x_3940_ == 0 {
        crate::leanh::lean_dec_ref(v_rangeStrs_3936_);
        return v___x_3937_;
    } else {
        let mut v___x_3941_: u8 = 0;
        v___x_3941_ = lean_nat_dec_le(v___x_3939_, v___x_3939_);
        if v___x_3941_ == 0 {
            if v___x_3940_ == 0 {
                crate::leanh::lean_dec_ref(v_rangeStrs_3936_);
                return v___x_3937_;
            } else {
                let mut v___x_3942_: usize = 0;
                let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3942_ = lean_usize_of_nat(v___x_3939_);
                v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_3936_, v___x_3935_, v___x_3942_, v___x_3937_);
                crate::leanh::lean_dec_ref(v_rangeStrs_3936_);
                return v___x_3943_;
            }
        } else {
            let mut v___x_3944_: usize = 0;
            let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3944_ = lean_usize_of_nat(v___x_3939_);
            v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_3936_, v___x_3935_, v___x_3944_, v___x_3937_);
            crate::leanh::lean_dec_ref(v_rangeStrs_3936_);
            return v___x_3945_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorIdx(
    mut v_x_3946_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3946_ {
        0 => {
            let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3947_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3947_;
        }
        1 => {
            let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3948_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3948_;
        }
        2 => {
            let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3949_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3949_;
        }
        3 => {
            let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3950_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3950_;
        }
        _ => {
            let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3951_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3951_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorIdx___boxed(
    mut v_x_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3953_: u8 = 0;
    let mut v_res_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3953_ = (crate::leanh::lean_unbox(v_x_3952_) as u8);
    v_res_3954_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx(v_x_boxed_3953_);
    return v_res_3954_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_toCtorIdx(
    mut v_x_3955_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3956_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx(v_x_3955_);
    return v___x_3956_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_toCtorIdx___boxed(
    mut v_x_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3958_: u8 = 0;
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3958_ = (crate::leanh::lean_unbox(v_x_3957_) as u8);
    v_res_3959_ = l_Lean_Meta_Hint_DiffGranularity_toCtorIdx(v_x_4__boxed_3958_);
    return v_res_3959_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(
    mut v_k_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3960_);
    return v_k_3960_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(
    mut v_k_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3962_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_3961_);
    crate::leanh::lean_dec(v_k_3961_);
    return v_res_3962_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorElim(
    mut v_motive_3963_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3964_: *mut crate::leanh::LeanObject,
    mut v_t_3965_: u8,
    mut v_h_3966_: *mut crate::leanh::LeanObject,
    mut v_k_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3967_);
    return v_k_3967_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(
    mut v_motive_3968_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3969_: *mut crate::leanh::LeanObject,
    mut v_t_3970_: *mut crate::leanh::LeanObject,
    mut v_h_3971_: *mut crate::leanh::LeanObject,
    mut v_k_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3973_ = (crate::leanh::lean_unbox(v_t_3970_) as u8);
    v_res_3974_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(
        v_motive_3968_,
        v_ctorIdx_3969_,
        v_t_boxed_3973_,
        v_h_3971_,
        v_k_3972_,
    );
    crate::leanh::lean_dec(v_k_3972_);
    crate::leanh::lean_dec(v_ctorIdx_3969_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(
    mut v_auto_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_auto_3975_);
    return v_auto_3975_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(
    mut v_auto_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_3976_);
    crate::leanh::lean_dec(v_auto_3976_);
    return v_res_3977_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_auto_elim(
    mut v_motive_3978_: *mut crate::leanh::LeanObject,
    mut v_t_3979_: u8,
    mut v_h_3980_: *mut crate::leanh::LeanObject,
    mut v_auto_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_auto_3981_);
    return v_auto_3981_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(
    mut v_motive_3982_: *mut crate::leanh::LeanObject,
    mut v_t_3983_: *mut crate::leanh::LeanObject,
    mut v_h_3984_: *mut crate::leanh::LeanObject,
    mut v_auto_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3986_: u8 = 0;
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3986_ = (crate::leanh::lean_unbox(v_t_3983_) as u8);
    v_res_3987_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(
        v_motive_3982_,
        v_t_boxed_3986_,
        v_h_3984_,
        v_auto_3985_,
    );
    crate::leanh::lean_dec(v_auto_3985_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(
    mut v_char_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_char_3988_);
    return v_char_3988_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(
    mut v_char_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_3989_);
    crate::leanh::lean_dec(v_char_3989_);
    return v_res_3990_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_char_elim(
    mut v_motive_3991_: *mut crate::leanh::LeanObject,
    mut v_t_3992_: u8,
    mut v_h_3993_: *mut crate::leanh::LeanObject,
    mut v_char_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_char_3994_);
    return v_char_3994_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(
    mut v_motive_3995_: *mut crate::leanh::LeanObject,
    mut v_t_3996_: *mut crate::leanh::LeanObject,
    mut v_h_3997_: *mut crate::leanh::LeanObject,
    mut v_char_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3999_: u8 = 0;
    let mut v_res_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3999_ = (crate::leanh::lean_unbox(v_t_3996_) as u8);
    v_res_4000_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(
        v_motive_3995_,
        v_t_boxed_3999_,
        v_h_3997_,
        v_char_3998_,
    );
    crate::leanh::lean_dec(v_char_3998_);
    return v_res_4000_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(
    mut v_word_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_word_4001_);
    return v_word_4001_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(
    mut v_word_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_4002_);
    crate::leanh::lean_dec(v_word_4002_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_word_elim(
    mut v_motive_4004_: *mut crate::leanh::LeanObject,
    mut v_t_4005_: u8,
    mut v_h_4006_: *mut crate::leanh::LeanObject,
    mut v_word_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_word_4007_);
    return v_word_4007_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(
    mut v_motive_4008_: *mut crate::leanh::LeanObject,
    mut v_t_4009_: *mut crate::leanh::LeanObject,
    mut v_h_4010_: *mut crate::leanh::LeanObject,
    mut v_word_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4012_: u8 = 0;
    let mut v_res_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4012_ = (crate::leanh::lean_unbox(v_t_4009_) as u8);
    v_res_4013_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(
        v_motive_4008_,
        v_t_boxed_4012_,
        v_h_4010_,
        v_word_4011_,
    );
    crate::leanh::lean_dec(v_word_4011_);
    return v_res_4013_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(
    mut v_all_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_4014_);
    return v_all_4014_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(
    mut v_all_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4016_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_4015_);
    crate::leanh::lean_dec(v_all_4015_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_all_elim(
    mut v_motive_4017_: *mut crate::leanh::LeanObject,
    mut v_t_4018_: u8,
    mut v_h_4019_: *mut crate::leanh::LeanObject,
    mut v_all_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_4020_);
    return v_all_4020_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(
    mut v_motive_4021_: *mut crate::leanh::LeanObject,
    mut v_t_4022_: *mut crate::leanh::LeanObject,
    mut v_h_4023_: *mut crate::leanh::LeanObject,
    mut v_all_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4025_: u8 = 0;
    let mut v_res_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4025_ = (crate::leanh::lean_unbox(v_t_4022_) as u8);
    v_res_4026_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(
        v_motive_4021_,
        v_t_boxed_4025_,
        v_h_4023_,
        v_all_4024_,
    );
    crate::leanh::lean_dec(v_all_4024_);
    return v_res_4026_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(
    mut v_none_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_4027_);
    return v_none_4027_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(
    mut v_none_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_4028_);
    crate::leanh::lean_dec(v_none_4028_);
    return v_res_4029_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_none_elim(
    mut v_motive_4030_: *mut crate::leanh::LeanObject,
    mut v_t_4031_: u8,
    mut v_h_4032_: *mut crate::leanh::LeanObject,
    mut v_none_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_4033_);
    return v_none_4033_;
}
pub unsafe fn l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(
    mut v_motive_4034_: *mut crate::leanh::LeanObject,
    mut v_t_4035_: *mut crate::leanh::LeanObject,
    mut v_h_4036_: *mut crate::leanh::LeanObject,
    mut v_none_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4038_: u8 = 0;
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4038_ = (crate::leanh::lean_unbox(v_t_4035_) as u8);
    v_res_4039_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(
        v_motive_4034_,
        v_t_boxed_4038_,
        v_h_4036_,
        v_none_4037_,
    );
    crate::leanh::lean_dec(v_none_4037_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(
    mut v_t_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = crate::leanh::lean_box(0);
    v___x_4042_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4042_, 0, v_t_4040_);
    crate::leanh::lean_ctor_set(v___x_4042_, 1, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4042_, 2, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4042_, 3, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4042_, 4, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4042_, 5, v___x_4041_);
    v___x_4043_ = 0;
    v___x_4044_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4042_);
    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4044_, 2, v___x_4041_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4044_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4043_,
    );
    return v___x_4044_;
}
pub unsafe fn l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(
    mut v_s_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTryThisSuggestion_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageData_x3f_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suggestion_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut v_val_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTryThisSuggestion_4048_ = crate::leanh::lean_ctor_get(v_s_4047_, 0);
                crate::leanh::lean_inc_ref(v_toTryThisSuggestion_4048_);
                crate::leanh::lean_dec_ref(v_s_4047_);
                v_messageData_x3f_4049_ =
                    crate::leanh::lean_ctor_get(v_toTryThisSuggestion_4048_, 4);
                if crate::leanh::lean_obj_tag(v_messageData_x3f_4049_) == 0 {
                    v_suggestion_4050_ =
                        crate::leanh::lean_ctor_get(v_toTryThisSuggestion_4048_, 0);
                    crate::leanh::lean_inc_ref(v_suggestion_4050_);
                    crate::leanh::lean_dec_ref(v_toTryThisSuggestion_4048_);
                    if crate::leanh::lean_obj_tag(v_suggestion_4050_) == 0 {
                        v_a_4051_ = crate::leanh::lean_ctor_get(v_suggestion_4050_, 1);
                        crate::leanh::lean_inc(v_a_4051_);
                        crate::leanh::lean_dec_ref_known(v_suggestion_4050_, 2);
                        v___x_4052_ = l_Lean_MessageData_ofSyntax(v_a_4051_);
                        return v___x_4052_;
                    } else {
                        v_a_4053_ = crate::leanh::lean_ctor_get(v_suggestion_4050_, 0);
                        v_isSharedCheck_4061_ =
                            (!crate::leanh::lean_is_exclusive(v_suggestion_4050_)) as u8;
                        if v_isSharedCheck_4061_ == 0 {
                            v___x_4055_ = v_suggestion_4050_;
                            v_isShared_4056_ = v_isSharedCheck_4061_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4053_);
                            crate::leanh::lean_dec(v_suggestion_4050_);
                            v___x_4055_ = crate::leanh::lean_box(0);
                            v_isShared_4056_ = v_isSharedCheck_4061_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_messageData_x3f_4049_);
                    crate::leanh::lean_dec_ref(v_toTryThisSuggestion_4048_);
                    v_val_4062_ = crate::leanh::lean_ctor_get(v_messageData_x3f_4049_, 0);
                    crate::leanh::lean_inc(v_val_4062_);
                    crate::leanh::lean_dec_ref_known(v_messageData_x3f_4049_, 1);
                    return v_val_4062_;
                }
            }
            1 => {
                if v_isShared_4056_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4055_, 3);
                    v___x_4058_ = v___x_4055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4053_);
                    v___x_4058_ = v_reuseFailAlloc_4060_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4059_ = l_Lean_MessageData_ofFormat(v___x_4058_);
                return v___x_4059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(
    mut v_as_4065_: *mut crate::leanh::LeanObject,
    mut v_i_4066_: usize,
    mut v_stop_4067_: usize,
    mut v_b_4068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: usize = 0;
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4074_ = lean_usize_dec_eq(v_i_4066_, v_stop_4067_);
                if v___x_4074_ == 0 {
                    v___x_4075_ = lean_array_uget(v_as_4065_, v_i_4066_);
                    v_fst_4076_ = crate::leanh::lean_ctor_get(v___x_4075_, 0);
                    v_snd_4077_ = crate::leanh::lean_ctor_get(v___x_4075_, 1);
                    v_isSharedCheck_4114_ = (!crate::leanh::lean_is_exclusive(v___x_4075_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v___x_4079_ = v___x_4075_;
                        v_isShared_4080_ = v_isSharedCheck_4114_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4077_);
                        crate::leanh::lean_inc(v_fst_4076_);
                        crate::leanh::lean_dec(v___x_4075_);
                        v___x_4079_ = crate::leanh::lean_box(0);
                        v_isShared_4080_ = v_isSharedCheck_4114_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_4068_;
                }
            }
            1 => {
                v___x_4071_ = 1usize;
                v___x_4072_ = lean_usize_add(v_i_4066_, v___x_4071_);
                v_i_4066_ = v___x_4072_;
                v_b_4068_ = v___y_4070_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4081_ = lean_array_get_size(v_b_4068_);
                v___x_4082_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4083_ = lean_nat_dec_eq(v___x_4081_, v___x_4082_);
                if v___x_4083_ == 0 {
                    crate::leanh::lean_del_object(v___x_4079_);
                    v___x_4084_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4085_ = lean_nat_sub(v___x_4081_, v___x_4084_);
                    v___x_4086_ = lean_array_fget(v_b_4068_, v___x_4085_);
                    v_fst_4087_ = crate::leanh::lean_ctor_get(v___x_4086_, 0);
                    v_snd_4088_ = crate::leanh::lean_ctor_get(v___x_4086_, 1);
                    v_isSharedCheck_4106_ = (!crate::leanh::lean_is_exclusive(v___x_4086_)) as u8;
                    if v_isSharedCheck_4106_ == 0 {
                        v___x_4090_ = v___x_4086_;
                        v_isShared_4091_ = v_isSharedCheck_4106_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4088_);
                        crate::leanh::lean_inc(v_fst_4087_);
                        crate::leanh::lean_dec(v___x_4086_);
                        v___x_4090_ = crate::leanh::lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4106_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_4068_);
                    v___x_4107_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4108_ = lean_mk_empty_array_with_capacity(v___x_4107_);
                    crate::leanh::lean_inc_ref(v___x_4108_);
                    v___x_4109_ = lean_array_push(v___x_4108_, v_snd_4077_);
                    if v_isShared_4080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4079_, 1, v___x_4109_);
                        v___x_4111_ = v___x_4079_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_fst_4076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v___x_4109_);
                        v___x_4111_ = v_reuseFailAlloc_4113_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4092_ = (crate::leanh::lean_unbox(v_fst_4076_) as u8);
                v___x_4093_ = (crate::leanh::lean_unbox(v_fst_4087_) as u8);
                crate::leanh::lean_dec(v_fst_4087_);
                v___x_4094_ = l_Lean_Diff_instBEqAction_beq(v___x_4092_, v___x_4093_);
                if v___x_4094_ == 0 {
                    crate::leanh::lean_dec(v_snd_4088_);
                    crate::leanh::lean_dec(v___x_4085_);
                    v___x_4095_ = lean_mk_empty_array_with_capacity(v___x_4084_);
                    v___x_4096_ = lean_array_push(v___x_4095_, v_snd_4077_);
                    if v_isShared_4091_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4096_);
                        crate::leanh::lean_ctor_set(v___x_4090_, 0, v_fst_4076_);
                        v___x_4098_ = v___x_4090_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4100_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_fst_4076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4096_);
                        v___x_4098_ = v_reuseFailAlloc_4100_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4101_ = lean_array_push(v_snd_4088_, v_snd_4077_);
                    if v_isShared_4091_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4101_);
                        crate::leanh::lean_ctor_set(v___x_4090_, 0, v_fst_4076_);
                        v___x_4103_ = v___x_4090_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4105_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_fst_4076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4101_);
                        v___x_4103_ = v_reuseFailAlloc_4105_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4099_ = lean_array_push(v_b_4068_, v___x_4098_);
                v___y_4070_ = v___x_4099_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4104_ = lean_array_fset(v_b_4068_, v___x_4085_, v___x_4103_);
                crate::leanh::lean_dec(v___x_4085_);
                v___y_4070_ = v___x_4104_;
                state = 1;
                continue;
            }
            6 => {
                v___x_4112_ = lean_array_push(v___x_4108_, v___x_4111_);
                v___y_4070_ = v___x_4112_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(
    mut v_as_4115_: *mut crate::leanh::LeanObject,
    mut v_i_4116_: *mut crate::leanh::LeanObject,
    mut v_stop_4117_: *mut crate::leanh::LeanObject,
    mut v_b_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4119_: usize = 0;
    let mut v_stop_boxed_4120_: usize = 0;
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4119_ = crate::leanh::lean_unbox_usize(v_i_4116_);
    crate::leanh::lean_dec(v_i_4116_);
    v_stop_boxed_4120_ = crate::leanh::lean_unbox_usize(v_stop_4117_);
    crate::leanh::lean_dec(v_stop_4117_);
    v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_4115_, v_i_boxed_4119_, v_stop_boxed_4120_, v_b_4118_);
    crate::leanh::lean_dec_ref(v_as_4115_);
    return v_res_4121_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(
    mut v_ds_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: u8 = 0;
    v___x_4125_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4126_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0;
    v___x_4127_ = lean_array_get_size(v_ds_4124_);
    v___x_4128_ = lean_nat_dec_lt(v___x_4125_, v___x_4127_);
    if v___x_4128_ == 0 {
        return v___x_4126_;
    } else {
        let mut v___x_4129_: u8 = 0;
        v___x_4129_ = lean_nat_dec_le(v___x_4127_, v___x_4127_);
        if v___x_4129_ == 0 {
            if v___x_4128_ == 0 {
                return v___x_4126_;
            } else {
                let mut v___x_4130_: usize = 0;
                let mut v___x_4131_: usize = 0;
                let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4130_ = 0usize;
                v___x_4131_ = lean_usize_of_nat(v___x_4127_);
                v___x_4132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_4124_, v___x_4130_, v___x_4131_, v___x_4126_);
                return v___x_4132_;
            }
        } else {
            let mut v___x_4133_: usize = 0;
            let mut v___x_4134_: usize = 0;
            let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4133_ = 0usize;
            v___x_4134_ = lean_usize_of_nat(v___x_4127_);
            v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_4124_, v___x_4133_, v___x_4134_, v___x_4126_);
            return v___x_4135_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(
    mut v_ds_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4137_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_4136_);
    crate::leanh::lean_dec_ref(v_ds_4136_);
    return v_res_4137_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(
    mut v_00_u03b1_4138_: *mut crate::leanh::LeanObject,
    mut v_ds_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_4139_);
    return v___x_4140_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(
    mut v_00_u03b1_4141_: *mut crate::leanh::LeanObject,
    mut v_ds_4142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4143_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(
        v_00_u03b1_4141_,
        v_ds_4142_,
    );
    crate::leanh::lean_dec_ref(v_ds_4142_);
    return v_res_4143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(
    mut v_00_u03b1_4144_: *mut crate::leanh::LeanObject,
    mut v_as_4145_: *mut crate::leanh::LeanObject,
    mut v_i_4146_: usize,
    mut v_stop_4147_: usize,
    mut v_b_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_4145_, v_i_4146_, v_stop_4147_, v_b_4148_);
    return v___x_4149_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(
    mut v_00_u03b1_4150_: *mut crate::leanh::LeanObject,
    mut v_as_4151_: *mut crate::leanh::LeanObject,
    mut v_i_4152_: *mut crate::leanh::LeanObject,
    mut v_stop_4153_: *mut crate::leanh::LeanObject,
    mut v_b_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4155_: usize = 0;
    let mut v_stop_boxed_4156_: usize = 0;
    let mut v_res_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4155_ = crate::leanh::lean_unbox_usize(v_i_4152_);
    crate::leanh::lean_dec(v_i_4152_);
    v_stop_boxed_4156_ = crate::leanh::lean_unbox_usize(v_stop_4153_);
    crate::leanh::lean_dec(v_stop_4153_);
    v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_4150_, v_as_4151_, v_i_boxed_4155_, v_stop_boxed_4156_, v_b_4154_);
    crate::leanh::lean_dec_ref(v_as_4151_);
    return v_res_4157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(
    mut v_sz_4158_: usize,
    mut v_i_4159_: usize,
    mut v_bs_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4161_: u8 = 0;
    let mut v_v_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4167_: u8 = 0;
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: usize = 0;
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4161_ = lean_usize_dec_lt(v_i_4159_, v_sz_4158_);
                if v___x_4161_ == 0 {
                    return v_bs_4160_;
                } else {
                    v_v_4162_ = lean_array_uget(v_bs_4160_, v_i_4159_);
                    v_fst_4163_ = crate::leanh::lean_ctor_get(v_v_4162_, 0);
                    v_snd_4164_ = crate::leanh::lean_ctor_get(v_v_4162_, 1);
                    v_isSharedCheck_4179_ = (!crate::leanh::lean_is_exclusive(v_v_4162_)) as u8;
                    if v_isSharedCheck_4179_ == 0 {
                        v___x_4166_ = v_v_4162_;
                        v_isShared_4167_ = v_isSharedCheck_4179_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4164_);
                        crate::leanh::lean_inc(v_fst_4163_);
                        crate::leanh::lean_dec(v_v_4162_);
                        v___x_4166_ = crate::leanh::lean_box(0);
                        v_isShared_4167_ = v_isSharedCheck_4179_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4168_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4169_ = lean_array_uset(v_bs_4160_, v_i_4159_, v___x_4168_);
                v___x_4170_ = lean_array_to_list(v_snd_4164_);
                v___x_4171_ = lean_string_mk(v___x_4170_);
                if v_isShared_4167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4166_, 1, v___x_4171_);
                    v___x_4173_ = v___x_4166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_fst_4163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4171_);
                    v___x_4173_ = v_reuseFailAlloc_4178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4174_ = 1usize;
                v___x_4175_ = lean_usize_add(v_i_4159_, v___x_4174_);
                v___x_4176_ = lean_array_uset(v_bs_x27_4169_, v_i_4159_, v___x_4173_);
                v_i_4159_ = v___x_4175_;
                v_bs_4160_ = v___x_4176_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(
    mut v_sz_4180_: *mut crate::leanh::LeanObject,
    mut v_i_4181_: *mut crate::leanh::LeanObject,
    mut v_bs_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4183_: usize = 0;
    let mut v_i_boxed_4184_: usize = 0;
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4183_ = crate::leanh::lean_unbox_usize(v_sz_4180_);
    crate::leanh::lean_dec(v_sz_4180_);
    v_i_boxed_4184_ = crate::leanh::lean_unbox_usize(v_i_4181_);
    crate::leanh::lean_dec(v_i_4181_);
    v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_4183_, v_i_boxed_4184_, v_bs_4182_);
    return v_res_4185_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(
    mut v_d_4186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4188_: usize = 0;
    let mut v___x_4189_: usize = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4187_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_4186_);
    v_sz_4188_ = lean_array_size(v___x_4187_);
    v___x_4189_ = 0usize;
    v___x_4190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_4188_, v___x_4189_, v___x_4187_);
    return v___x_4190_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(
    mut v_d_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_4191_);
    crate::leanh::lean_dec_ref(v_d_4191_);
    return v_res_4192_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(
    mut v_sz_4193_: usize,
    mut v_i_4194_: usize,
    mut v_bs_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4196_: u8 = 0;
    let mut v_v_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: u8 = 0;
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: usize = 0;
    let mut v___x_4204_: usize = 0;
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4196_ = lean_usize_dec_lt(v_i_4194_, v_sz_4193_);
                if v___x_4196_ == 0 {
                    return v_bs_4195_;
                } else {
                    v_v_4197_ = lean_array_uget(v_bs_4195_, v_i_4194_);
                    v___x_4198_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4199_ = lean_array_uset(v_bs_4195_, v_i_4194_, v___x_4198_);
                    v___x_4200_ = 0;
                    v___x_4201_ = crate::leanh::lean_box((v___x_4200_) as usize);
                    v___x_4202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4202_, 0, v___x_4201_);
                    crate::leanh::lean_ctor_set(v___x_4202_, 1, v_v_4197_);
                    v___x_4203_ = 1usize;
                    v___x_4204_ = lean_usize_add(v_i_4194_, v___x_4203_);
                    v___x_4205_ = lean_array_uset(v_bs_x27_4199_, v_i_4194_, v___x_4202_);
                    v_i_4194_ = v___x_4204_;
                    v_bs_4195_ = v___x_4205_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(
    mut v_sz_4207_: *mut crate::leanh::LeanObject,
    mut v_i_4208_: *mut crate::leanh::LeanObject,
    mut v_bs_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4210_: usize = 0;
    let mut v_i_boxed_4211_: usize = 0;
    let mut v_res_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4210_ = crate::leanh::lean_unbox_usize(v_sz_4207_);
    crate::leanh::lean_dec(v_sz_4207_);
    v_i_boxed_4211_ = crate::leanh::lean_unbox_usize(v_i_4208_);
    crate::leanh::lean_dec(v_i_4208_);
    v_res_4212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_4210_, v_i_boxed_4211_, v_bs_4209_);
    return v_res_4212_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(
    mut v___x_4213_: *mut crate::leanh::LeanObject,
    mut v_original_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4216_ = crate::leanh::lean_ctor_get(v_a_4215_, 0);
                v_snd_4217_ = crate::leanh::lean_ctor_get(v_a_4215_, 1);
                v_isSharedCheck_4236_ = (!crate::leanh::lean_is_exclusive(v_a_4215_)) as u8;
                if v_isSharedCheck_4236_ == 0 {
                    v___x_4219_ = v_a_4215_;
                    v_isShared_4220_ = v_isSharedCheck_4236_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4217_);
                    crate::leanh::lean_inc(v_fst_4216_);
                    crate::leanh::lean_dec(v_a_4215_);
                    v___x_4219_ = crate::leanh::lean_box(0);
                    v_isShared_4220_ = v_isSharedCheck_4236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4221_ = lean_nat_dec_lt(v_snd_4217_, v___x_4213_);
                if v___x_4221_ == 0 {
                    if v_isShared_4220_ == 0 {
                        v___x_4223_ = v___x_4219_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_fst_4216_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_snd_4217_);
                        v___x_4223_ = v_reuseFailAlloc_4224_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4225_ = 1;
                    v___x_4226_ = lean_array_fget_borrowed(v_original_4214_, v_snd_4217_);
                    v___x_4227_ = crate::leanh::lean_box((v___x_4225_) as usize);
                    crate::leanh::lean_inc(v___x_4226_);
                    if v_isShared_4220_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4219_, 1, v___x_4226_);
                        crate::leanh::lean_ctor_set(v___x_4219_, 0, v___x_4227_);
                        v___x_4229_ = v___x_4219_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___x_4226_);
                        v___x_4229_ = v_reuseFailAlloc_4235_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4223_;
            }
            3 => {
                v___x_4230_ = lean_array_push(v_fst_4216_, v___x_4229_);
                v___x_4231_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4232_ = lean_nat_add(v_snd_4217_, v___x_4231_);
                crate::leanh::lean_dec(v_snd_4217_);
                v___x_4233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4233_, 0, v___x_4230_);
                crate::leanh::lean_ctor_set(v___x_4233_, 1, v___x_4232_);
                v_a_4215_ = v___x_4233_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(
    mut v___x_4237_: *mut crate::leanh::LeanObject,
    mut v_original_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_4237_, v_original_4238_, v_a_4239_);
    crate::leanh::lean_dec_ref(v_original_4238_);
    crate::leanh::lean_dec(v___x_4237_);
    return v_res_4240_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(
    mut v___x_4241_: *mut crate::leanh::LeanObject,
    mut v_edited_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4244_ = crate::leanh::lean_ctor_get(v_a_4243_, 0);
                v_snd_4245_ = crate::leanh::lean_ctor_get(v_a_4243_, 1);
                v_isSharedCheck_4264_ = (!crate::leanh::lean_is_exclusive(v_a_4243_)) as u8;
                if v_isSharedCheck_4264_ == 0 {
                    v___x_4247_ = v_a_4243_;
                    v_isShared_4248_ = v_isSharedCheck_4264_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4245_);
                    crate::leanh::lean_inc(v_fst_4244_);
                    crate::leanh::lean_dec(v_a_4243_);
                    v___x_4247_ = crate::leanh::lean_box(0);
                    v_isShared_4248_ = v_isSharedCheck_4264_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4249_ = lean_nat_dec_lt(v_snd_4245_, v___x_4241_);
                if v___x_4249_ == 0 {
                    if v_isShared_4248_ == 0 {
                        v___x_4251_ = v___x_4247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_fst_4244_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_snd_4245_);
                        v___x_4251_ = v_reuseFailAlloc_4252_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4253_ = 0;
                    v___x_4254_ = lean_array_fget_borrowed(v_edited_4242_, v_snd_4245_);
                    v___x_4255_ = crate::leanh::lean_box((v___x_4253_) as usize);
                    crate::leanh::lean_inc(v___x_4254_);
                    if v_isShared_4248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4247_, 1, v___x_4254_);
                        crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4255_);
                        v___x_4257_ = v___x_4247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4263_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4255_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4263_, 1, v___x_4254_);
                        v___x_4257_ = v_reuseFailAlloc_4263_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4251_;
            }
            3 => {
                v___x_4258_ = lean_array_push(v_fst_4244_, v___x_4257_);
                v___x_4259_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4260_ = lean_nat_add(v_snd_4245_, v___x_4259_);
                crate::leanh::lean_dec(v_snd_4245_);
                v___x_4261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4261_, 0, v___x_4258_);
                crate::leanh::lean_ctor_set(v___x_4261_, 1, v___x_4260_);
                v_a_4243_ = v___x_4261_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(
    mut v___x_4265_: *mut crate::leanh::LeanObject,
    mut v_edited_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_4265_, v_edited_4266_, v_a_4267_);
    crate::leanh::lean_dec_ref(v_edited_4266_);
    crate::leanh::lean_dec(v___x_4265_);
    return v_res_4268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(
    mut v_a_4269_: u32,
    mut v_x_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u32 = 0;
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4270_) == 0 {
                    v___x_4271_ = crate::leanh::lean_box(0);
                    return v___x_4271_;
                } else {
                    v_key_4272_ = crate::leanh::lean_ctor_get(v_x_4270_, 0);
                    v_value_4273_ = crate::leanh::lean_ctor_get(v_x_4270_, 1);
                    v_tail_4274_ = crate::leanh::lean_ctor_get(v_x_4270_, 2);
                    v___x_4275_ = crate::leanh::lean_unbox_uint32(v_key_4272_);
                    v___x_4276_ = lean_uint32_dec_eq(v___x_4275_, v_a_4269_);
                    if v___x_4276_ == 0 {
                        v_x_4270_ = v_tail_4274_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4273_);
                        v___x_4278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4278_, 0, v_value_4273_);
                        return v___x_4278_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg___boxed(
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4281_: u32 = 0;
    let mut v_res_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4281_ = crate::leanh::lean_unbox_uint32(v_a_4279_);
    crate::leanh::lean_dec(v_a_4279_);
    v_res_4282_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_boxed_4281_, v_x_4280_);
    crate::leanh::lean_dec(v_x_4280_);
    return v_res_4282_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(
    mut v_m_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u64 = 0;
    let mut v___x_4288_: u64 = 0;
    let mut v___x_4289_: u64 = 0;
    let mut v_fold_4290_: u64 = 0;
    let mut v___x_4291_: u64 = 0;
    let mut v___x_4292_: u64 = 0;
    let mut v___x_4293_: u64 = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: usize = 0;
    let mut v___x_4296_: usize = 0;
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: usize = 0;
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4285_ = crate::leanh::lean_ctor_get(v_m_4283_, 1);
    v___x_4286_ = lean_array_get_size(v_buckets_4285_);
    v___x_4287_ = lean_uint32_to_uint64(v_a_4284_);
    v___x_4288_ = 32u64;
    v___x_4289_ = lean_uint64_shift_right(v___x_4287_, v___x_4288_);
    v_fold_4290_ = lean_uint64_xor(v___x_4287_, v___x_4289_);
    v___x_4291_ = 16u64;
    v___x_4292_ = lean_uint64_shift_right(v_fold_4290_, v___x_4291_);
    v___x_4293_ = lean_uint64_xor(v_fold_4290_, v___x_4292_);
    v___x_4294_ = lean_uint64_to_usize(v___x_4293_);
    v___x_4295_ = lean_usize_of_nat(v___x_4286_);
    v___x_4296_ = 1usize;
    v___x_4297_ = lean_usize_sub(v___x_4295_, v___x_4296_);
    v___x_4298_ = lean_usize_land(v___x_4294_, v___x_4297_);
    v___x_4299_ = lean_array_uget_borrowed(v_buckets_4285_, v___x_4298_);
    v___x_4300_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_4284_, v___x_4299_);
    return v___x_4300_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg___boxed(
    mut v_m_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4303_: u32 = 0;
    let mut v_res_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4303_ = crate::leanh::lean_unbox_uint32(v_a_4302_);
    crate::leanh::lean_dec(v_a_4302_);
    v_res_4304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_4301_, v_a_boxed_4303_);
    crate::leanh::lean_dec_ref(v_m_4301_);
    return v_res_4304_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(
    mut v_a_4305_: u32,
    mut v_x_4306_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4307_: u8 = 0;
    let mut v_key_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u32 = 0;
    let mut v___x_4311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4306_) == 0 {
                    v___x_4307_ = 0;
                    return v___x_4307_;
                } else {
                    v_key_4308_ = crate::leanh::lean_ctor_get(v_x_4306_, 0);
                    v_tail_4309_ = crate::leanh::lean_ctor_get(v_x_4306_, 2);
                    v___x_4310_ = crate::leanh::lean_unbox_uint32(v_key_4308_);
                    v___x_4311_ = lean_uint32_dec_eq(v___x_4310_, v_a_4305_);
                    if v___x_4311_ == 0 {
                        v_x_4306_ = v_tail_4309_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4311_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg___boxed(
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_x_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4315_: u32 = 0;
    let mut v_res_4316_: u8 = 0;
    let mut v_r_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4315_ = crate::leanh::lean_unbox_uint32(v_a_4313_);
    crate::leanh::lean_dec(v_a_4313_);
    v_res_4316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_boxed_4315_, v_x_4314_);
    crate::leanh::lean_dec(v_x_4314_);
    v_r_4317_ = crate::leanh::lean_box((v_res_4316_) as usize);
    return v_r_4317_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(
    mut v_a_4318_: u32,
    mut v_b_4319_: *mut crate::leanh::LeanObject,
    mut v_x_4320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4327_: u32 = 0;
    let mut v___x_4328_: u8 = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4320_) == 0 {
                    crate::leanh::lean_dec(v_b_4319_);
                    return v_x_4320_;
                } else {
                    v_key_4321_ = crate::leanh::lean_ctor_get(v_x_4320_, 0);
                    v_value_4322_ = crate::leanh::lean_ctor_get(v_x_4320_, 1);
                    v_tail_4323_ = crate::leanh::lean_ctor_get(v_x_4320_, 2);
                    v_isSharedCheck_4337_ = (!crate::leanh::lean_is_exclusive(v_x_4320_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4325_ = v_x_4320_;
                        v_isShared_4326_ = v_isSharedCheck_4337_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4323_);
                        crate::leanh::lean_inc(v_value_4322_);
                        crate::leanh::lean_inc(v_key_4321_);
                        crate::leanh::lean_dec(v_x_4320_);
                        v___x_4325_ = crate::leanh::lean_box(0);
                        v_isShared_4326_ = v_isSharedCheck_4337_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4327_ = crate::leanh::lean_unbox_uint32(v_key_4321_);
                v___x_4328_ = lean_uint32_dec_eq(v___x_4327_, v_a_4318_);
                if v___x_4328_ == 0 {
                    v___x_4329_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_4318_, v_b_4319_, v_tail_4323_);
                    if v_isShared_4326_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4325_, 2, v___x_4329_);
                        v___x_4331_ = v___x_4325_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_key_4321_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_value_4322_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 2, v___x_4329_);
                        v___x_4331_ = v_reuseFailAlloc_4332_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4322_);
                    crate::leanh::lean_dec(v_key_4321_);
                    v___x_4333_ = crate::leanh::lean_box_uint32(v_a_4318_);
                    if v_isShared_4326_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4325_, 1, v_b_4319_);
                        crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4333_);
                        v___x_4335_ = v___x_4325_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_b_4319_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_tail_4323_);
                        v___x_4335_ = v_reuseFailAlloc_4336_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4331_;
            }
            3 => {
                return v___x_4335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg___boxed(
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_b_4339_: *mut crate::leanh::LeanObject,
    mut v_x_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4341_: u32 = 0;
    let mut v_res_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4341_ = crate::leanh::lean_unbox_uint32(v_a_4338_);
    crate::leanh::lean_dec(v_a_4338_);
    v_res_4342_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_boxed_4341_, v_b_4339_, v_x_4340_);
    return v_res_4342_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(
    mut v_x_4343_: *mut crate::leanh::LeanObject,
    mut v_x_4344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: u32 = 0;
    let mut v___x_4353_: u64 = 0;
    let mut v___x_4354_: u64 = 0;
    let mut v___x_4355_: u64 = 0;
    let mut v_fold_4356_: u64 = 0;
    let mut v___x_4357_: u64 = 0;
    let mut v___x_4358_: u64 = 0;
    let mut v___x_4359_: u64 = 0;
    let mut v___x_4360_: usize = 0;
    let mut v___x_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v___x_4363_: usize = 0;
    let mut v___x_4364_: usize = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4344_) == 0 {
                    return v_x_4343_;
                } else {
                    v_key_4345_ = crate::leanh::lean_ctor_get(v_x_4344_, 0);
                    v_value_4346_ = crate::leanh::lean_ctor_get(v_x_4344_, 1);
                    v_tail_4347_ = crate::leanh::lean_ctor_get(v_x_4344_, 2);
                    v_isSharedCheck_4371_ = (!crate::leanh::lean_is_exclusive(v_x_4344_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4349_ = v_x_4344_;
                        v_isShared_4350_ = v_isSharedCheck_4371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4347_);
                        crate::leanh::lean_inc(v_value_4346_);
                        crate::leanh::lean_inc(v_key_4345_);
                        crate::leanh::lean_dec(v_x_4344_);
                        v___x_4349_ = crate::leanh::lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4351_ = lean_array_get_size(v_x_4343_);
                v___x_4352_ = crate::leanh::lean_unbox_uint32(v_key_4345_);
                v___x_4353_ = lean_uint32_to_uint64(v___x_4352_);
                v___x_4354_ = 32u64;
                v___x_4355_ = lean_uint64_shift_right(v___x_4353_, v___x_4354_);
                v_fold_4356_ = lean_uint64_xor(v___x_4353_, v___x_4355_);
                v___x_4357_ = 16u64;
                v___x_4358_ = lean_uint64_shift_right(v_fold_4356_, v___x_4357_);
                v___x_4359_ = lean_uint64_xor(v_fold_4356_, v___x_4358_);
                v___x_4360_ = lean_uint64_to_usize(v___x_4359_);
                v___x_4361_ = lean_usize_of_nat(v___x_4351_);
                v___x_4362_ = 1usize;
                v___x_4363_ = lean_usize_sub(v___x_4361_, v___x_4362_);
                v___x_4364_ = lean_usize_land(v___x_4360_, v___x_4363_);
                v___x_4365_ = lean_array_uget_borrowed(v_x_4343_, v___x_4364_);
                crate::leanh::lean_inc(v___x_4365_);
                if v_isShared_4350_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4349_, 2, v___x_4365_);
                    v___x_4367_ = v___x_4349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_key_4345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_value_4346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 2, v___x_4365_);
                    v___x_4367_ = v_reuseFailAlloc_4370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4368_ = lean_array_uset(v_x_4343_, v___x_4364_, v___x_4367_);
                v_x_4343_ = v___x_4368_;
                v_x_4344_ = v_tail_4347_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(
    mut v_i_4372_: *mut crate::leanh::LeanObject,
    mut v_source_4373_: *mut crate::leanh::LeanObject,
    mut v_target_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v_es_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4375_ = lean_array_get_size(v_source_4373_);
                v___x_4376_ = lean_nat_dec_lt(v_i_4372_, v___x_4375_);
                if v___x_4376_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4373_);
                    crate::leanh::lean_dec(v_i_4372_);
                    return v_target_4374_;
                } else {
                    v_es_4377_ = lean_array_fget(v_source_4373_, v_i_4372_);
                    v___x_4378_ = crate::leanh::lean_box(0);
                    v_source_4379_ = lean_array_fset(v_source_4373_, v_i_4372_, v___x_4378_);
                    v_target_4380_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_target_4374_, v_es_4377_);
                    v___x_4381_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4382_ = lean_nat_add(v_i_4372_, v___x_4381_);
                    crate::leanh::lean_dec(v_i_4372_);
                    v_i_4372_ = v___x_4382_;
                    v_source_4373_ = v_source_4379_;
                    v_target_4374_ = v_target_4380_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(
    mut v_data_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4385_ = lean_array_get_size(v_data_4384_);
    v___x_4386_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4387_ = lean_nat_mul(v___x_4385_, v___x_4386_);
    v___x_4388_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4389_ = crate::leanh::lean_box(0);
    v___x_4390_ = lean_mk_array(v_nbuckets_4387_, v___x_4389_);
    v___x_4391_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v___x_4388_, v_data_4384_, v___x_4390_);
    return v___x_4391_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(
    mut v_m_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: u32,
    mut v_b_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: u64 = 0;
    let mut v___x_4402_: u64 = 0;
    let mut v___x_4403_: u64 = 0;
    let mut v_fold_4404_: u64 = 0;
    let mut v___x_4405_: u64 = 0;
    let mut v___x_4406_: u64 = 0;
    let mut v___x_4407_: u64 = 0;
    let mut v___x_4408_: usize = 0;
    let mut v___x_4409_: usize = 0;
    let mut v___x_4410_: usize = 0;
    let mut v___x_4411_: usize = 0;
    let mut v___x_4412_: usize = 0;
    let mut v_bkt_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v_val_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4395_ = crate::leanh::lean_ctor_get(v_m_4392_, 0);
                v_buckets_4396_ = crate::leanh::lean_ctor_get(v_m_4392_, 1);
                v_isSharedCheck_4440_ = (!crate::leanh::lean_is_exclusive(v_m_4392_)) as u8;
                if v_isSharedCheck_4440_ == 0 {
                    v___x_4398_ = v_m_4392_;
                    v_isShared_4399_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4396_);
                    crate::leanh::lean_inc(v_size_4395_);
                    crate::leanh::lean_dec(v_m_4392_);
                    v___x_4398_ = crate::leanh::lean_box(0);
                    v_isShared_4399_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4400_ = lean_array_get_size(v_buckets_4396_);
                v___x_4401_ = lean_uint32_to_uint64(v_a_4393_);
                v___x_4402_ = 32u64;
                v___x_4403_ = lean_uint64_shift_right(v___x_4401_, v___x_4402_);
                v_fold_4404_ = lean_uint64_xor(v___x_4401_, v___x_4403_);
                v___x_4405_ = 16u64;
                v___x_4406_ = lean_uint64_shift_right(v_fold_4404_, v___x_4405_);
                v___x_4407_ = lean_uint64_xor(v_fold_4404_, v___x_4406_);
                v___x_4408_ = lean_uint64_to_usize(v___x_4407_);
                v___x_4409_ = lean_usize_of_nat(v___x_4400_);
                v___x_4410_ = 1usize;
                v___x_4411_ = lean_usize_sub(v___x_4409_, v___x_4410_);
                v___x_4412_ = lean_usize_land(v___x_4408_, v___x_4411_);
                v_bkt_4413_ = lean_array_uget_borrowed(v_buckets_4396_, v___x_4412_);
                v___x_4414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_4393_, v_bkt_4413_);
                if v___x_4414_ == 0 {
                    v___x_4415_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4416_ = lean_nat_add(v_size_4395_, v___x_4415_);
                    crate::leanh::lean_dec(v_size_4395_);
                    v___x_4417_ = crate::leanh::lean_box_uint32(v_a_4393_);
                    crate::leanh::lean_inc(v_bkt_4413_);
                    v___x_4418_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4417_);
                    crate::leanh::lean_ctor_set(v___x_4418_, 1, v_b_4394_);
                    crate::leanh::lean_ctor_set(v___x_4418_, 2, v_bkt_4413_);
                    v_buckets_x27_4419_ =
                        lean_array_uset(v_buckets_4396_, v___x_4412_, v___x_4418_);
                    v___x_4420_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4421_ = lean_nat_mul(v_size_x27_4416_, v___x_4420_);
                    v___x_4422_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4423_ = lean_nat_div(v___x_4421_, v___x_4422_);
                    crate::leanh::lean_dec(v___x_4421_);
                    v___x_4424_ = lean_array_get_size(v_buckets_x27_4419_);
                    v___x_4425_ = lean_nat_dec_le(v___x_4423_, v___x_4424_);
                    crate::leanh::lean_dec(v___x_4423_);
                    if v___x_4425_ == 0 {
                        v_val_4426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_buckets_x27_4419_);
                        if v_isShared_4399_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4398_, 1, v_val_4426_);
                            crate::leanh::lean_ctor_set(v___x_4398_, 0, v_size_x27_4416_);
                            v___x_4428_ = v___x_4398_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4429_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4429_,
                                0,
                                v_size_x27_4416_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_val_4426_);
                            v___x_4428_ = v_reuseFailAlloc_4429_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4399_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4398_, 1, v_buckets_x27_4419_);
                            crate::leanh::lean_ctor_set(v___x_4398_, 0, v_size_x27_4416_);
                            v___x_4431_ = v___x_4398_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4432_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4432_,
                                0,
                                v_size_x27_4416_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4432_,
                                1,
                                v_buckets_x27_4419_,
                            );
                            v___x_4431_ = v_reuseFailAlloc_4432_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4413_);
                    v___x_4433_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4434_ =
                        lean_array_uset(v_buckets_4396_, v___x_4412_, v___x_4433_);
                    v___x_4435_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_4393_, v_b_4394_, v_bkt_4413_);
                    v___x_4436_ = lean_array_uset(v_buckets_x27_4434_, v___x_4412_, v___x_4435_);
                    if v_isShared_4399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4398_, 1, v___x_4436_);
                        v___x_4438_ = v___x_4398_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_size_4395_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4436_);
                        v___x_4438_ = v_reuseFailAlloc_4439_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4428_;
            }
            3 => {
                return v___x_4431_;
            }
            4 => {
                return v___x_4438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg___boxed(
    mut v_m_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
    mut v_b_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4444_: u32 = 0;
    let mut v_res_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4444_ = crate::leanh::lean_unbox_uint32(v_a_4442_);
    crate::leanh::lean_dec(v_a_4442_);
    v_res_4445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_4441_, v_a_boxed_4444_, v_b_4443_);
    return v_res_4445_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(
    mut v_histogram_4446_: *mut crate::leanh::LeanObject,
    mut v_index_4447_: *mut crate::leanh::LeanObject,
    mut v_val_4448_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4459_: u8 = 0;
    let mut v_leftCount_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut v_unused_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_4446_, v_val_4448_);
                if crate::leanh::lean_obj_tag(v___x_4449_) == 0 {
                    v___x_4450_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4451_ = crate::leanh::lean_box(0);
                    v___x_4452_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4453_, 0, v_index_4447_);
                    v___x_4454_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4450_);
                    crate::leanh::lean_ctor_set(v___x_4454_, 1, v___x_4451_);
                    crate::leanh::lean_ctor_set(v___x_4454_, 2, v___x_4452_);
                    crate::leanh::lean_ctor_set(v___x_4454_, 3, v___x_4453_);
                    v___x_4455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_4446_, v_val_4448_, v___x_4454_);
                    return v___x_4455_;
                } else {
                    v_val_4456_ = crate::leanh::lean_ctor_get(v___x_4449_, 0);
                    v_isSharedCheck_4477_ = (!crate::leanh::lean_is_exclusive(v___x_4449_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4458_ = v___x_4449_;
                        v_isShared_4459_ = v_isSharedCheck_4477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4456_);
                        crate::leanh::lean_dec(v___x_4449_);
                        v___x_4458_ = crate::leanh::lean_box(0);
                        v_isShared_4459_ = v_isSharedCheck_4477_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_4460_ = crate::leanh::lean_ctor_get(v_val_4456_, 0);
                v_leftIndex_4461_ = crate::leanh::lean_ctor_get(v_val_4456_, 1);
                v_isSharedCheck_4474_ = (!crate::leanh::lean_is_exclusive(v_val_4456_)) as u8;
                if v_isSharedCheck_4474_ == 0 {
                    v_unused_4475_ = crate::leanh::lean_ctor_get(v_val_4456_, 3);
                    crate::leanh::lean_dec(v_unused_4475_);
                    v_unused_4476_ = crate::leanh::lean_ctor_get(v_val_4456_, 2);
                    crate::leanh::lean_dec(v_unused_4476_);
                    v___x_4463_ = v_val_4456_;
                    v_isShared_4464_ = v_isSharedCheck_4474_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_leftIndex_4461_);
                    crate::leanh::lean_inc(v_leftCount_4460_);
                    crate::leanh::lean_dec(v_val_4456_);
                    v___x_4463_ = crate::leanh::lean_box(0);
                    v_isShared_4464_ = v_isSharedCheck_4474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4465_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4466_ = lean_nat_add(v_leftCount_4460_, v___x_4465_);
                if v_isShared_4459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4458_, 0, v_index_4447_);
                    v___x_4468_ = v___x_4458_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_index_4447_);
                    v___x_4468_ = v_reuseFailAlloc_4473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4463_, 3, v___x_4468_);
                    crate::leanh::lean_ctor_set(v___x_4463_, 2, v___x_4466_);
                    v___x_4470_ = v___x_4463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_leftCount_4460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_leftIndex_4461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 2, v___x_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 3, v___x_4468_);
                    v___x_4470_ = v_reuseFailAlloc_4472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_4446_, v_val_4448_, v___x_4470_);
                return v___x_4471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(
    mut v_histogram_4478_: *mut crate::leanh::LeanObject,
    mut v_index_4479_: *mut crate::leanh::LeanObject,
    mut v_val_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_4481_: u32 = 0;
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4481_ = crate::leanh::lean_unbox_uint32(v_val_4480_);
    crate::leanh::lean_dec(v_val_4480_);
    v_res_4482_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_4478_, v_index_4479_, v_val_boxed_4481_);
    return v_res_4482_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(
    mut v_upperBound_4483_: *mut crate::leanh::LeanObject,
    mut v___x_4484_: *mut crate::leanh::LeanObject,
    mut v_fst_4485_: *mut crate::leanh::LeanObject,
    mut v___x_4486_: *mut crate::leanh::LeanObject,
    mut v_a_4487_: *mut crate::leanh::LeanObject,
    mut v_b_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: u32 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4489_ = lean_nat_dec_lt(v_a_4487_, v_upperBound_4483_);
                if v___x_4489_ == 0 {
                    crate::leanh::lean_dec(v_a_4487_);
                    return v_b_4488_;
                } else {
                    v___x_4490_ = l_Subarray_get___redArg(v_fst_4485_, v_a_4487_);
                    v___x_4491_ = crate::leanh::lean_unbox_uint32(v___x_4490_);
                    crate::leanh::lean_dec(v___x_4490_);
                    crate::leanh::lean_inc(v_a_4487_);
                    v___x_4492_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_b_4488_, v_a_4487_, v___x_4491_);
                    v___x_4493_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4494_ = lean_nat_add(v_a_4487_, v___x_4493_);
                    crate::leanh::lean_dec(v_a_4487_);
                    v_a_4487_ = v___x_4494_;
                    v_b_4488_ = v___x_4492_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(
    mut v_upperBound_4496_: *mut crate::leanh::LeanObject,
    mut v___x_4497_: *mut crate::leanh::LeanObject,
    mut v_fst_4498_: *mut crate::leanh::LeanObject,
    mut v___x_4499_: *mut crate::leanh::LeanObject,
    mut v_a_4500_: *mut crate::leanh::LeanObject,
    mut v_b_4501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_4496_, v___x_4497_, v_fst_4498_, v___x_4499_, v_a_4500_, v_b_4501_);
    crate::leanh::lean_dec(v___x_4499_);
    crate::leanh::lean_dec_ref(v_fst_4498_);
    crate::leanh::lean_dec(v___x_4497_);
    crate::leanh::lean_dec(v_upperBound_4496_);
    return v_res_4502_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(
    mut v_as_x27_4503_: *mut crate::leanh::LeanObject,
    mut v_b_4504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftCount_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftCount_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4531_: u8 = 0;
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4537_: u8 = 0;
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_unused_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4549_: u8 = 0;
    let mut v_unused_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4503_) == 0 {
                    return v_b_4504_;
                } else {
                    v_head_4505_ = crate::leanh::lean_ctor_get(v_as_x27_4503_, 0);
                    v_snd_4506_ = crate::leanh::lean_ctor_get(v_head_4505_, 1);
                    v_leftIndex_4507_ = crate::leanh::lean_ctor_get(v_snd_4506_, 1);
                    if crate::leanh::lean_obj_tag(v_leftIndex_4507_) == 1 {
                        v_rightIndex_4508_ = crate::leanh::lean_ctor_get(v_snd_4506_, 3);
                        if crate::leanh::lean_obj_tag(v_rightIndex_4508_) == 1 {
                            if crate::leanh::lean_obj_tag(v_b_4504_) == 0 {
                                v_tail_4509_ = crate::leanh::lean_ctor_get(v_as_x27_4503_, 1);
                                v_fst_4510_ = crate::leanh::lean_ctor_get(v_head_4505_, 0);
                                v_leftCount_4511_ = crate::leanh::lean_ctor_get(v_snd_4506_, 0);
                                v_rightCount_4512_ = crate::leanh::lean_ctor_get(v_snd_4506_, 2);
                                v_val_4513_ = crate::leanh::lean_ctor_get(v_leftIndex_4507_, 0);
                                v_val_4514_ = crate::leanh::lean_ctor_get(v_rightIndex_4508_, 0);
                                v___x_4515_ = lean_nat_add(v_leftCount_4511_, v_rightCount_4512_);
                                crate::leanh::lean_inc(v_val_4514_);
                                crate::leanh::lean_inc(v_val_4513_);
                                v___x_4516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4516_, 0, v_val_4513_);
                                crate::leanh::lean_ctor_set(v___x_4516_, 1, v_val_4514_);
                                crate::leanh::lean_inc(v_fst_4510_);
                                v___x_4517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4517_, 0, v_fst_4510_);
                                crate::leanh::lean_ctor_set(v___x_4517_, 1, v___x_4516_);
                                v___x_4518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4515_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 1, v___x_4517_);
                                v___x_4519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4519_, 0, v___x_4518_);
                                v_as_x27_4503_ = v_tail_4509_;
                                v_b_4504_ = v___x_4519_;
                                state = 0;
                                continue;
                            } else {
                                v_val_4521_ = crate::leanh::lean_ctor_get(v_b_4504_, 0);
                                crate::leanh::lean_inc(v_val_4521_);
                                v_tail_4522_ = crate::leanh::lean_ctor_get(v_as_x27_4503_, 1);
                                v_fst_4523_ = crate::leanh::lean_ctor_get(v_head_4505_, 0);
                                v_leftCount_4524_ = crate::leanh::lean_ctor_get(v_snd_4506_, 0);
                                v_rightCount_4525_ = crate::leanh::lean_ctor_get(v_snd_4506_, 2);
                                v_val_4526_ = crate::leanh::lean_ctor_get(v_leftIndex_4507_, 0);
                                v_val_4527_ = crate::leanh::lean_ctor_get(v_rightIndex_4508_, 0);
                                v_fst_4528_ = crate::leanh::lean_ctor_get(v_val_4521_, 0);
                                v_isSharedCheck_4549_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_4521_)) as u8;
                                if v_isSharedCheck_4549_ == 0 {
                                    v_unused_4550_ = crate::leanh::lean_ctor_get(v_val_4521_, 1);
                                    crate::leanh::lean_dec(v_unused_4550_);
                                    v___x_4530_ = v_val_4521_;
                                    v_isShared_4531_ = v_isSharedCheck_4549_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fst_4528_);
                                    crate::leanh::lean_dec(v_val_4521_);
                                    v___x_4530_ = crate::leanh::lean_box(0);
                                    v_isShared_4531_ = v_isSharedCheck_4549_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_tail_4551_ = crate::leanh::lean_ctor_get(v_as_x27_4503_, 1);
                            v_as_x27_4503_ = v_tail_4551_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_4553_ = crate::leanh::lean_ctor_get(v_as_x27_4503_, 1);
                        v_as_x27_4503_ = v_tail_4553_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4532_ = lean_nat_add(v_leftCount_4524_, v_rightCount_4525_);
                v___x_4533_ = lean_nat_dec_lt(v___x_4532_, v_fst_4528_);
                crate::leanh::lean_dec(v_fst_4528_);
                if v___x_4533_ == 0 {
                    crate::leanh::lean_dec(v___x_4532_);
                    crate::leanh::lean_del_object(v___x_4530_);
                    v_as_x27_4503_ = v_tail_4522_;
                    state = 0;
                    continue;
                } else {
                    v_isSharedCheck_4547_ = (!crate::leanh::lean_is_exclusive(v_b_4504_)) as u8;
                    if v_isSharedCheck_4547_ == 0 {
                        v_unused_4548_ = crate::leanh::lean_ctor_get(v_b_4504_, 0);
                        crate::leanh::lean_dec(v_unused_4548_);
                        v___x_4536_ = v_b_4504_;
                        v_isShared_4537_ = v_isSharedCheck_4547_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_4504_);
                        v___x_4536_ = crate::leanh::lean_box(0);
                        v_isShared_4537_ = v_isSharedCheck_4547_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_val_4527_);
                crate::leanh::lean_inc(v_val_4526_);
                if v_isShared_4531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4530_, 1, v_val_4527_);
                    crate::leanh::lean_ctor_set(v___x_4530_, 0, v_val_4526_);
                    v___x_4539_ = v___x_4530_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_val_4526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_val_4527_);
                    v___x_4539_ = v_reuseFailAlloc_4546_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_fst_4523_);
                v___x_4540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4540_, 0, v_fst_4523_);
                crate::leanh::lean_ctor_set(v___x_4540_, 1, v___x_4539_);
                v___x_4541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4541_, 0, v___x_4532_);
                crate::leanh::lean_ctor_set(v___x_4541_, 1, v___x_4540_);
                if v_isShared_4537_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4536_, 0, v___x_4541_);
                    v___x_4543_ = v___x_4536_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4541_);
                    v___x_4543_ = v_reuseFailAlloc_4545_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_as_x27_4503_ = v_tail_4522_;
                v_b_4504_ = v___x_4543_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_as_x27_4555_: *mut crate::leanh::LeanObject,
    mut v_b_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4557_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_4555_, v_b_4556_);
    crate::leanh::lean_dec(v_as_x27_4555_);
    return v_res_4557_;
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(
    mut v_left_4558_: *mut crate::leanh::LeanObject,
    mut v_right_4559_: *mut crate::leanh::LeanObject,
    mut v_pref_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut v_start_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u32 = 0;
    let mut v___x_4578_: u32 = 0;
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_4561_ = crate::leanh::lean_ctor_get(v_left_4558_, 1);
                v_stop_4562_ = crate::leanh::lean_ctor_get(v_left_4558_, 2);
                v_i_4563_ = lean_array_get_size(v_pref_4560_);
                v___x_4569_ = lean_nat_sub(v_stop_4562_, v_start_4561_);
                v___x_4570_ = lean_nat_dec_lt(v_i_4563_, v___x_4569_);
                crate::leanh::lean_dec(v___x_4569_);
                if v___x_4570_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_start_4571_ = crate::leanh::lean_ctor_get(v_right_4559_, 1);
                    v_stop_4572_ = crate::leanh::lean_ctor_get(v_right_4559_, 2);
                    v___x_4573_ = lean_nat_sub(v_stop_4572_, v_start_4571_);
                    v___x_4574_ = lean_nat_dec_lt(v_i_4563_, v___x_4573_);
                    crate::leanh::lean_dec(v___x_4573_);
                    if v___x_4574_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_4575_ = l_Subarray_get___redArg(v_left_4558_, v_i_4563_);
                        v___x_4576_ = l_Subarray_get___redArg(v_right_4559_, v_i_4563_);
                        v___x_4577_ = crate::leanh::lean_unbox_uint32(v___x_4575_);
                        v___x_4578_ = crate::leanh::lean_unbox_uint32(v___x_4576_);
                        crate::leanh::lean_dec(v___x_4576_);
                        v___x_4579_ = lean_uint32_dec_eq(v___x_4577_, v___x_4578_);
                        if v___x_4579_ == 0 {
                            crate::leanh::lean_dec(v___x_4575_);
                            v___x_4580_ = l_Subarray_drop___redArg(v_left_4558_, v_i_4563_);
                            v___x_4581_ = l_Subarray_drop___redArg(v_right_4559_, v_i_4563_);
                            v___x_4582_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4582_, 0, v___x_4580_);
                            crate::leanh::lean_ctor_set(v___x_4582_, 1, v___x_4581_);
                            v___x_4583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4583_, 0, v_pref_4560_);
                            crate::leanh::lean_ctor_set(v___x_4583_, 1, v___x_4582_);
                            return v___x_4583_;
                        } else {
                            v___x_4584_ = lean_array_push(v_pref_4560_, v___x_4575_);
                            v_pref_4560_ = v___x_4584_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4565_ = l_Subarray_drop___redArg(v_left_4558_, v_i_4563_);
                v___x_4566_ = l_Subarray_drop___redArg(v_right_4559_, v_i_4563_);
                v___x_4567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4567_, 0, v___x_4565_);
                crate::leanh::lean_ctor_set(v___x_4567_, 1, v___x_4566_);
                v___x_4568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4568_, 0, v_pref_4560_);
                crate::leanh::lean_ctor_set(v___x_4568_, 1, v___x_4567_);
                return v___x_4568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(
    mut v_left_4586_: *mut crate::leanh::LeanObject,
    mut v_right_4587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0;
    v___x_4589_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_4586_, v_right_4587_, v___x_4588_);
    return v___x_4589_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_b_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4597_: u8 = 0;
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4592_ = crate::leanh::lean_ctor_get(v_a_4590_, 0);
                v_start_4593_ = crate::leanh::lean_ctor_get(v_a_4590_, 1);
                v_stop_4594_ = crate::leanh::lean_ctor_get(v_a_4590_, 2);
                v_isSharedCheck_4607_ = (!crate::leanh::lean_is_exclusive(v_a_4590_)) as u8;
                if v_isSharedCheck_4607_ == 0 {
                    v___x_4596_ = v_a_4590_;
                    v_isShared_4597_ = v_isSharedCheck_4607_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_4594_);
                    crate::leanh::lean_inc(v_start_4593_);
                    crate::leanh::lean_inc(v_array_4592_);
                    crate::leanh::lean_dec(v_a_4590_);
                    v___x_4596_ = crate::leanh::lean_box(0);
                    v_isShared_4597_ = v_isSharedCheck_4607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4598_ = lean_nat_dec_lt(v_start_4593_, v_stop_4594_);
                if v___x_4598_ == 0 {
                    crate::leanh::lean_del_object(v___x_4596_);
                    crate::leanh::lean_dec(v_stop_4594_);
                    crate::leanh::lean_dec(v_start_4593_);
                    crate::leanh::lean_dec_ref(v_array_4592_);
                    return v_b_4591_;
                } else {
                    v___x_4599_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4600_ = lean_nat_add(v_start_4593_, v___x_4599_);
                    crate::leanh::lean_inc_ref(v_array_4592_);
                    if v_isShared_4597_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4596_, 1, v___x_4600_);
                        v___x_4602_ = v___x_4596_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4606_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_array_4592_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 1, v___x_4600_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_stop_4594_);
                        v___x_4602_ = v_reuseFailAlloc_4606_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4603_ = lean_array_fget(v_array_4592_, v_start_4593_);
                crate::leanh::lean_dec(v_start_4593_);
                crate::leanh::lean_dec_ref(v_array_4592_);
                v___x_4604_ = lean_array_push(v_b_4591_, v___x_4603_);
                v_a_4590_ = v___x_4602_;
                v_b_4591_ = v___x_4604_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(
    mut v_left_4608_: *mut crate::leanh::LeanObject,
    mut v_right_4609_: *mut crate::leanh::LeanObject,
    mut v_i_4610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: u8 = 0;
    let mut v_start_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u32 = 0;
    let mut v___x_4640_: u32 = 0;
    let mut v___x_4641_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_4611_ = crate::leanh::lean_ctor_get(v_left_4608_, 1);
                v_stop_4612_ = crate::leanh::lean_ctor_get(v_left_4608_, 2);
                v___x_4613_ = lean_nat_sub(v_stop_4612_, v_start_4611_);
                v___x_4627_ = lean_nat_dec_lt(v_i_4610_, v___x_4613_);
                if v___x_4627_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_start_4628_ = crate::leanh::lean_ctor_get(v_right_4609_, 1);
                    v_stop_4629_ = crate::leanh::lean_ctor_get(v_right_4609_, 2);
                    v___x_4630_ = lean_nat_sub(v_stop_4629_, v_start_4628_);
                    v___x_4631_ = lean_nat_dec_lt(v_i_4610_, v___x_4630_);
                    if v___x_4631_ == 0 {
                        crate::leanh::lean_dec(v___x_4630_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4632_ = lean_nat_sub(v___x_4613_, v_i_4610_);
                        crate::leanh::lean_dec(v___x_4613_);
                        v___x_4633_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4634_ = lean_nat_sub(v___x_4632_, v___x_4633_);
                        v___x_4635_ = l_Subarray_get___redArg(v_left_4608_, v___x_4634_);
                        crate::leanh::lean_dec(v___x_4634_);
                        v___x_4636_ = lean_nat_sub(v___x_4630_, v_i_4610_);
                        crate::leanh::lean_dec(v___x_4630_);
                        v___x_4637_ = lean_nat_sub(v___x_4636_, v___x_4633_);
                        v___x_4638_ = l_Subarray_get___redArg(v_right_4609_, v___x_4637_);
                        crate::leanh::lean_dec(v___x_4637_);
                        v___x_4639_ = crate::leanh::lean_unbox_uint32(v___x_4635_);
                        crate::leanh::lean_dec(v___x_4635_);
                        v___x_4640_ = crate::leanh::lean_unbox_uint32(v___x_4638_);
                        crate::leanh::lean_dec(v___x_4638_);
                        v___x_4641_ = lean_uint32_dec_eq(v___x_4639_, v___x_4640_);
                        if v___x_4641_ == 0 {
                            crate::leanh::lean_dec(v_i_4610_);
                            crate::leanh::lean_inc_ref(v_left_4608_);
                            v___x_4642_ = l_Subarray_take___redArg(v_left_4608_, v___x_4632_);
                            v___x_4643_ = l_Subarray_take___redArg(v_right_4609_, v___x_4636_);
                            crate::leanh::lean_dec(v___x_4636_);
                            v___x_4644_ = l_Subarray_drop___redArg(v_left_4608_, v___x_4632_);
                            crate::leanh::lean_dec(v___x_4632_);
                            v___x_4645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0;
                            v___x_4646_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_4644_, v___x_4645_);
                            v___x_4647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4647_, 0, v___x_4643_);
                            crate::leanh::lean_ctor_set(v___x_4647_, 1, v___x_4646_);
                            v___x_4648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4642_);
                            crate::leanh::lean_ctor_set(v___x_4648_, 1, v___x_4647_);
                            return v___x_4648_;
                        } else {
                            crate::leanh::lean_dec(v___x_4636_);
                            crate::leanh::lean_dec(v___x_4632_);
                            v___x_4649_ = lean_nat_add(v_i_4610_, v___x_4633_);
                            crate::leanh::lean_dec(v_i_4610_);
                            v_i_4610_ = v___x_4649_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_start_4615_ = crate::leanh::lean_ctor_get(v_right_4609_, 1);
                v_stop_4616_ = crate::leanh::lean_ctor_get(v_right_4609_, 2);
                v___x_4617_ = lean_nat_sub(v___x_4613_, v_i_4610_);
                crate::leanh::lean_dec(v___x_4613_);
                crate::leanh::lean_inc_ref(v_left_4608_);
                v___x_4618_ = l_Subarray_take___redArg(v_left_4608_, v___x_4617_);
                v___x_4619_ = lean_nat_sub(v_stop_4616_, v_start_4615_);
                v___x_4620_ = lean_nat_sub(v___x_4619_, v_i_4610_);
                crate::leanh::lean_dec(v_i_4610_);
                crate::leanh::lean_dec(v___x_4619_);
                v___x_4621_ = l_Subarray_take___redArg(v_right_4609_, v___x_4620_);
                crate::leanh::lean_dec(v___x_4620_);
                v___x_4622_ = l_Subarray_drop___redArg(v_left_4608_, v___x_4617_);
                crate::leanh::lean_dec(v___x_4617_);
                v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0;
                v___x_4624_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_4622_, v___x_4623_);
                v___x_4625_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4621_);
                crate::leanh::lean_ctor_set(v___x_4625_, 1, v___x_4624_);
                v___x_4626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4626_, 0, v___x_4618_);
                crate::leanh::lean_ctor_set(v___x_4626_, 1, v___x_4625_);
                return v___x_4626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(
    mut v_left_4651_: *mut crate::leanh::LeanObject,
    mut v_right_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4653_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4654_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_4651_, v_right_4652_, v___x_4653_);
    return v___x_4654_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(
    mut v_x_4655_: *mut crate::leanh::LeanObject,
    mut v_x_4656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4656_) == 0 {
        crate::leanh::lean_inc(v_x_4655_);
        return v_x_4655_;
    } else {
        let mut v_key_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_4657_ = crate::leanh::lean_ctor_get(v_x_4656_, 0);
        v_value_4658_ = crate::leanh::lean_ctor_get(v_x_4656_, 1);
        v_tail_4659_ = crate::leanh::lean_ctor_get(v_x_4656_, 2);
        v___x_4660_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_4655_, v_tail_4659_);
        crate::leanh::lean_inc(v_value_4658_);
        crate::leanh::lean_inc(v_key_4657_);
        v___x_4661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4661_, 0, v_key_4657_);
        crate::leanh::lean_ctor_set(v___x_4661_, 1, v_value_4658_);
        v___x_4662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4662_, 0, v___x_4661_);
        crate::leanh::lean_ctor_set(v___x_4662_, 1, v___x_4660_);
        return v___x_4662_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(
    mut v_x_4663_: *mut crate::leanh::LeanObject,
    mut v_x_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4665_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_4663_, v_x_4664_);
    crate::leanh::lean_dec(v_x_4664_);
    crate::leanh::lean_dec(v_x_4663_);
    return v_res_4665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(
    mut v_as_4666_: *mut crate::leanh::LeanObject,
    mut v_i_4667_: usize,
    mut v_stop_4668_: usize,
    mut v_b_4669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: usize = 0;
    let mut v___x_4672_: usize = 0;
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4670_ = lean_usize_dec_eq(v_i_4667_, v_stop_4668_);
                if v___x_4670_ == 0 {
                    v___x_4671_ = 1usize;
                    v___x_4672_ = lean_usize_sub(v_i_4667_, v___x_4671_);
                    v___x_4673_ = lean_array_uget_borrowed(v_as_4666_, v___x_4672_);
                    v___x_4674_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_b_4669_, v___x_4673_);
                    crate::leanh::lean_dec(v_b_4669_);
                    v_i_4667_ = v___x_4672_;
                    v_b_4669_ = v___x_4674_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(
    mut v_as_4676_: *mut crate::leanh::LeanObject,
    mut v_i_4677_: *mut crate::leanh::LeanObject,
    mut v_stop_4678_: *mut crate::leanh::LeanObject,
    mut v_b_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4680_: usize = 0;
    let mut v_stop_boxed_4681_: usize = 0;
    let mut v_res_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4680_ = crate::leanh::lean_unbox_usize(v_i_4677_);
    crate::leanh::lean_dec(v_i_4677_);
    v_stop_boxed_4681_ = crate::leanh::lean_unbox_usize(v_stop_4678_);
    crate::leanh::lean_dec(v_stop_4678_);
    v_res_4682_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_as_4676_, v_i_boxed_4680_, v_stop_boxed_4681_, v_b_4679_);
    crate::leanh::lean_dec_ref(v_as_4676_);
    return v_res_4682_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(
    mut v_histogram_4683_: *mut crate::leanh::LeanObject,
    mut v_index_4684_: *mut crate::leanh::LeanObject,
    mut v_val_4685_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v_leftCount_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4712_: u8 = 0;
    let mut v_unused_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_4683_, v_val_4685_);
                if crate::leanh::lean_obj_tag(v___x_4686_) == 0 {
                    v___x_4687_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4688_, 0, v_index_4684_);
                    v___x_4689_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4690_ = crate::leanh::lean_box(0);
                    v___x_4691_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4691_, 0, v___x_4687_);
                    crate::leanh::lean_ctor_set(v___x_4691_, 1, v___x_4688_);
                    crate::leanh::lean_ctor_set(v___x_4691_, 2, v___x_4689_);
                    crate::leanh::lean_ctor_set(v___x_4691_, 3, v___x_4690_);
                    v___x_4692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_4683_, v_val_4685_, v___x_4691_);
                    return v___x_4692_;
                } else {
                    v_val_4693_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4714_ = (!crate::leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4714_ == 0 {
                        v___x_4695_ = v___x_4686_;
                        v_isShared_4696_ = v_isSharedCheck_4714_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4693_);
                        crate::leanh::lean_dec(v___x_4686_);
                        v___x_4695_ = crate::leanh::lean_box(0);
                        v_isShared_4696_ = v_isSharedCheck_4714_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_4697_ = crate::leanh::lean_ctor_get(v_val_4693_, 0);
                v_rightCount_4698_ = crate::leanh::lean_ctor_get(v_val_4693_, 2);
                v_rightIndex_4699_ = crate::leanh::lean_ctor_get(v_val_4693_, 3);
                v_isSharedCheck_4712_ = (!crate::leanh::lean_is_exclusive(v_val_4693_)) as u8;
                if v_isSharedCheck_4712_ == 0 {
                    v_unused_4713_ = crate::leanh::lean_ctor_get(v_val_4693_, 1);
                    crate::leanh::lean_dec(v_unused_4713_);
                    v___x_4701_ = v_val_4693_;
                    v_isShared_4702_ = v_isSharedCheck_4712_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rightIndex_4699_);
                    crate::leanh::lean_inc(v_rightCount_4698_);
                    crate::leanh::lean_inc(v_leftCount_4697_);
                    crate::leanh::lean_dec(v_val_4693_);
                    v___x_4701_ = crate::leanh::lean_box(0);
                    v_isShared_4702_ = v_isSharedCheck_4712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4703_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4704_ = lean_nat_add(v_leftCount_4697_, v___x_4703_);
                crate::leanh::lean_dec(v_leftCount_4697_);
                if v_isShared_4696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4695_, 0, v_index_4684_);
                    v___x_4706_ = v___x_4695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_index_4684_);
                    v___x_4706_ = v_reuseFailAlloc_4711_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4702_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4701_, 1, v___x_4706_);
                    crate::leanh::lean_ctor_set(v___x_4701_, 0, v___x_4704_);
                    v___x_4708_ = v___x_4701_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4710_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4710_, 1, v___x_4706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4710_, 2, v_rightCount_4698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4710_, 3, v_rightIndex_4699_);
                    v___x_4708_ = v_reuseFailAlloc_4710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_4683_, v_val_4685_, v___x_4708_);
                return v___x_4709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(
    mut v_histogram_4715_: *mut crate::leanh::LeanObject,
    mut v_index_4716_: *mut crate::leanh::LeanObject,
    mut v_val_4717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_4718_: u32 = 0;
    let mut v_res_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4718_ = crate::leanh::lean_unbox_uint32(v_val_4717_);
    crate::leanh::lean_dec(v_val_4717_);
    v_res_4719_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_4715_, v_index_4716_, v_val_boxed_4718_);
    return v_res_4719_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(
    mut v_upperBound_4720_: *mut crate::leanh::LeanObject,
    mut v_fst_4721_: *mut crate::leanh::LeanObject,
    mut v___x_4722_: *mut crate::leanh::LeanObject,
    mut v_fst_4723_: *mut crate::leanh::LeanObject,
    mut v_a_4724_: *mut crate::leanh::LeanObject,
    mut v_b_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u32 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4726_ = lean_nat_dec_lt(v_a_4724_, v_upperBound_4720_);
                if v___x_4726_ == 0 {
                    crate::leanh::lean_dec(v_a_4724_);
                    return v_b_4725_;
                } else {
                    v___x_4727_ = l_Subarray_get___redArg(v_fst_4723_, v_a_4724_);
                    v___x_4728_ = crate::leanh::lean_unbox_uint32(v___x_4727_);
                    crate::leanh::lean_dec(v___x_4727_);
                    crate::leanh::lean_inc(v_a_4724_);
                    v___x_4729_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_b_4725_, v_a_4724_, v___x_4728_);
                    v___x_4730_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4731_ = lean_nat_add(v_a_4724_, v___x_4730_);
                    crate::leanh::lean_dec(v_a_4724_);
                    v_a_4724_ = v___x_4731_;
                    v_b_4725_ = v___x_4729_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(
    mut v_upperBound_4733_: *mut crate::leanh::LeanObject,
    mut v_fst_4734_: *mut crate::leanh::LeanObject,
    mut v___x_4735_: *mut crate::leanh::LeanObject,
    mut v_fst_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
    mut v_b_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_4733_, v_fst_4734_, v___x_4735_, v_fst_4736_, v_a_4737_, v_b_4738_);
    crate::leanh::lean_dec_ref(v_fst_4736_);
    crate::leanh::lean_dec(v___x_4735_);
    crate::leanh::lean_dec_ref(v_fst_4734_);
    crate::leanh::lean_dec(v_upperBound_4733_);
    return v_res_4739_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4740_ = crate::leanh::lean_box(0);
    v___x_4741_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4742_ = lean_mk_array(v___x_4741_, v___x_4740_);
    return v___x_4742_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once), _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
    v___x_4744_ = crate::leanh::lean_unsigned_to_nat(0);
    v_hist_4745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_hist_4745_, 0, v___x_4744_);
    crate::leanh::lean_ctor_set(v_hist_4745_, 1, v___x_4743_);
    return v_hist_4745_;
}
pub unsafe fn l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(
    mut v_left_4746_: *mut crate::leanh::LeanObject,
    mut v_right_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: usize = 0;
    let mut v___x_4801_: usize = 0;
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4748_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_4746_, v_right_4747_);
                v_snd_4749_ = crate::leanh::lean_ctor_get(v___x_4748_, 1);
                crate::leanh::lean_inc(v_snd_4749_);
                v_fst_4750_ = crate::leanh::lean_ctor_get(v___x_4748_, 0);
                crate::leanh::lean_inc(v_fst_4750_);
                crate::leanh::lean_dec_ref(v___x_4748_);
                v_fst_4751_ = crate::leanh::lean_ctor_get(v_snd_4749_, 0);
                crate::leanh::lean_inc(v_fst_4751_);
                v_snd_4752_ = crate::leanh::lean_ctor_get(v_snd_4749_, 1);
                crate::leanh::lean_inc(v_snd_4752_);
                crate::leanh::lean_dec(v_snd_4749_);
                v___x_4753_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_4751_, v_snd_4752_);
                v_snd_4754_ = crate::leanh::lean_ctor_get(v___x_4753_, 1);
                crate::leanh::lean_inc(v_snd_4754_);
                v_fst_4755_ = crate::leanh::lean_ctor_get(v___x_4753_, 0);
                crate::leanh::lean_inc(v_fst_4755_);
                crate::leanh::lean_dec_ref(v___x_4753_);
                v_fst_4756_ = crate::leanh::lean_ctor_get(v_snd_4754_, 0);
                crate::leanh::lean_inc(v_fst_4756_);
                v_snd_4757_ = crate::leanh::lean_ctor_get(v_snd_4754_, 1);
                crate::leanh::lean_inc(v_snd_4757_);
                crate::leanh::lean_dec(v_snd_4754_);
                v_start_4758_ = crate::leanh::lean_ctor_get(v_fst_4755_, 1);
                v_stop_4759_ = crate::leanh::lean_ctor_get(v_fst_4755_, 2);
                v___x_4760_ = crate::leanh::lean_unsigned_to_nat(0);
                v_hist_4761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once), _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
                v___x_4762_ = lean_nat_sub(v_stop_4759_, v_start_4758_);
                v___x_4763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v___x_4762_, v_fst_4756_, v___x_4762_, v_fst_4755_, v___x_4760_, v_hist_4761_);
                v_start_4764_ = crate::leanh::lean_ctor_get(v_fst_4756_, 1);
                v_stop_4765_ = crate::leanh::lean_ctor_get(v_fst_4756_, 2);
                v___x_4766_ = lean_nat_sub(v_stop_4765_, v_start_4764_);
                v___x_4767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v___x_4766_, v___x_4766_, v_fst_4756_, v___x_4762_, v___x_4760_, v___x_4763_);
                crate::leanh::lean_dec(v___x_4762_);
                crate::leanh::lean_dec(v___x_4766_);
                v_buckets_4768_ = crate::leanh::lean_ctor_get(v___x_4767_, 1);
                crate::leanh::lean_inc_ref(v_buckets_4768_);
                crate::leanh::lean_dec_ref(v___x_4767_);
                v___x_4769_ = crate::leanh::lean_box(0);
                v___x_4797_ = crate::leanh::lean_box(0);
                v___x_4798_ = lean_array_get_size(v_buckets_4768_);
                v___x_4799_ = lean_nat_dec_lt(v___x_4760_, v___x_4798_);
                if v___x_4799_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_4768_);
                    v___y_4771_ = v___x_4797_;
                    state = 1;
                    continue;
                } else {
                    v___x_4800_ = lean_usize_of_nat(v___x_4798_);
                    v___x_4801_ = 0usize;
                    v___x_4802_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_buckets_4768_, v___x_4800_, v___x_4801_, v___x_4797_);
                    crate::leanh::lean_dec_ref(v_buckets_4768_);
                    v___y_4771_ = v___x_4802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4772_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v___y_4771_, v___x_4769_);
                crate::leanh::lean_dec(v___y_4771_);
                if crate::leanh::lean_obj_tag(v___x_4772_) == 1 {
                    v_val_4773_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                    crate::leanh::lean_inc(v_val_4773_);
                    crate::leanh::lean_dec_ref_known(v___x_4772_, 1);
                    v_snd_4774_ = crate::leanh::lean_ctor_get(v_val_4773_, 1);
                    crate::leanh::lean_inc(v_snd_4774_);
                    crate::leanh::lean_dec(v_val_4773_);
                    v_snd_4775_ = crate::leanh::lean_ctor_get(v_snd_4774_, 1);
                    crate::leanh::lean_inc(v_snd_4775_);
                    v_fst_4776_ = crate::leanh::lean_ctor_get(v_snd_4774_, 0);
                    crate::leanh::lean_inc(v_fst_4776_);
                    crate::leanh::lean_dec(v_snd_4774_);
                    v_fst_4777_ = crate::leanh::lean_ctor_get(v_snd_4775_, 0);
                    crate::leanh::lean_inc(v_fst_4777_);
                    v_snd_4778_ = crate::leanh::lean_ctor_get(v_snd_4775_, 1);
                    crate::leanh::lean_inc(v_snd_4778_);
                    crate::leanh::lean_dec(v_snd_4775_);
                    v___x_4779_ = l_Subarray_split___redArg(v_fst_4755_, v_fst_4777_);
                    crate::leanh::lean_dec(v_fst_4777_);
                    v_fst_4780_ = crate::leanh::lean_ctor_get(v___x_4779_, 0);
                    crate::leanh::lean_inc(v_fst_4780_);
                    v_snd_4781_ = crate::leanh::lean_ctor_get(v___x_4779_, 1);
                    crate::leanh::lean_inc(v_snd_4781_);
                    crate::leanh::lean_dec_ref(v___x_4779_);
                    v___x_4782_ = l_Subarray_split___redArg(v_fst_4756_, v_snd_4778_);
                    crate::leanh::lean_dec(v_snd_4778_);
                    v_fst_4783_ = crate::leanh::lean_ctor_get(v___x_4782_, 0);
                    crate::leanh::lean_inc(v_fst_4783_);
                    v_snd_4784_ = crate::leanh::lean_ctor_get(v___x_4782_, 1);
                    crate::leanh::lean_inc(v_snd_4784_);
                    crate::leanh::lean_dec_ref(v___x_4782_);
                    v___x_4785_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_4780_, v_fst_4783_);
                    v___x_4786_ = l_Array_append___redArg(v_fst_4750_, v___x_4785_);
                    crate::leanh::lean_dec_ref(v___x_4785_);
                    v___x_4787_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4788_ = lean_mk_empty_array_with_capacity(v___x_4787_);
                    v___x_4789_ = lean_array_push(v___x_4788_, v_fst_4776_);
                    v___x_4790_ = l_Array_append___redArg(v___x_4786_, v___x_4789_);
                    crate::leanh::lean_dec_ref(v___x_4789_);
                    v___x_4791_ = l_Subarray_drop___redArg(v_snd_4781_, v___x_4787_);
                    v___x_4792_ = l_Subarray_drop___redArg(v_snd_4784_, v___x_4787_);
                    v___x_4793_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_4791_, v___x_4792_);
                    v___x_4794_ = l_Array_append___redArg(v___x_4790_, v___x_4793_);
                    crate::leanh::lean_dec_ref(v___x_4793_);
                    v___x_4795_ = l_Array_append___redArg(v___x_4794_, v_snd_4757_);
                    crate::leanh::lean_dec(v_snd_4757_);
                    return v___x_4795_;
                } else {
                    crate::leanh::lean_dec(v___x_4772_);
                    crate::leanh::lean_dec(v_fst_4756_);
                    crate::leanh::lean_dec(v_fst_4755_);
                    v___x_4796_ = l_Array_append___redArg(v_fst_4750_, v_snd_4757_);
                    crate::leanh::lean_dec(v_snd_4757_);
                    return v___x_4796_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(
    mut v_sz_4803_: usize,
    mut v_i_4804_: usize,
    mut v_bs_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: u8 = 0;
    let mut v_v_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4806_ = lean_usize_dec_lt(v_i_4804_, v_sz_4803_);
                if v___x_4806_ == 0 {
                    return v_bs_4805_;
                } else {
                    v_v_4807_ = lean_array_uget(v_bs_4805_, v_i_4804_);
                    v___x_4808_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4809_ = lean_array_uset(v_bs_4805_, v_i_4804_, v___x_4808_);
                    v___x_4810_ = 1;
                    v___x_4811_ = crate::leanh::lean_box((v___x_4810_) as usize);
                    v___x_4812_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4812_, 0, v___x_4811_);
                    crate::leanh::lean_ctor_set(v___x_4812_, 1, v_v_4807_);
                    v___x_4813_ = 1usize;
                    v___x_4814_ = lean_usize_add(v_i_4804_, v___x_4813_);
                    v___x_4815_ = lean_array_uset(v_bs_x27_4809_, v_i_4804_, v___x_4812_);
                    v_i_4804_ = v___x_4814_;
                    v_bs_4805_ = v___x_4815_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(
    mut v_sz_4817_: *mut crate::leanh::LeanObject,
    mut v_i_4818_: *mut crate::leanh::LeanObject,
    mut v_bs_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4820_: usize = 0;
    let mut v_i_boxed_4821_: usize = 0;
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4820_ = crate::leanh::lean_unbox_usize(v_sz_4817_);
    crate::leanh::lean_dec(v_sz_4817_);
    v_i_boxed_4821_ = crate::leanh::lean_unbox_usize(v_i_4818_);
    crate::leanh::lean_dec(v_i_4818_);
    v_res_4822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_4820_, v_i_boxed_4821_, v_bs_4819_);
    return v_res_4822_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: u32 = 0;
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ = 65;
    v___x_4824_ = crate::leanh::lean_box_uint32(v___x_4823_);
    return v___x_4824_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(
    mut v_edited_4825_: *mut crate::leanh::LeanObject,
    mut v___x_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: u32,
    mut v_a_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v___y_4835_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: u8 = 0;
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: u32 = 0;
    let mut v___x_4855_: u8 = 0;
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4829_ = crate::leanh::lean_ctor_get(v_a_4828_, 0);
                v_snd_4830_ = crate::leanh::lean_ctor_get(v_a_4828_, 1);
                v_isSharedCheck_4857_ = (!crate::leanh::lean_is_exclusive(v_a_4828_)) as u8;
                if v_isSharedCheck_4857_ == 0 {
                    v___x_4832_ = v_a_4828_;
                    v_isShared_4833_ = v_isSharedCheck_4857_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4830_);
                    crate::leanh::lean_inc(v_fst_4829_);
                    crate::leanh::lean_dec(v_a_4828_);
                    v___x_4832_ = crate::leanh::lean_box(0);
                    v_isShared_4833_ = v_isSharedCheck_4857_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4851_ = lean_nat_dec_lt(v_snd_4830_, v___x_4826_);
                if v___x_4851_ == 0 {
                    v___y_4835_ = v___x_4851_;
                    state = 2;
                    continue;
                } else {
                    v___x_4852_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
                    v___x_4853_ = lean_array_get_borrowed(v___x_4852_, v_edited_4825_, v_snd_4830_);
                    v___x_4854_ = crate::leanh::lean_unbox_uint32(v___x_4853_);
                    v___x_4855_ = lean_uint32_dec_eq(v___x_4854_, v_a_4827_);
                    if v___x_4855_ == 0 {
                        v___y_4835_ = v___x_4851_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4832_);
                        v___x_4856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4856_, 0, v_fst_4829_);
                        crate::leanh::lean_ctor_set(v___x_4856_, 1, v_snd_4830_);
                        return v___x_4856_;
                    }
                }
            }
            2 => {
                if v___y_4835_ == 0 {
                    if v_isShared_4833_ == 0 {
                        v___x_4837_ = v___x_4832_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_fst_4829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_snd_4830_);
                        v___x_4837_ = v_reuseFailAlloc_4838_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4839_ = 0;
                    v___x_4840_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
                    v___x_4841_ = lean_array_get_borrowed(v___x_4840_, v_edited_4825_, v_snd_4830_);
                    v___x_4842_ = crate::leanh::lean_box((v___x_4839_) as usize);
                    crate::leanh::lean_inc(v___x_4841_);
                    if v_isShared_4833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4832_, 1, v___x_4841_);
                        crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4842_);
                        v___x_4844_ = v___x_4832_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4850_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4842_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4841_);
                        v___x_4844_ = v_reuseFailAlloc_4850_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4837_;
            }
            4 => {
                v___x_4845_ = lean_array_push(v_fst_4829_, v___x_4844_);
                v___x_4846_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4847_ = lean_nat_add(v_snd_4830_, v___x_4846_);
                crate::leanh::lean_dec(v_snd_4830_);
                v___x_4848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4845_);
                crate::leanh::lean_ctor_set(v___x_4848_, 1, v___x_4847_);
                v_a_4828_ = v___x_4848_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(
    mut v_edited_4858_: *mut crate::leanh::LeanObject,
    mut v___x_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4862_: u32 = 0;
    let mut v_res_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4862_ = crate::leanh::lean_unbox_uint32(v_a_4860_);
    crate::leanh::lean_dec(v_a_4860_);
    v_res_4863_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_4858_, v___x_4859_, v_a_boxed_4862_, v_a_4861_);
    crate::leanh::lean_dec(v___x_4859_);
    crate::leanh::lean_dec_ref(v_edited_4858_);
    return v_res_4863_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(
    mut v_original_4864_: *mut crate::leanh::LeanObject,
    mut v___x_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: u32,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___y_4874_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u32 = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4868_ = crate::leanh::lean_ctor_get(v_a_4867_, 0);
                v_snd_4869_ = crate::leanh::lean_ctor_get(v_a_4867_, 1);
                v_isSharedCheck_4896_ = (!crate::leanh::lean_is_exclusive(v_a_4867_)) as u8;
                if v_isSharedCheck_4896_ == 0 {
                    v___x_4871_ = v_a_4867_;
                    v_isShared_4872_ = v_isSharedCheck_4896_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4869_);
                    crate::leanh::lean_inc(v_fst_4868_);
                    crate::leanh::lean_dec(v_a_4867_);
                    v___x_4871_ = crate::leanh::lean_box(0);
                    v_isShared_4872_ = v_isSharedCheck_4896_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4890_ = lean_nat_dec_lt(v_snd_4869_, v___x_4865_);
                if v___x_4890_ == 0 {
                    v___y_4874_ = v___x_4890_;
                    state = 2;
                    continue;
                } else {
                    v___x_4891_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
                    v___x_4892_ =
                        lean_array_get_borrowed(v___x_4891_, v_original_4864_, v_snd_4869_);
                    v___x_4893_ = crate::leanh::lean_unbox_uint32(v___x_4892_);
                    v___x_4894_ = lean_uint32_dec_eq(v___x_4893_, v_a_4866_);
                    if v___x_4894_ == 0 {
                        v___y_4874_ = v___x_4890_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4871_);
                        v___x_4895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4895_, 0, v_fst_4868_);
                        crate::leanh::lean_ctor_set(v___x_4895_, 1, v_snd_4869_);
                        return v___x_4895_;
                    }
                }
            }
            2 => {
                if v___y_4874_ == 0 {
                    if v_isShared_4872_ == 0 {
                        v___x_4876_ = v___x_4871_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_fst_4868_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_snd_4869_);
                        v___x_4876_ = v_reuseFailAlloc_4877_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4878_ = 1;
                    v___x_4879_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
                    v___x_4880_ =
                        lean_array_get_borrowed(v___x_4879_, v_original_4864_, v_snd_4869_);
                    v___x_4881_ = crate::leanh::lean_box((v___x_4878_) as usize);
                    crate::leanh::lean_inc(v___x_4880_);
                    if v_isShared_4872_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4871_, 1, v___x_4880_);
                        crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4881_);
                        v___x_4883_ = v___x_4871_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4881_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 1, v___x_4880_);
                        v___x_4883_ = v_reuseFailAlloc_4889_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4876_;
            }
            4 => {
                v___x_4884_ = lean_array_push(v_fst_4868_, v___x_4883_);
                v___x_4885_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4886_ = lean_nat_add(v_snd_4869_, v___x_4885_);
                crate::leanh::lean_dec(v_snd_4869_);
                v___x_4887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4884_);
                crate::leanh::lean_ctor_set(v___x_4887_, 1, v___x_4886_);
                v_a_4867_ = v___x_4887_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(
    mut v_original_4897_: *mut crate::leanh::LeanObject,
    mut v___x_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
    mut v_a_4900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4901_: u32 = 0;
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4901_ = crate::leanh::lean_unbox_uint32(v_a_4899_);
    crate::leanh::lean_dec(v_a_4899_);
    v_res_4902_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_4897_, v___x_4898_, v_a_boxed_4901_, v_a_4900_);
    crate::leanh::lean_dec(v___x_4898_);
    crate::leanh::lean_dec_ref(v_original_4897_);
    return v_res_4902_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(
    mut v_original_4903_: *mut crate::leanh::LeanObject,
    mut v___x_4904_: *mut crate::leanh::LeanObject,
    mut v_edited_4905_: *mut crate::leanh::LeanObject,
    mut v___x_4906_: *mut crate::leanh::LeanObject,
    mut v_as_4907_: *mut crate::leanh::LeanObject,
    mut v_sz_4908_: usize,
    mut v_i_4909_: usize,
    mut v_b_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4911_: u8 = 0;
    let mut v_snd_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v_fst_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4921_: u8 = 0;
    let mut v_a_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u32 = 0;
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: u32 = 0;
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v___x_4941_: u8 = 0;
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: usize = 0;
    let mut v___x_4953_: usize = 0;
    let mut v_reuseFailAlloc_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_reuseFailAlloc_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut v_reuseFailAlloc_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4911_ = lean_usize_dec_lt(v_i_4909_, v_sz_4908_);
                if v___x_4911_ == 0 {
                    return v_b_4910_;
                } else {
                    v_snd_4912_ = crate::leanh::lean_ctor_get(v_b_4910_, 1);
                    v_fst_4913_ = crate::leanh::lean_ctor_get(v_b_4910_, 0);
                    v_isSharedCheck_4962_ = (!crate::leanh::lean_is_exclusive(v_b_4910_)) as u8;
                    if v_isSharedCheck_4962_ == 0 {
                        v___x_4915_ = v_b_4910_;
                        v_isShared_4916_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4912_);
                        crate::leanh::lean_inc(v_fst_4913_);
                        crate::leanh::lean_dec(v_b_4910_);
                        v___x_4915_ = crate::leanh::lean_box(0);
                        v_isShared_4916_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4917_ = crate::leanh::lean_ctor_get(v_snd_4912_, 0);
                v_snd_4918_ = crate::leanh::lean_ctor_get(v_snd_4912_, 1);
                v_isSharedCheck_4961_ = (!crate::leanh::lean_is_exclusive(v_snd_4912_)) as u8;
                if v_isSharedCheck_4961_ == 0 {
                    v___x_4920_ = v_snd_4912_;
                    v_isShared_4921_ = v_isSharedCheck_4961_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4918_);
                    crate::leanh::lean_inc(v_fst_4917_);
                    crate::leanh::lean_dec(v_snd_4912_);
                    v___x_4920_ = crate::leanh::lean_box(0);
                    v_isShared_4921_ = v_isSharedCheck_4961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4922_ = lean_array_uget_borrowed(v_as_4907_, v_i_4909_);
                if v_isShared_4921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4920_, 1, v_fst_4917_);
                    crate::leanh::lean_ctor_set(v___x_4920_, 0, v_fst_4913_);
                    v___x_4924_ = v___x_4920_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_fst_4913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_fst_4917_);
                    v___x_4924_ = v_reuseFailAlloc_4960_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4925_ = crate::leanh::lean_unbox_uint32(v_a_4922_);
                v___x_4926_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_4903_, v___x_4904_, v___x_4925_, v___x_4924_);
                v_fst_4927_ = crate::leanh::lean_ctor_get(v___x_4926_, 0);
                v_snd_4928_ = crate::leanh::lean_ctor_get(v___x_4926_, 1);
                v_isSharedCheck_4959_ = (!crate::leanh::lean_is_exclusive(v___x_4926_)) as u8;
                if v_isSharedCheck_4959_ == 0 {
                    v___x_4930_ = v___x_4926_;
                    v_isShared_4931_ = v_isSharedCheck_4959_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4928_);
                    crate::leanh::lean_inc(v_fst_4927_);
                    crate::leanh::lean_dec(v___x_4926_);
                    v___x_4930_ = crate::leanh::lean_box(0);
                    v_isShared_4931_ = v_isSharedCheck_4959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4930_, 1, v_snd_4918_);
                    v___x_4933_ = v___x_4930_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_fst_4927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 1, v_snd_4918_);
                    v___x_4933_ = v_reuseFailAlloc_4958_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4934_ = crate::leanh::lean_unbox_uint32(v_a_4922_);
                v___x_4935_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_4905_, v___x_4906_, v___x_4934_, v___x_4933_);
                v_fst_4936_ = crate::leanh::lean_ctor_get(v___x_4935_, 0);
                v_snd_4937_ = crate::leanh::lean_ctor_get(v___x_4935_, 1);
                v_isSharedCheck_4957_ = (!crate::leanh::lean_is_exclusive(v___x_4935_)) as u8;
                if v_isSharedCheck_4957_ == 0 {
                    v___x_4939_ = v___x_4935_;
                    v_isShared_4940_ = v_isSharedCheck_4957_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4937_);
                    crate::leanh::lean_inc(v_fst_4936_);
                    crate::leanh::lean_dec(v___x_4935_);
                    v___x_4939_ = crate::leanh::lean_box(0);
                    v_isShared_4940_ = v_isSharedCheck_4957_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4941_ = 2;
                v___x_4942_ = crate::leanh::lean_box((v___x_4941_) as usize);
                crate::leanh::lean_inc(v_a_4922_);
                if v_isShared_4940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4939_, 1, v_a_4922_);
                    crate::leanh::lean_ctor_set(v___x_4939_, 0, v___x_4942_);
                    v___x_4944_ = v___x_4939_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 1, v_a_4922_);
                    v___x_4944_ = v_reuseFailAlloc_4956_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4945_ = lean_array_push(v_fst_4936_, v___x_4944_);
                v___x_4946_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4947_ = lean_nat_add(v_snd_4928_, v___x_4946_);
                crate::leanh::lean_dec(v_snd_4928_);
                v___x_4948_ = lean_nat_add(v_snd_4937_, v___x_4946_);
                crate::leanh::lean_dec(v_snd_4937_);
                if v_isShared_4916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4915_, 1, v___x_4948_);
                    crate::leanh::lean_ctor_set(v___x_4915_, 0, v___x_4947_);
                    v___x_4950_ = v___x_4915_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___x_4948_);
                    v___x_4950_ = v_reuseFailAlloc_4955_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4951_, 0, v___x_4945_);
                crate::leanh::lean_ctor_set(v___x_4951_, 1, v___x_4950_);
                v___x_4952_ = 1usize;
                v___x_4953_ = lean_usize_add(v_i_4909_, v___x_4952_);
                v_i_4909_ = v___x_4953_;
                v_b_4910_ = v___x_4951_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(
    mut v_original_4963_: *mut crate::leanh::LeanObject,
    mut v___x_4964_: *mut crate::leanh::LeanObject,
    mut v_edited_4965_: *mut crate::leanh::LeanObject,
    mut v___x_4966_: *mut crate::leanh::LeanObject,
    mut v_as_4967_: *mut crate::leanh::LeanObject,
    mut v_sz_4968_: *mut crate::leanh::LeanObject,
    mut v_i_4969_: *mut crate::leanh::LeanObject,
    mut v_b_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4971_: usize = 0;
    let mut v_i_boxed_4972_: usize = 0;
    let mut v_res_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4971_ = crate::leanh::lean_unbox_usize(v_sz_4968_);
    crate::leanh::lean_dec(v_sz_4968_);
    v_i_boxed_4972_ = crate::leanh::lean_unbox_usize(v_i_4969_);
    crate::leanh::lean_dec(v_i_4969_);
    v_res_4973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_4963_, v___x_4964_, v_edited_4965_, v___x_4966_, v_as_4967_, v_sz_boxed_4971_, v_i_boxed_4972_, v_b_4970_);
    crate::leanh::lean_dec_ref(v_as_4967_);
    crate::leanh::lean_dec(v___x_4966_);
    crate::leanh::lean_dec_ref(v_edited_4965_);
    crate::leanh::lean_dec(v___x_4964_);
    crate::leanh::lean_dec_ref(v_original_4963_);
    return v_res_4973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(
    mut v_edited_4974_: *mut crate::leanh::LeanObject,
    mut v___x_4975_: *mut crate::leanh::LeanObject,
    mut v_original_4976_: *mut crate::leanh::LeanObject,
    mut v___x_4977_: *mut crate::leanh::LeanObject,
    mut v_as_4978_: *mut crate::leanh::LeanObject,
    mut v_sz_4979_: usize,
    mut v_i_4980_: usize,
    mut v_b_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4982_: u8 = 0;
    let mut v_snd_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4987_: u8 = 0;
    let mut v_fst_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v_a_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: u32 = 0;
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u32 = 0;
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5012_: u8 = 0;
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: usize = 0;
    let mut v___x_5024_: usize = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut v_reuseFailAlloc_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5030_: u8 = 0;
    let mut v_reuseFailAlloc_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5032_: u8 = 0;
    let mut v_isSharedCheck_5033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4982_ = lean_usize_dec_lt(v_i_4980_, v_sz_4979_);
                if v___x_4982_ == 0 {
                    return v_b_4981_;
                } else {
                    v_snd_4983_ = crate::leanh::lean_ctor_get(v_b_4981_, 1);
                    v_fst_4984_ = crate::leanh::lean_ctor_get(v_b_4981_, 0);
                    v_isSharedCheck_5033_ = (!crate::leanh::lean_is_exclusive(v_b_4981_)) as u8;
                    if v_isSharedCheck_5033_ == 0 {
                        v___x_4986_ = v_b_4981_;
                        v_isShared_4987_ = v_isSharedCheck_5033_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4983_);
                        crate::leanh::lean_inc(v_fst_4984_);
                        crate::leanh::lean_dec(v_b_4981_);
                        v___x_4986_ = crate::leanh::lean_box(0);
                        v_isShared_4987_ = v_isSharedCheck_5033_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4988_ = crate::leanh::lean_ctor_get(v_snd_4983_, 0);
                v_snd_4989_ = crate::leanh::lean_ctor_get(v_snd_4983_, 1);
                v_isSharedCheck_5032_ = (!crate::leanh::lean_is_exclusive(v_snd_4983_)) as u8;
                if v_isSharedCheck_5032_ == 0 {
                    v___x_4991_ = v_snd_4983_;
                    v_isShared_4992_ = v_isSharedCheck_5032_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4989_);
                    crate::leanh::lean_inc(v_fst_4988_);
                    crate::leanh::lean_dec(v_snd_4983_);
                    v___x_4991_ = crate::leanh::lean_box(0);
                    v_isShared_4992_ = v_isSharedCheck_5032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4993_ = lean_array_uget_borrowed(v_as_4978_, v_i_4980_);
                if v_isShared_4992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4991_, 1, v_fst_4988_);
                    crate::leanh::lean_ctor_set(v___x_4991_, 0, v_fst_4984_);
                    v___x_4995_ = v___x_4991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_fst_4984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_fst_4988_);
                    v___x_4995_ = v_reuseFailAlloc_5031_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4996_ = crate::leanh::lean_unbox_uint32(v_a_4993_);
                v___x_4997_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_4976_, v___x_4977_, v___x_4996_, v___x_4995_);
                v_fst_4998_ = crate::leanh::lean_ctor_get(v___x_4997_, 0);
                v_snd_4999_ = crate::leanh::lean_ctor_get(v___x_4997_, 1);
                v_isSharedCheck_5030_ = (!crate::leanh::lean_is_exclusive(v___x_4997_)) as u8;
                if v_isSharedCheck_5030_ == 0 {
                    v___x_5001_ = v___x_4997_;
                    v_isShared_5002_ = v_isSharedCheck_5030_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4999_);
                    crate::leanh::lean_inc(v_fst_4998_);
                    crate::leanh::lean_dec(v___x_4997_);
                    v___x_5001_ = crate::leanh::lean_box(0);
                    v_isShared_5002_ = v_isSharedCheck_5030_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5001_, 1, v_snd_4989_);
                    v___x_5004_ = v___x_5001_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_fst_4998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5029_, 1, v_snd_4989_);
                    v___x_5004_ = v_reuseFailAlloc_5029_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5005_ = crate::leanh::lean_unbox_uint32(v_a_4993_);
                v___x_5006_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_4974_, v___x_4975_, v___x_5005_, v___x_5004_);
                v_fst_5007_ = crate::leanh::lean_ctor_get(v___x_5006_, 0);
                v_snd_5008_ = crate::leanh::lean_ctor_get(v___x_5006_, 1);
                v_isSharedCheck_5028_ = (!crate::leanh::lean_is_exclusive(v___x_5006_)) as u8;
                if v_isSharedCheck_5028_ == 0 {
                    v___x_5010_ = v___x_5006_;
                    v_isShared_5011_ = v_isSharedCheck_5028_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5008_);
                    crate::leanh::lean_inc(v_fst_5007_);
                    crate::leanh::lean_dec(v___x_5006_);
                    v___x_5010_ = crate::leanh::lean_box(0);
                    v_isShared_5011_ = v_isSharedCheck_5028_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5012_ = 2;
                v___x_5013_ = crate::leanh::lean_box((v___x_5012_) as usize);
                crate::leanh::lean_inc(v_a_4993_);
                if v_isShared_5011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5010_, 1, v_a_4993_);
                    crate::leanh::lean_ctor_set(v___x_5010_, 0, v___x_5013_);
                    v___x_5015_ = v___x_5010_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_a_4993_);
                    v___x_5015_ = v_reuseFailAlloc_5027_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5016_ = lean_array_push(v_fst_5007_, v___x_5015_);
                v___x_5017_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5018_ = lean_nat_add(v_snd_4999_, v___x_5017_);
                crate::leanh::lean_dec(v_snd_4999_);
                v___x_5019_ = lean_nat_add(v_snd_5008_, v___x_5017_);
                crate::leanh::lean_dec(v_snd_5008_);
                if v_isShared_4987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4986_, 1, v___x_5019_);
                    crate::leanh::lean_ctor_set(v___x_4986_, 0, v___x_5018_);
                    v___x_5021_ = v___x_4986_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5026_, 1, v___x_5019_);
                    v___x_5021_ = v_reuseFailAlloc_5026_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5022_, 0, v___x_5016_);
                crate::leanh::lean_ctor_set(v___x_5022_, 1, v___x_5021_);
                v___x_5023_ = 1usize;
                v___x_5024_ = lean_usize_add(v_i_4980_, v___x_5023_);
                v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_4976_, v___x_4977_, v_edited_4974_, v___x_4975_, v_as_4978_, v_sz_4979_, v___x_5024_, v___x_5022_);
                return v___x_5025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(
    mut v_edited_5034_: *mut crate::leanh::LeanObject,
    mut v___x_5035_: *mut crate::leanh::LeanObject,
    mut v_original_5036_: *mut crate::leanh::LeanObject,
    mut v___x_5037_: *mut crate::leanh::LeanObject,
    mut v_as_5038_: *mut crate::leanh::LeanObject,
    mut v_sz_5039_: *mut crate::leanh::LeanObject,
    mut v_i_5040_: *mut crate::leanh::LeanObject,
    mut v_b_5041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5042_: usize = 0;
    let mut v_i_boxed_5043_: usize = 0;
    let mut v_res_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5042_ = crate::leanh::lean_unbox_usize(v_sz_5039_);
    crate::leanh::lean_dec(v_sz_5039_);
    v_i_boxed_5043_ = crate::leanh::lean_unbox_usize(v_i_5040_);
    crate::leanh::lean_dec(v_i_5040_);
    v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_5034_, v___x_5035_, v_original_5036_, v___x_5037_, v_as_5038_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5041_);
    crate::leanh::lean_dec_ref(v_as_5038_);
    crate::leanh::lean_dec(v___x_5037_);
    crate::leanh::lean_dec_ref(v_original_5036_);
    crate::leanh::lean_dec(v___x_5035_);
    crate::leanh::lean_dec_ref(v_edited_5034_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(
    mut v_original_5052_: *mut crate::leanh::LeanObject,
    mut v_edited_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: u8 = 0;
    let mut v_sz_5057_: usize = 0;
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v_sz_5062_: usize = 0;
    let mut v___x_5063_: usize = 0;
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ds_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5091_: u8 = 0;
    let mut v_unused_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_i_5054_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5055_ = lean_array_get_size(v_original_5052_);
                v___x_5056_ = lean_nat_dec_lt(v_i_5054_, v___x_5055_);
                if v___x_5056_ == 0 {
                    crate::leanh::lean_dec_ref(v_original_5052_);
                    v_sz_5057_ = lean_array_size(v_edited_5053_);
                    v___x_5058_ = 0usize;
                    v___x_5059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_5057_, v___x_5058_, v_edited_5053_);
                    return v___x_5059_;
                } else {
                    v___x_5060_ = lean_array_get_size(v_edited_5053_);
                    v___x_5061_ = lean_nat_dec_lt(v_i_5054_, v___x_5060_);
                    if v___x_5061_ == 0 {
                        crate::leanh::lean_dec_ref(v_edited_5053_);
                        v_sz_5062_ = lean_array_size(v_original_5052_);
                        v___x_5063_ = 0usize;
                        v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_5062_, v___x_5063_, v_original_5052_);
                        return v___x_5064_;
                    } else {
                        crate::leanh::lean_inc_ref(v_original_5052_);
                        v___x_5065_ =
                            l_Array_toSubarray___redArg(v_original_5052_, v_i_5054_, v___x_5055_);
                        crate::leanh::lean_inc_ref(v_edited_5053_);
                        v___x_5066_ =
                            l_Array_toSubarray___redArg(v_edited_5053_, v_i_5054_, v___x_5060_);
                        v_ds_5067_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_5065_, v___x_5066_);
                        v___x_5068_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2;
                        v_sz_5069_ = lean_array_size(v_ds_5067_);
                        v___x_5070_ = 0usize;
                        v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_5053_, v___x_5060_, v_original_5052_, v___x_5055_, v_ds_5067_, v_sz_5069_, v___x_5070_, v___x_5068_);
                        crate::leanh::lean_dec_ref(v_ds_5067_);
                        v_snd_5072_ = crate::leanh::lean_ctor_get(v___x_5071_, 1);
                        crate::leanh::lean_inc(v_snd_5072_);
                        v_fst_5073_ = crate::leanh::lean_ctor_get(v___x_5071_, 0);
                        crate::leanh::lean_inc(v_fst_5073_);
                        crate::leanh::lean_dec_ref(v___x_5071_);
                        v_fst_5074_ = crate::leanh::lean_ctor_get(v_snd_5072_, 0);
                        v_snd_5075_ = crate::leanh::lean_ctor_get(v_snd_5072_, 1);
                        v_isSharedCheck_5094_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_5072_)) as u8;
                        if v_isSharedCheck_5094_ == 0 {
                            v___x_5077_ = v_snd_5072_;
                            v_isShared_5078_ = v_isSharedCheck_5094_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5075_);
                            crate::leanh::lean_inc(v_fst_5074_);
                            crate::leanh::lean_dec(v_snd_5072_);
                            v___x_5077_ = crate::leanh::lean_box(0);
                            v_isShared_5078_ = v_isSharedCheck_5094_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5077_, 1, v_fst_5074_);
                    crate::leanh::lean_ctor_set(v___x_5077_, 0, v_fst_5073_);
                    v___x_5080_ = v___x_5077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_fst_5073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 1, v_fst_5074_);
                    v___x_5080_ = v_reuseFailAlloc_5093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5081_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_5055_, v_original_5052_, v___x_5080_);
                crate::leanh::lean_dec_ref(v_original_5052_);
                v_fst_5082_ = crate::leanh::lean_ctor_get(v___x_5081_, 0);
                v_isSharedCheck_5091_ = (!crate::leanh::lean_is_exclusive(v___x_5081_)) as u8;
                if v_isSharedCheck_5091_ == 0 {
                    v_unused_5092_ = crate::leanh::lean_ctor_get(v___x_5081_, 1);
                    crate::leanh::lean_dec(v_unused_5092_);
                    v___x_5084_ = v___x_5081_;
                    v_isShared_5085_ = v_isSharedCheck_5091_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5082_);
                    crate::leanh::lean_dec(v___x_5081_);
                    v___x_5084_ = crate::leanh::lean_box(0);
                    v_isShared_5085_ = v_isSharedCheck_5091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5085_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5084_, 1, v_snd_5075_);
                    v___x_5087_ = v___x_5084_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_fst_5082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5090_, 1, v_snd_5075_);
                    v___x_5087_ = v_reuseFailAlloc_5090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5088_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_5060_, v_edited_5053_, v___x_5087_);
                crate::leanh::lean_dec_ref(v_edited_5053_);
                v_fst_5089_ = crate::leanh::lean_ctor_get(v___x_5088_, 0);
                crate::leanh::lean_inc(v_fst_5089_);
                crate::leanh::lean_dec_ref(v___x_5088_);
                return v_fst_5089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(
    mut v_s_5095_: *mut crate::leanh::LeanObject,
    mut v_a_5096_: *mut crate::leanh::LeanObject,
    mut v_b_5097_: u8,
) -> u8 {
    let mut v_str_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: u8 = 0;
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: u32 = 0;
    let mut v___x_5105_: u32 = 0;
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5098_ = crate::leanh::lean_ctor_get(v_s_5095_, 0);
                v_startInclusive_5099_ = crate::leanh::lean_ctor_get(v_s_5095_, 1);
                v_endExclusive_5100_ = crate::leanh::lean_ctor_get(v_s_5095_, 2);
                v___x_5101_ = lean_nat_sub(v_endExclusive_5100_, v_startInclusive_5099_);
                v___x_5102_ = lean_nat_dec_eq(v_a_5096_, v___x_5101_);
                crate::leanh::lean_dec(v___x_5101_);
                if v___x_5102_ == 0 {
                    v___x_5103_ = lean_nat_add(v_startInclusive_5099_, v_a_5096_);
                    crate::leanh::lean_dec(v_a_5096_);
                    v___x_5104_ = lean_string_utf8_get_fast(v_str_5098_, v___x_5103_);
                    v___x_5105_ = 10;
                    v___x_5106_ = lean_uint32_dec_eq(v___x_5104_, v___x_5105_);
                    if v___x_5106_ == 0 {
                        v___x_5107_ = lean_string_utf8_next_fast(v_str_5098_, v___x_5103_);
                        crate::leanh::lean_dec(v___x_5103_);
                        v___x_5108_ = lean_nat_sub(v___x_5107_, v_startInclusive_5099_);
                        v_a_5096_ = v___x_5108_;
                        v_b_5097_ = v___x_5106_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5103_);
                        return v___x_5106_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5096_);
                    return v_b_5097_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(
    mut v_s_5110_: *mut crate::leanh::LeanObject,
    mut v_a_5111_: *mut crate::leanh::LeanObject,
    mut v_b_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_5113_: u8 = 0;
    let mut v_res_5114_: u8 = 0;
    let mut v_r_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_5113_ = (crate::leanh::lean_unbox(v_b_5112_) as u8);
    v_res_5114_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_5110_, v_a_5111_, v_b_boxed_5113_);
    crate::leanh::lean_dec_ref(v_s_5110_);
    v_r_5115_ = crate::leanh::lean_box((v_res_5114_) as usize);
    return v_r_5115_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(
    mut v_s_5116_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_searcher_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: u8 = 0;
    v_searcher_5117_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5118_ = 0;
    v___x_5119_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_5116_, v_searcher_5117_, v___x_5118_);
    return v___x_5119_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(
    mut v_s_5120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5121_: u8 = 0;
    let mut v_r_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5121_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_5120_);
    crate::leanh::lean_dec_ref(v_s_5120_);
    v_r_5122_ = crate::leanh::lean_box((v_res_5121_) as usize);
    return v_r_5122_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(
    mut v_oldWs_5123_: *mut crate::leanh::LeanObject,
    mut v_newWs_5124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: u8 = 0;
    v___x_5125_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5126_ = lean_string_utf8_byte_size(v_oldWs_5123_);
    crate::leanh::lean_inc_ref(v_oldWs_5123_);
    v___x_5127_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5127_, 0, v_oldWs_5123_);
    crate::leanh::lean_ctor_set(v___x_5127_, 1, v___x_5125_);
    crate::leanh::lean_ctor_set(v___x_5127_, 2, v___x_5126_);
    v___x_5128_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_5127_);
    crate::leanh::lean_dec_ref_known(v___x_5127_, 3);
    if v___x_5128_ == 0 {
        let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5129_ = lean_string_data(v_oldWs_5123_);
        v___x_5130_ = lean_array_mk(v___x_5129_);
        v___x_5131_ = lean_string_data(v_newWs_5124_);
        v___x_5132_ = lean_array_mk(v___x_5131_);
        v___x_5133_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_5130_, v___x_5132_);
        v___x_5134_ =
            l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_5133_);
        crate::leanh::lean_dec_ref(v___x_5133_);
        return v___x_5134_;
    } else {
        let mut v___x_5135_: u8 = 0;
        let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_oldWs_5123_);
        v___x_5135_ = 2;
        v___x_5136_ = crate::leanh::lean_box((v___x_5135_) as usize);
        v___x_5137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5136_);
        crate::leanh::lean_ctor_set(v___x_5137_, 1, v_newWs_5124_);
        v___x_5138_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5139_ = lean_mk_empty_array_with_capacity(v___x_5138_);
        v___x_5140_ = lean_array_push(v___x_5139_, v___x_5137_);
        return v___x_5140_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(
    mut v_s_5141_: *mut crate::leanh::LeanObject,
    mut v_inst_5142_: *mut crate::leanh::LeanObject,
    mut v_R_5143_: *mut crate::leanh::LeanObject,
    mut v_a_5144_: *mut crate::leanh::LeanObject,
    mut v_b_5145_: u8,
    mut v_c_5146_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5147_: u8 = 0;
    v___x_5147_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_5141_, v_a_5144_, v_b_5145_);
    return v___x_5147_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(
    mut v_s_5148_: *mut crate::leanh::LeanObject,
    mut v_inst_5149_: *mut crate::leanh::LeanObject,
    mut v_R_5150_: *mut crate::leanh::LeanObject,
    mut v_a_5151_: *mut crate::leanh::LeanObject,
    mut v_b_5152_: *mut crate::leanh::LeanObject,
    mut v_c_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_5154_: u8 = 0;
    let mut v_res_5155_: u8 = 0;
    let mut v_r_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_5154_ = (crate::leanh::lean_unbox(v_b_5152_) as u8);
    v_res_5155_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_5148_, v_inst_5149_, v_R_5150_, v_a_5151_, v_b_boxed_5154_, v_c_5153_);
    crate::leanh::lean_dec_ref(v_s_5148_);
    v_r_5156_ = crate::leanh::lean_box((v_res_5155_) as usize);
    return v_r_5156_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(
    mut v_original_5157_: *mut crate::leanh::LeanObject,
    mut v___x_5158_: *mut crate::leanh::LeanObject,
    mut v_a_5159_: u32,
    mut v_inst_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5162_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_5157_, v___x_5158_, v_a_5159_, v_a_5161_);
    return v___x_5162_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(
    mut v_original_5163_: *mut crate::leanh::LeanObject,
    mut v___x_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
    mut v_inst_5166_: *mut crate::leanh::LeanObject,
    mut v_a_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5168_: u32 = 0;
    let mut v_res_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5168_ = crate::leanh::lean_unbox_uint32(v_a_5165_);
    crate::leanh::lean_dec(v_a_5165_);
    v_res_5169_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_5163_, v___x_5164_, v_a_boxed_5168_, v_inst_5166_, v_a_5167_);
    crate::leanh::lean_dec(v___x_5164_);
    crate::leanh::lean_dec_ref(v_original_5163_);
    return v_res_5169_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(
    mut v_edited_5170_: *mut crate::leanh::LeanObject,
    mut v___x_5171_: *mut crate::leanh::LeanObject,
    mut v_a_5172_: u32,
    mut v_inst_5173_: *mut crate::leanh::LeanObject,
    mut v_a_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5175_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_5170_, v___x_5171_, v_a_5172_, v_a_5174_);
    return v___x_5175_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(
    mut v_edited_5176_: *mut crate::leanh::LeanObject,
    mut v___x_5177_: *mut crate::leanh::LeanObject,
    mut v_a_5178_: *mut crate::leanh::LeanObject,
    mut v_inst_5179_: *mut crate::leanh::LeanObject,
    mut v_a_5180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5181_: u32 = 0;
    let mut v_res_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5181_ = crate::leanh::lean_unbox_uint32(v_a_5178_);
    crate::leanh::lean_dec(v_a_5178_);
    v_res_5182_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_5176_, v___x_5177_, v_a_boxed_5181_, v_inst_5179_, v_a_5180_);
    crate::leanh::lean_dec(v___x_5177_);
    crate::leanh::lean_dec_ref(v_edited_5176_);
    return v_res_5182_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(
    mut v___x_5183_: *mut crate::leanh::LeanObject,
    mut v_original_5184_: *mut crate::leanh::LeanObject,
    mut v_inst_5185_: *mut crate::leanh::LeanObject,
    mut v_a_5186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5187_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_5183_, v_original_5184_, v_a_5186_);
    return v___x_5187_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(
    mut v___x_5188_: *mut crate::leanh::LeanObject,
    mut v_original_5189_: *mut crate::leanh::LeanObject,
    mut v_inst_5190_: *mut crate::leanh::LeanObject,
    mut v_a_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_5188_, v_original_5189_, v_inst_5190_, v_a_5191_);
    crate::leanh::lean_dec_ref(v_original_5189_);
    crate::leanh::lean_dec(v___x_5188_);
    return v_res_5192_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(
    mut v___x_5193_: *mut crate::leanh::LeanObject,
    mut v_edited_5194_: *mut crate::leanh::LeanObject,
    mut v_inst_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_5193_, v_edited_5194_, v_a_5196_);
    return v___x_5197_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(
    mut v___x_5198_: *mut crate::leanh::LeanObject,
    mut v_edited_5199_: *mut crate::leanh::LeanObject,
    mut v_inst_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5202_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_5198_, v_edited_5199_, v_inst_5200_, v_a_5201_);
    crate::leanh::lean_dec_ref(v_edited_5199_);
    crate::leanh::lean_dec(v___x_5198_);
    return v_res_5202_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(
    mut v_as_5203_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5204_: *mut crate::leanh::LeanObject,
    mut v_b_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5207_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_5204_, v_b_5205_);
    return v___x_5207_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(
    mut v_as_5208_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5209_: *mut crate::leanh::LeanObject,
    mut v_b_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5212_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_5208_, v_as_x27_5209_, v_b_5210_, v_a_5211_);
    crate::leanh::lean_dec(v_as_x27_5209_);
    crate::leanh::lean_dec(v_as_5208_);
    return v_res_5212_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(
    mut v_lsize_5213_: *mut crate::leanh::LeanObject,
    mut v_rsize_5214_: *mut crate::leanh::LeanObject,
    mut v_histogram_5215_: *mut crate::leanh::LeanObject,
    mut v_index_5216_: *mut crate::leanh::LeanObject,
    mut v_val_5217_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_5215_, v_index_5216_, v_val_5217_);
    return v___x_5218_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(
    mut v_lsize_5219_: *mut crate::leanh::LeanObject,
    mut v_rsize_5220_: *mut crate::leanh::LeanObject,
    mut v_histogram_5221_: *mut crate::leanh::LeanObject,
    mut v_index_5222_: *mut crate::leanh::LeanObject,
    mut v_val_5223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_5224_: u32 = 0;
    let mut v_res_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_5224_ = crate::leanh::lean_unbox_uint32(v_val_5223_);
    crate::leanh::lean_dec(v_val_5223_);
    v_res_5225_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_5219_, v_rsize_5220_, v_histogram_5221_, v_index_5222_, v_val_boxed_5224_);
    crate::leanh::lean_dec(v_rsize_5220_);
    crate::leanh::lean_dec(v_lsize_5219_);
    return v_res_5225_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(
    mut v_upperBound_5226_: *mut crate::leanh::LeanObject,
    mut v___x_5227_: *mut crate::leanh::LeanObject,
    mut v_fst_5228_: *mut crate::leanh::LeanObject,
    mut v___x_5229_: *mut crate::leanh::LeanObject,
    mut v_inst_5230_: *mut crate::leanh::LeanObject,
    mut v_R_5231_: *mut crate::leanh::LeanObject,
    mut v_a_5232_: *mut crate::leanh::LeanObject,
    mut v_b_5233_: *mut crate::leanh::LeanObject,
    mut v_c_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_5226_, v___x_5227_, v_fst_5228_, v___x_5229_, v_a_5232_, v_b_5233_);
    return v___x_5235_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(
    mut v_upperBound_5236_: *mut crate::leanh::LeanObject,
    mut v___x_5237_: *mut crate::leanh::LeanObject,
    mut v_fst_5238_: *mut crate::leanh::LeanObject,
    mut v___x_5239_: *mut crate::leanh::LeanObject,
    mut v_inst_5240_: *mut crate::leanh::LeanObject,
    mut v_R_5241_: *mut crate::leanh::LeanObject,
    mut v_a_5242_: *mut crate::leanh::LeanObject,
    mut v_b_5243_: *mut crate::leanh::LeanObject,
    mut v_c_5244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_5236_, v___x_5237_, v_fst_5238_, v___x_5239_, v_inst_5240_, v_R_5241_, v_a_5242_, v_b_5243_, v_c_5244_);
    crate::leanh::lean_dec(v___x_5239_);
    crate::leanh::lean_dec_ref(v_fst_5238_);
    crate::leanh::lean_dec(v___x_5237_);
    crate::leanh::lean_dec(v_upperBound_5236_);
    return v_res_5245_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(
    mut v_lsize_5246_: *mut crate::leanh::LeanObject,
    mut v_rsize_5247_: *mut crate::leanh::LeanObject,
    mut v_histogram_5248_: *mut crate::leanh::LeanObject,
    mut v_index_5249_: *mut crate::leanh::LeanObject,
    mut v_val_5250_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_5248_, v_index_5249_, v_val_5250_);
    return v___x_5251_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(
    mut v_lsize_5252_: *mut crate::leanh::LeanObject,
    mut v_rsize_5253_: *mut crate::leanh::LeanObject,
    mut v_histogram_5254_: *mut crate::leanh::LeanObject,
    mut v_index_5255_: *mut crate::leanh::LeanObject,
    mut v_val_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_5257_: u32 = 0;
    let mut v_res_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_5257_ = crate::leanh::lean_unbox_uint32(v_val_5256_);
    crate::leanh::lean_dec(v_val_5256_);
    v_res_5258_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_5252_, v_rsize_5253_, v_histogram_5254_, v_index_5255_, v_val_boxed_5257_);
    crate::leanh::lean_dec(v_rsize_5253_);
    crate::leanh::lean_dec(v_lsize_5252_);
    return v_res_5258_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(
    mut v_upperBound_5259_: *mut crate::leanh::LeanObject,
    mut v_fst_5260_: *mut crate::leanh::LeanObject,
    mut v___x_5261_: *mut crate::leanh::LeanObject,
    mut v_fst_5262_: *mut crate::leanh::LeanObject,
    mut v_inst_5263_: *mut crate::leanh::LeanObject,
    mut v_R_5264_: *mut crate::leanh::LeanObject,
    mut v_a_5265_: *mut crate::leanh::LeanObject,
    mut v_b_5266_: *mut crate::leanh::LeanObject,
    mut v_c_5267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_5259_, v_fst_5260_, v___x_5261_, v_fst_5262_, v_a_5265_, v_b_5266_);
    return v___x_5268_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(
    mut v_upperBound_5269_: *mut crate::leanh::LeanObject,
    mut v_fst_5270_: *mut crate::leanh::LeanObject,
    mut v___x_5271_: *mut crate::leanh::LeanObject,
    mut v_fst_5272_: *mut crate::leanh::LeanObject,
    mut v_inst_5273_: *mut crate::leanh::LeanObject,
    mut v_R_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_b_5276_: *mut crate::leanh::LeanObject,
    mut v_c_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_5269_, v_fst_5270_, v___x_5271_, v_fst_5272_, v_inst_5273_, v_R_5274_, v_a_5275_, v_b_5276_, v_c_5277_);
    crate::leanh::lean_dec_ref(v_fst_5272_);
    crate::leanh::lean_dec(v___x_5271_);
    crate::leanh::lean_dec_ref(v_fst_5270_);
    crate::leanh::lean_dec(v_upperBound_5269_);
    return v_res_5278_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(
    mut v_00_u03b2_5279_: *mut crate::leanh::LeanObject,
    mut v_m_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_5280_, v_a_5281_);
    return v___x_5282_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(
    mut v_00_u03b2_5283_: *mut crate::leanh::LeanObject,
    mut v_m_5284_: *mut crate::leanh::LeanObject,
    mut v_a_5285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5286_: u32 = 0;
    let mut v_res_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5286_ = crate::leanh::lean_unbox_uint32(v_a_5285_);
    crate::leanh::lean_dec(v_a_5285_);
    v_res_5287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_5283_, v_m_5284_, v_a_boxed_5286_);
    crate::leanh::lean_dec_ref(v_m_5284_);
    return v_res_5287_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(
    mut v_00_u03b2_5288_: *mut crate::leanh::LeanObject,
    mut v_m_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: u32,
    mut v_b_5291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_5289_, v_a_5290_, v_b_5291_);
    return v___x_5292_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(
    mut v_00_u03b2_5293_: *mut crate::leanh::LeanObject,
    mut v_m_5294_: *mut crate::leanh::LeanObject,
    mut v_a_5295_: *mut crate::leanh::LeanObject,
    mut v_b_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5297_: u32 = 0;
    let mut v_res_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5297_ = crate::leanh::lean_unbox_uint32(v_a_5295_);
    crate::leanh::lean_dec(v_a_5295_);
    v_res_5298_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_5293_, v_m_5294_, v_a_boxed_5297_, v_b_5296_);
    return v_res_5298_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(
    mut v_inst_5299_: *mut crate::leanh::LeanObject,
    mut v_R_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_b_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5303_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_5301_, v_b_5302_);
    return v___x_5303_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(
    mut v_00_u03b2_5304_: *mut crate::leanh::LeanObject,
    mut v_a_5305_: u32,
    mut v_x_5306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_5305_, v_x_5306_);
    return v___x_5307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(
    mut v_00_u03b2_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
    mut v_x_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5311_: u32 = 0;
    let mut v_res_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5311_ = crate::leanh::lean_unbox_uint32(v_a_5309_);
    crate::leanh::lean_dec(v_a_5309_);
    v_res_5312_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_5308_, v_a_boxed_5311_, v_x_5310_);
    crate::leanh::lean_dec(v_x_5310_);
    return v_res_5312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(
    mut v_00_u03b2_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: u32,
    mut v_x_5315_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5316_: u8 = 0;
    v___x_5316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_5314_, v_x_5315_);
    return v___x_5316_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(
    mut v_00_u03b2_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_x_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5320_: u32 = 0;
    let mut v_res_5321_: u8 = 0;
    let mut v_r_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5320_ = crate::leanh::lean_unbox_uint32(v_a_5318_);
    crate::leanh::lean_dec(v_a_5318_);
    v_res_5321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_5317_, v_a_boxed_5320_, v_x_5319_);
    crate::leanh::lean_dec(v_x_5319_);
    v_r_5322_ = crate::leanh::lean_box((v_res_5321_) as usize);
    return v_r_5322_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(
    mut v_00_u03b2_5323_: *mut crate::leanh::LeanObject,
    mut v_data_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_5324_);
    return v___x_5325_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(
    mut v_00_u03b2_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: u32,
    mut v_b_5328_: *mut crate::leanh::LeanObject,
    mut v_x_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_5327_, v_b_5328_, v_x_5329_);
    return v___x_5330_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(
    mut v_00_u03b2_5331_: *mut crate::leanh::LeanObject,
    mut v_a_5332_: *mut crate::leanh::LeanObject,
    mut v_b_5333_: *mut crate::leanh::LeanObject,
    mut v_x_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_5335_: u32 = 0;
    let mut v_res_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5335_ = crate::leanh::lean_unbox_uint32(v_a_5332_);
    crate::leanh::lean_dec(v_a_5332_);
    v_res_5336_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_5331_, v_a_boxed_5335_, v_b_5333_, v_x_5334_);
    return v_res_5336_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(
    mut v_00_u03b2_5337_: *mut crate::leanh::LeanObject,
    mut v_i_5338_: *mut crate::leanh::LeanObject,
    mut v_source_5339_: *mut crate::leanh::LeanObject,
    mut v_target_5340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5341_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_5338_, v_source_5339_, v_target_5340_);
    return v___x_5341_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(
    mut v_00_u03b2_5342_: *mut crate::leanh::LeanObject,
    mut v_x_5343_: *mut crate::leanh::LeanObject,
    mut v_x_5344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5345_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_5343_, v_x_5344_);
    return v___x_5345_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(
    mut v_s_5346_: *mut crate::leanh::LeanObject,
    mut v_stopPos_5347_: *mut crate::leanh::LeanObject,
    mut v_i_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5353_: u8 = 0;
    let mut v___x_5354_: u8 = 0;
    let mut v___x_5355_: u32 = 0;
    let mut v___y_5357_: u8 = 0;
    let mut v___x_5358_: u32 = 0;
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: u32 = 0;
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: u32 = 0;
    let mut v___x_5363_: u8 = 0;
    let mut v___x_5364_: u32 = 0;
    let mut v___x_5365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5354_ = lean_nat_dec_lt(v_i_5348_, v_stopPos_5347_);
                if v___x_5354_ == 0 {
                    return v_i_5348_;
                } else {
                    v___x_5355_ = lean_string_utf8_get(v_s_5346_, v_i_5348_);
                    v___x_5362_ = 32;
                    v___x_5363_ = lean_uint32_dec_eq(v___x_5355_, v___x_5362_);
                    if v___x_5363_ == 0 {
                        v___x_5364_ = 9;
                        v___x_5365_ = lean_uint32_dec_eq(v___x_5355_, v___x_5364_);
                        v___y_5357_ = v___x_5365_;
                        state = 3;
                        continue;
                    } else {
                        v___y_5357_ = v___x_5363_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5350_ = lean_string_utf8_next(v_s_5346_, v_i_5348_);
                crate::leanh::lean_dec(v_i_5348_);
                v_i_5348_ = v___x_5350_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_5353_ == 0 {
                    return v_i_5348_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_5357_ == 0 {
                    v___x_5358_ = 13;
                    v___x_5359_ = lean_uint32_dec_eq(v___x_5355_, v___x_5358_);
                    if v___x_5359_ == 0 {
                        v___x_5360_ = 10;
                        v___x_5361_ = lean_uint32_dec_eq(v___x_5355_, v___x_5360_);
                        v___y_5353_ = v___x_5361_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5353_ = v___x_5359_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(
    mut v_s_5366_: *mut crate::leanh::LeanObject,
    mut v_stopPos_5367_: *mut crate::leanh::LeanObject,
    mut v_i_5368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5369_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_5366_, v_stopPos_5367_, v_i_5368_);
    crate::leanh::lean_dec(v_stopPos_5367_);
    crate::leanh::lean_dec_ref(v_s_5366_);
    return v_res_5369_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(
    mut v_s_5370_: *mut crate::leanh::LeanObject,
    mut v_b_5371_: *mut crate::leanh::LeanObject,
    mut v_i_5372_: *mut crate::leanh::LeanObject,
    mut v_r_5373_: *mut crate::leanh::LeanObject,
    mut v_ws_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: u8 = 0;
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: u8 = 0;
    let mut v___x_5388_: u32 = 0;
    let mut v___y_5390_: u8 = 0;
    let mut v___x_5391_: u32 = 0;
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: u32 = 0;
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: u32 = 0;
    let mut v___x_5396_: u8 = 0;
    let mut v___x_5397_: u32 = 0;
    let mut v___x_5398_: u8 = 0;
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5387_ = lean_string_utf8_at_end(v_s_5370_, v_i_5372_);
                if v___x_5387_ == 0 {
                    v___x_5388_ = lean_string_utf8_get(v_s_5370_, v_i_5372_);
                    v___x_5395_ = 32;
                    v___x_5396_ = lean_uint32_dec_eq(v___x_5388_, v___x_5395_);
                    if v___x_5396_ == 0 {
                        v___x_5397_ = 9;
                        v___x_5398_ = lean_uint32_dec_eq(v___x_5388_, v___x_5397_);
                        v___y_5390_ = v___x_5398_;
                        state = 3;
                        continue;
                    } else {
                        v___y_5390_ = v___x_5396_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5399_ = lean_string_utf8_extract(v_s_5370_, v_b_5371_, v_i_5372_);
                    crate::leanh::lean_dec(v_i_5372_);
                    crate::leanh::lean_dec(v_b_5371_);
                    v___x_5400_ = lean_array_push(v_r_5373_, v___x_5399_);
                    v___x_5401_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5401_, 0, v___x_5400_);
                    crate::leanh::lean_ctor_set(v___x_5401_, 1, v_ws_5374_);
                    return v___x_5401_;
                }
            }
            1 => {
                v___x_5376_ = lean_string_utf8_byte_size(v_s_5370_);
                crate::leanh::lean_inc(v_i_5372_);
                v_e_5377_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_5370_, v___x_5376_, v_i_5372_);
                v___x_5378_ = lean_string_utf8_extract(v_s_5370_, v_b_5371_, v_i_5372_);
                crate::leanh::lean_dec(v_b_5371_);
                v___x_5379_ = lean_array_push(v_r_5373_, v___x_5378_);
                v___x_5380_ = lean_string_utf8_extract(v_s_5370_, v_i_5372_, v_e_5377_);
                crate::leanh::lean_dec(v_i_5372_);
                v___x_5381_ = lean_array_push(v_ws_5374_, v___x_5380_);
                crate::leanh::lean_inc(v_e_5377_);
                v_b_5371_ = v_e_5377_;
                v_i_5372_ = v_e_5377_;
                v_r_5373_ = v___x_5379_;
                v_ws_5374_ = v___x_5381_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_5384_ == 0 {
                    v___x_5385_ = lean_string_utf8_next(v_s_5370_, v_i_5372_);
                    crate::leanh::lean_dec(v_i_5372_);
                    v_i_5372_ = v___x_5385_;
                    state = 0;
                    continue;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_5390_ == 0 {
                    v___x_5391_ = 13;
                    v___x_5392_ = lean_uint32_dec_eq(v___x_5388_, v___x_5391_);
                    if v___x_5392_ == 0 {
                        v___x_5393_ = 10;
                        v___x_5394_ = lean_uint32_dec_eq(v___x_5388_, v___x_5393_);
                        v___y_5384_ = v___x_5394_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5384_ = v___x_5392_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(
    mut v_s_5402_: *mut crate::leanh::LeanObject,
    mut v_b_5403_: *mut crate::leanh::LeanObject,
    mut v_i_5404_: *mut crate::leanh::LeanObject,
    mut v_r_5405_: *mut crate::leanh::LeanObject,
    mut v_ws_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5407_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(
        v_s_5402_, v_b_5403_, v_i_5404_, v_r_5405_, v_ws_5406_,
    );
    crate::leanh::lean_dec_ref(v_s_5402_);
    return v_res_5407_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(
    mut v_s_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5411_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5412_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0;
    v___x_5413_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(
        v_s_5410_,
        v___x_5411_,
        v___x_5411_,
        v___x_5412_,
        v___x_5412_,
    );
    return v___x_5413_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(
    mut v_s_5414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5415_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_5414_);
    crate::leanh::lean_dec_ref(v_s_5414_);
    return v_res_5415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(
    mut v_sz_5416_: usize,
    mut v_i_5417_: usize,
    mut v_bs_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5419_: u8 = 0;
    let mut v_v_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5425_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: usize = 0;
    let mut v___x_5431_: usize = 0;
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: u8 = 0;
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: usize = 0;
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: usize = 0;
    let mut v___x_5451_: usize = 0;
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5419_ = lean_usize_dec_lt(v_i_5417_, v_sz_5416_);
                if v___x_5419_ == 0 {
                    return v_bs_5418_;
                } else {
                    v_v_5420_ = lean_array_uget(v_bs_5418_, v_i_5417_);
                    v_fst_5421_ = crate::leanh::lean_ctor_get(v_v_5420_, 0);
                    v_snd_5422_ = crate::leanh::lean_ctor_get(v_v_5420_, 1);
                    v_isSharedCheck_5456_ = (!crate::leanh::lean_is_exclusive(v_v_5420_)) as u8;
                    if v_isSharedCheck_5456_ == 0 {
                        v___x_5424_ = v_v_5420_;
                        v_isShared_5425_ = v_isSharedCheck_5456_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5422_);
                        crate::leanh::lean_inc(v_fst_5421_);
                        crate::leanh::lean_dec(v_v_5420_);
                        v___x_5424_ = crate::leanh::lean_box(0);
                        v_isShared_5425_ = v_isSharedCheck_5456_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5426_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_5427_ = lean_array_uset(v_bs_5418_, v_i_5417_, v___x_5426_);
                v___x_5434_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
                v___x_5435_ = lean_array_get_size(v_snd_5422_);
                v___x_5436_ = lean_nat_dec_lt(v___x_5426_, v___x_5435_);
                if v___x_5436_ == 0 {
                    crate::leanh::lean_dec(v_snd_5422_);
                    if v_isShared_5425_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5424_, 1, v___x_5434_);
                        v___x_5438_ = v___x_5424_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_fst_5421_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 1, v___x_5434_);
                        v___x_5438_ = v_reuseFailAlloc_5439_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5440_ = lean_nat_dec_le(v___x_5435_, v___x_5435_);
                    if v___x_5440_ == 0 {
                        if v___x_5436_ == 0 {
                            crate::leanh::lean_dec(v_snd_5422_);
                            if v_isShared_5425_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5424_, 1, v___x_5434_);
                                v___x_5442_ = v___x_5424_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_5443_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_fst_5421_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5443_, 1, v___x_5434_);
                                v___x_5442_ = v_reuseFailAlloc_5443_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_5444_ = 0usize;
                            v___x_5445_ = lean_usize_of_nat(v___x_5435_);
                            v___x_5446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_5422_, v___x_5444_, v___x_5445_, v___x_5434_);
                            crate::leanh::lean_dec(v_snd_5422_);
                            if v_isShared_5425_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5424_, 1, v___x_5446_);
                                v___x_5448_ = v___x_5424_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_5449_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5421_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5446_);
                                v___x_5448_ = v_reuseFailAlloc_5449_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_5450_ = 0usize;
                        v___x_5451_ = lean_usize_of_nat(v___x_5435_);
                        v___x_5452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_5422_, v___x_5450_, v___x_5451_, v___x_5434_);
                        crate::leanh::lean_dec(v_snd_5422_);
                        if v_isShared_5425_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5424_, 1, v___x_5452_);
                            v___x_5454_ = v___x_5424_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5455_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_fst_5421_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5452_);
                            v___x_5454_ = v_reuseFailAlloc_5455_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_5430_ = 1usize;
                v___x_5431_ = lean_usize_add(v_i_5417_, v___x_5430_);
                v___x_5432_ = lean_array_uset(v_bs_x27_5427_, v_i_5417_, v___y_5429_);
                v_i_5417_ = v___x_5431_;
                v_bs_5418_ = v___x_5432_;
                state = 0;
                continue;
            }
            3 => {
                v___y_5429_ = v___x_5438_;
                state = 2;
                continue;
            }
            4 => {
                v___y_5429_ = v___x_5442_;
                state = 2;
                continue;
            }
            5 => {
                v___y_5429_ = v___x_5448_;
                state = 2;
                continue;
            }
            6 => {
                v___y_5429_ = v___x_5454_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(
    mut v_sz_5457_: *mut crate::leanh::LeanObject,
    mut v_i_5458_: *mut crate::leanh::LeanObject,
    mut v_bs_5459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5460_: usize = 0;
    let mut v_i_boxed_5461_: usize = 0;
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5460_ = crate::leanh::lean_unbox_usize(v_sz_5457_);
    crate::leanh::lean_dec(v_sz_5457_);
    v_i_boxed_5461_ = crate::leanh::lean_unbox_usize(v_i_5458_);
    crate::leanh::lean_dec(v_i_5458_);
    v_res_5462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_5460_, v_i_boxed_5461_, v_bs_5459_);
    return v_res_5462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(
    mut v_sz_5463_: usize,
    mut v_i_5464_: usize,
    mut v_bs_5465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5466_: u8 = 0;
    let mut v_v_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: usize = 0;
    let mut v___x_5474_: usize = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5466_ = lean_usize_dec_lt(v_i_5464_, v_sz_5463_);
                if v___x_5466_ == 0 {
                    return v_bs_5465_;
                } else {
                    v_v_5467_ = lean_array_uget(v_bs_5465_, v_i_5464_);
                    v___x_5468_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5469_ = lean_array_uset(v_bs_5465_, v_i_5464_, v___x_5468_);
                    v___x_5470_ = 0;
                    v___x_5471_ = crate::leanh::lean_box((v___x_5470_) as usize);
                    v___x_5472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5472_, 0, v___x_5471_);
                    crate::leanh::lean_ctor_set(v___x_5472_, 1, v_v_5467_);
                    v___x_5473_ = 1usize;
                    v___x_5474_ = lean_usize_add(v_i_5464_, v___x_5473_);
                    v___x_5475_ = lean_array_uset(v_bs_x27_5469_, v_i_5464_, v___x_5472_);
                    v_i_5464_ = v___x_5474_;
                    v_bs_5465_ = v___x_5475_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(
    mut v_sz_5477_: *mut crate::leanh::LeanObject,
    mut v_i_5478_: *mut crate::leanh::LeanObject,
    mut v_bs_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5480_: usize = 0;
    let mut v_i_boxed_5481_: usize = 0;
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5480_ = crate::leanh::lean_unbox_usize(v_sz_5477_);
    crate::leanh::lean_dec(v_sz_5477_);
    v_i_boxed_5481_ = crate::leanh::lean_unbox_usize(v_i_5478_);
    crate::leanh::lean_dec(v_i_5478_);
    v_res_5482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_5480_, v_i_boxed_5481_, v_bs_5479_);
    return v_res_5482_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(
    mut v___x_5483_: *mut crate::leanh::LeanObject,
    mut v_original_5484_: *mut crate::leanh::LeanObject,
    mut v_a_5485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5491_: u8 = 0;
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: u8 = 0;
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5486_ = crate::leanh::lean_ctor_get(v_a_5485_, 0);
                v_snd_5487_ = crate::leanh::lean_ctor_get(v_a_5485_, 1);
                v_isSharedCheck_5506_ = (!crate::leanh::lean_is_exclusive(v_a_5485_)) as u8;
                if v_isSharedCheck_5506_ == 0 {
                    v___x_5489_ = v_a_5485_;
                    v_isShared_5490_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5487_);
                    crate::leanh::lean_inc(v_fst_5486_);
                    crate::leanh::lean_dec(v_a_5485_);
                    v___x_5489_ = crate::leanh::lean_box(0);
                    v_isShared_5490_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5491_ = lean_nat_dec_lt(v_snd_5487_, v___x_5483_);
                if v___x_5491_ == 0 {
                    if v_isShared_5490_ == 0 {
                        v___x_5493_ = v___x_5489_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_fst_5486_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5494_, 1, v_snd_5487_);
                        v___x_5493_ = v_reuseFailAlloc_5494_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5495_ = 1;
                    v___x_5496_ = lean_array_fget_borrowed(v_original_5484_, v_snd_5487_);
                    v___x_5497_ = crate::leanh::lean_box((v___x_5495_) as usize);
                    crate::leanh::lean_inc(v___x_5496_);
                    if v_isShared_5490_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5489_, 1, v___x_5496_);
                        crate::leanh::lean_ctor_set(v___x_5489_, 0, v___x_5497_);
                        v___x_5499_ = v___x_5489_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5497_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 1, v___x_5496_);
                        v___x_5499_ = v_reuseFailAlloc_5505_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5493_;
            }
            3 => {
                v___x_5500_ = lean_array_push(v_fst_5486_, v___x_5499_);
                v___x_5501_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5502_ = lean_nat_add(v_snd_5487_, v___x_5501_);
                crate::leanh::lean_dec(v_snd_5487_);
                v___x_5503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5503_, 0, v___x_5500_);
                crate::leanh::lean_ctor_set(v___x_5503_, 1, v___x_5502_);
                v_a_5485_ = v___x_5503_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(
    mut v___x_5507_: *mut crate::leanh::LeanObject,
    mut v_original_5508_: *mut crate::leanh::LeanObject,
    mut v_a_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_5507_, v_original_5508_, v_a_5509_);
    crate::leanh::lean_dec_ref(v_original_5508_);
    crate::leanh::lean_dec(v___x_5507_);
    return v_res_5510_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(
    mut v___x_5511_: *mut crate::leanh::LeanObject,
    mut v_edited_5512_: *mut crate::leanh::LeanObject,
    mut v_a_5513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: u8 = 0;
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5514_ = crate::leanh::lean_ctor_get(v_a_5513_, 0);
                v_snd_5515_ = crate::leanh::lean_ctor_get(v_a_5513_, 1);
                v_isSharedCheck_5534_ = (!crate::leanh::lean_is_exclusive(v_a_5513_)) as u8;
                if v_isSharedCheck_5534_ == 0 {
                    v___x_5517_ = v_a_5513_;
                    v_isShared_5518_ = v_isSharedCheck_5534_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5515_);
                    crate::leanh::lean_inc(v_fst_5514_);
                    crate::leanh::lean_dec(v_a_5513_);
                    v___x_5517_ = crate::leanh::lean_box(0);
                    v_isShared_5518_ = v_isSharedCheck_5534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5519_ = lean_nat_dec_lt(v_snd_5515_, v___x_5511_);
                if v___x_5519_ == 0 {
                    if v_isShared_5518_ == 0 {
                        v___x_5521_ = v___x_5517_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_fst_5514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5522_, 1, v_snd_5515_);
                        v___x_5521_ = v_reuseFailAlloc_5522_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5523_ = 0;
                    v___x_5524_ = lean_array_fget_borrowed(v_edited_5512_, v_snd_5515_);
                    v___x_5525_ = crate::leanh::lean_box((v___x_5523_) as usize);
                    crate::leanh::lean_inc(v___x_5524_);
                    if v_isShared_5518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5517_, 1, v___x_5524_);
                        crate::leanh::lean_ctor_set(v___x_5517_, 0, v___x_5525_);
                        v___x_5527_ = v___x_5517_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5525_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5533_, 1, v___x_5524_);
                        v___x_5527_ = v_reuseFailAlloc_5533_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5521_;
            }
            3 => {
                v___x_5528_ = lean_array_push(v_fst_5514_, v___x_5527_);
                v___x_5529_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5530_ = lean_nat_add(v_snd_5515_, v___x_5529_);
                crate::leanh::lean_dec(v_snd_5515_);
                v___x_5531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5531_, 0, v___x_5528_);
                crate::leanh::lean_ctor_set(v___x_5531_, 1, v___x_5530_);
                v_a_5513_ = v___x_5531_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(
    mut v___x_5535_: *mut crate::leanh::LeanObject,
    mut v_edited_5536_: *mut crate::leanh::LeanObject,
    mut v_a_5537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5538_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_5535_, v_edited_5536_, v_a_5537_);
    crate::leanh::lean_dec_ref(v_edited_5536_);
    crate::leanh::lean_dec(v___x_5535_);
    return v_res_5538_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(
    mut v_edited_5539_: *mut crate::leanh::LeanObject,
    mut v___x_5540_: *mut crate::leanh::LeanObject,
    mut v_a_5541_: *mut crate::leanh::LeanObject,
    mut v_a_5542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: u8 = 0;
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5543_ = crate::leanh::lean_ctor_get(v_a_5542_, 0);
                v_snd_5544_ = crate::leanh::lean_ctor_get(v_a_5542_, 1);
                v_isSharedCheck_5569_ = (!crate::leanh::lean_is_exclusive(v_a_5542_)) as u8;
                if v_isSharedCheck_5569_ == 0 {
                    v___x_5546_ = v_a_5542_;
                    v_isShared_5547_ = v_isSharedCheck_5569_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5544_);
                    crate::leanh::lean_inc(v_fst_5543_);
                    crate::leanh::lean_dec(v_a_5542_);
                    v___x_5546_ = crate::leanh::lean_box(0);
                    v_isShared_5547_ = v_isSharedCheck_5569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5548_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
                v___x_5565_ = lean_nat_dec_lt(v_snd_5544_, v___x_5540_);
                if v___x_5565_ == 0 {
                    v___y_5550_ = v___x_5565_;
                    state = 2;
                    continue;
                } else {
                    v___x_5566_ = lean_array_get_borrowed(v___x_5548_, v_edited_5539_, v_snd_5544_);
                    v___x_5567_ = lean_string_dec_eq(v___x_5566_, v_a_5541_);
                    if v___x_5567_ == 0 {
                        v___y_5550_ = v___x_5565_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5546_);
                        v___x_5568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5568_, 0, v_fst_5543_);
                        crate::leanh::lean_ctor_set(v___x_5568_, 1, v_snd_5544_);
                        return v___x_5568_;
                    }
                }
            }
            2 => {
                if v___y_5550_ == 0 {
                    if v_isShared_5547_ == 0 {
                        v___x_5552_ = v___x_5546_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_fst_5543_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 1, v_snd_5544_);
                        v___x_5552_ = v_reuseFailAlloc_5553_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5554_ = 0;
                    v___x_5555_ = lean_array_get_borrowed(v___x_5548_, v_edited_5539_, v_snd_5544_);
                    v___x_5556_ = crate::leanh::lean_box((v___x_5554_) as usize);
                    crate::leanh::lean_inc(v___x_5555_);
                    if v_isShared_5547_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5546_, 1, v___x_5555_);
                        crate::leanh::lean_ctor_set(v___x_5546_, 0, v___x_5556_);
                        v___x_5558_ = v___x_5546_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5556_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 1, v___x_5555_);
                        v___x_5558_ = v_reuseFailAlloc_5564_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5552_;
            }
            4 => {
                v___x_5559_ = lean_array_push(v_fst_5543_, v___x_5558_);
                v___x_5560_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5561_ = lean_nat_add(v_snd_5544_, v___x_5560_);
                crate::leanh::lean_dec(v_snd_5544_);
                v___x_5562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5562_, 0, v___x_5559_);
                crate::leanh::lean_ctor_set(v___x_5562_, 1, v___x_5561_);
                v_a_5542_ = v___x_5562_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(
    mut v_edited_5570_: *mut crate::leanh::LeanObject,
    mut v___x_5571_: *mut crate::leanh::LeanObject,
    mut v_a_5572_: *mut crate::leanh::LeanObject,
    mut v_a_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5574_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_5570_, v___x_5571_, v_a_5572_, v_a_5573_);
    crate::leanh::lean_dec_ref(v_a_5572_);
    crate::leanh::lean_dec(v___x_5571_);
    crate::leanh::lean_dec_ref(v_edited_5570_);
    return v_res_5574_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(
    mut v_original_5575_: *mut crate::leanh::LeanObject,
    mut v___x_5576_: *mut crate::leanh::LeanObject,
    mut v_a_5577_: *mut crate::leanh::LeanObject,
    mut v_a_5578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5586_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: u8 = 0;
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: u8 = 0;
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5579_ = crate::leanh::lean_ctor_get(v_a_5578_, 0);
                v_snd_5580_ = crate::leanh::lean_ctor_get(v_a_5578_, 1);
                v_isSharedCheck_5605_ = (!crate::leanh::lean_is_exclusive(v_a_5578_)) as u8;
                if v_isSharedCheck_5605_ == 0 {
                    v___x_5582_ = v_a_5578_;
                    v_isShared_5583_ = v_isSharedCheck_5605_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5580_);
                    crate::leanh::lean_inc(v_fst_5579_);
                    crate::leanh::lean_dec(v_a_5578_);
                    v___x_5582_ = crate::leanh::lean_box(0);
                    v_isShared_5583_ = v_isSharedCheck_5605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5584_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
                v___x_5601_ = lean_nat_dec_lt(v_snd_5580_, v___x_5576_);
                if v___x_5601_ == 0 {
                    v___y_5586_ = v___x_5601_;
                    state = 2;
                    continue;
                } else {
                    v___x_5602_ =
                        lean_array_get_borrowed(v___x_5584_, v_original_5575_, v_snd_5580_);
                    v___x_5603_ = lean_string_dec_eq(v___x_5602_, v_a_5577_);
                    if v___x_5603_ == 0 {
                        v___y_5586_ = v___x_5601_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5582_);
                        v___x_5604_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5604_, 0, v_fst_5579_);
                        crate::leanh::lean_ctor_set(v___x_5604_, 1, v_snd_5580_);
                        return v___x_5604_;
                    }
                }
            }
            2 => {
                if v___y_5586_ == 0 {
                    if v_isShared_5583_ == 0 {
                        v___x_5588_ = v___x_5582_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_fst_5579_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 1, v_snd_5580_);
                        v___x_5588_ = v_reuseFailAlloc_5589_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5590_ = 1;
                    v___x_5591_ =
                        lean_array_get_borrowed(v___x_5584_, v_original_5575_, v_snd_5580_);
                    v___x_5592_ = crate::leanh::lean_box((v___x_5590_) as usize);
                    crate::leanh::lean_inc(v___x_5591_);
                    if v_isShared_5583_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5582_, 1, v___x_5591_);
                        crate::leanh::lean_ctor_set(v___x_5582_, 0, v___x_5592_);
                        v___x_5594_ = v___x_5582_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5600_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5592_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___x_5591_);
                        v___x_5594_ = v_reuseFailAlloc_5600_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5588_;
            }
            4 => {
                v___x_5595_ = lean_array_push(v_fst_5579_, v___x_5594_);
                v___x_5596_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5597_ = lean_nat_add(v_snd_5580_, v___x_5596_);
                crate::leanh::lean_dec(v_snd_5580_);
                v___x_5598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5598_, 0, v___x_5595_);
                crate::leanh::lean_ctor_set(v___x_5598_, 1, v___x_5597_);
                v_a_5578_ = v___x_5598_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(
    mut v_original_5606_: *mut crate::leanh::LeanObject,
    mut v___x_5607_: *mut crate::leanh::LeanObject,
    mut v_a_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5610_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_5606_, v___x_5607_, v_a_5608_, v_a_5609_);
    crate::leanh::lean_dec_ref(v_a_5608_);
    crate::leanh::lean_dec(v___x_5607_);
    crate::leanh::lean_dec_ref(v_original_5606_);
    return v_res_5610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(
    mut v_original_5611_: *mut crate::leanh::LeanObject,
    mut v___x_5612_: *mut crate::leanh::LeanObject,
    mut v_edited_5613_: *mut crate::leanh::LeanObject,
    mut v___x_5614_: *mut crate::leanh::LeanObject,
    mut v_as_5615_: *mut crate::leanh::LeanObject,
    mut v_sz_5616_: usize,
    mut v_i_5617_: usize,
    mut v_b_5618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5619_: u8 = 0;
    let mut v_snd_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_fst_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5629_: u8 = 0;
    let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5638_: u8 = 0;
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v___x_5647_: u8 = 0;
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: usize = 0;
    let mut v___x_5659_: usize = 0;
    let mut v_reuseFailAlloc_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5663_: u8 = 0;
    let mut v_reuseFailAlloc_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut v_reuseFailAlloc_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_isSharedCheck_5668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5619_ = lean_usize_dec_lt(v_i_5617_, v_sz_5616_);
                if v___x_5619_ == 0 {
                    return v_b_5618_;
                } else {
                    v_snd_5620_ = crate::leanh::lean_ctor_get(v_b_5618_, 1);
                    v_fst_5621_ = crate::leanh::lean_ctor_get(v_b_5618_, 0);
                    v_isSharedCheck_5668_ = (!crate::leanh::lean_is_exclusive(v_b_5618_)) as u8;
                    if v_isSharedCheck_5668_ == 0 {
                        v___x_5623_ = v_b_5618_;
                        v_isShared_5624_ = v_isSharedCheck_5668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5620_);
                        crate::leanh::lean_inc(v_fst_5621_);
                        crate::leanh::lean_dec(v_b_5618_);
                        v___x_5623_ = crate::leanh::lean_box(0);
                        v_isShared_5624_ = v_isSharedCheck_5668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5625_ = crate::leanh::lean_ctor_get(v_snd_5620_, 0);
                v_snd_5626_ = crate::leanh::lean_ctor_get(v_snd_5620_, 1);
                v_isSharedCheck_5667_ = (!crate::leanh::lean_is_exclusive(v_snd_5620_)) as u8;
                if v_isSharedCheck_5667_ == 0 {
                    v___x_5628_ = v_snd_5620_;
                    v_isShared_5629_ = v_isSharedCheck_5667_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5626_);
                    crate::leanh::lean_inc(v_fst_5625_);
                    crate::leanh::lean_dec(v_snd_5620_);
                    v___x_5628_ = crate::leanh::lean_box(0);
                    v_isShared_5629_ = v_isSharedCheck_5667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5630_ = lean_array_uget_borrowed(v_as_5615_, v_i_5617_);
                if v_isShared_5629_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5628_, 1, v_fst_5625_);
                    crate::leanh::lean_ctor_set(v___x_5628_, 0, v_fst_5621_);
                    v___x_5632_ = v___x_5628_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_fst_5621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_fst_5625_);
                    v___x_5632_ = v_reuseFailAlloc_5666_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5633_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_5611_, v___x_5612_, v_a_5630_, v___x_5632_);
                v_fst_5634_ = crate::leanh::lean_ctor_get(v___x_5633_, 0);
                v_snd_5635_ = crate::leanh::lean_ctor_get(v___x_5633_, 1);
                v_isSharedCheck_5665_ = (!crate::leanh::lean_is_exclusive(v___x_5633_)) as u8;
                if v_isSharedCheck_5665_ == 0 {
                    v___x_5637_ = v___x_5633_;
                    v_isShared_5638_ = v_isSharedCheck_5665_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5635_);
                    crate::leanh::lean_inc(v_fst_5634_);
                    crate::leanh::lean_dec(v___x_5633_);
                    v___x_5637_ = crate::leanh::lean_box(0);
                    v_isShared_5638_ = v_isSharedCheck_5665_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5637_, 1, v_snd_5626_);
                    v___x_5640_ = v___x_5637_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_fst_5634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_snd_5626_);
                    v___x_5640_ = v_reuseFailAlloc_5664_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5641_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_5613_, v___x_5614_, v_a_5630_, v___x_5640_);
                v_fst_5642_ = crate::leanh::lean_ctor_get(v___x_5641_, 0);
                v_snd_5643_ = crate::leanh::lean_ctor_get(v___x_5641_, 1);
                v_isSharedCheck_5663_ = (!crate::leanh::lean_is_exclusive(v___x_5641_)) as u8;
                if v_isSharedCheck_5663_ == 0 {
                    v___x_5645_ = v___x_5641_;
                    v_isShared_5646_ = v_isSharedCheck_5663_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5643_);
                    crate::leanh::lean_inc(v_fst_5642_);
                    crate::leanh::lean_dec(v___x_5641_);
                    v___x_5645_ = crate::leanh::lean_box(0);
                    v_isShared_5646_ = v_isSharedCheck_5663_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5647_ = 2;
                v___x_5648_ = crate::leanh::lean_box((v___x_5647_) as usize);
                crate::leanh::lean_inc(v_a_5630_);
                if v_isShared_5646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5645_, 1, v_a_5630_);
                    crate::leanh::lean_ctor_set(v___x_5645_, 0, v___x_5648_);
                    v___x_5650_ = v___x_5645_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_a_5630_);
                    v___x_5650_ = v_reuseFailAlloc_5662_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5651_ = lean_array_push(v_fst_5642_, v___x_5650_);
                v___x_5652_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5653_ = lean_nat_add(v_snd_5635_, v___x_5652_);
                crate::leanh::lean_dec(v_snd_5635_);
                v___x_5654_ = lean_nat_add(v_snd_5643_, v___x_5652_);
                crate::leanh::lean_dec(v_snd_5643_);
                if v_isShared_5624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5623_, 1, v___x_5654_);
                    crate::leanh::lean_ctor_set(v___x_5623_, 0, v___x_5653_);
                    v___x_5656_ = v___x_5623_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 1, v___x_5654_);
                    v___x_5656_ = v_reuseFailAlloc_5661_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5657_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5657_, 0, v___x_5651_);
                crate::leanh::lean_ctor_set(v___x_5657_, 1, v___x_5656_);
                v___x_5658_ = 1usize;
                v___x_5659_ = lean_usize_add(v_i_5617_, v___x_5658_);
                v_i_5617_ = v___x_5659_;
                v_b_5618_ = v___x_5657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(
    mut v_original_5669_: *mut crate::leanh::LeanObject,
    mut v___x_5670_: *mut crate::leanh::LeanObject,
    mut v_edited_5671_: *mut crate::leanh::LeanObject,
    mut v___x_5672_: *mut crate::leanh::LeanObject,
    mut v_as_5673_: *mut crate::leanh::LeanObject,
    mut v_sz_5674_: *mut crate::leanh::LeanObject,
    mut v_i_5675_: *mut crate::leanh::LeanObject,
    mut v_b_5676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5677_: usize = 0;
    let mut v_i_boxed_5678_: usize = 0;
    let mut v_res_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5677_ = crate::leanh::lean_unbox_usize(v_sz_5674_);
    crate::leanh::lean_dec(v_sz_5674_);
    v_i_boxed_5678_ = crate::leanh::lean_unbox_usize(v_i_5675_);
    crate::leanh::lean_dec(v_i_5675_);
    v_res_5679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_5669_, v___x_5670_, v_edited_5671_, v___x_5672_, v_as_5673_, v_sz_boxed_5677_, v_i_boxed_5678_, v_b_5676_);
    crate::leanh::lean_dec_ref(v_as_5673_);
    crate::leanh::lean_dec(v___x_5672_);
    crate::leanh::lean_dec_ref(v_edited_5671_);
    crate::leanh::lean_dec(v___x_5670_);
    crate::leanh::lean_dec_ref(v_original_5669_);
    return v_res_5679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(
    mut v_edited_5680_: *mut crate::leanh::LeanObject,
    mut v___x_5681_: *mut crate::leanh::LeanObject,
    mut v_original_5682_: *mut crate::leanh::LeanObject,
    mut v___x_5683_: *mut crate::leanh::LeanObject,
    mut v_as_5684_: *mut crate::leanh::LeanObject,
    mut v_sz_5685_: usize,
    mut v_i_5686_: usize,
    mut v_b_5687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5688_: u8 = 0;
    let mut v_snd_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5693_: u8 = 0;
    let mut v_fst_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5698_: u8 = 0;
    let mut v_a_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5715_: u8 = 0;
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: usize = 0;
    let mut v___x_5728_: usize = 0;
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5732_: u8 = 0;
    let mut v_reuseFailAlloc_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5734_: u8 = 0;
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut v_isSharedCheck_5737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5688_ = lean_usize_dec_lt(v_i_5686_, v_sz_5685_);
                if v___x_5688_ == 0 {
                    return v_b_5687_;
                } else {
                    v_snd_5689_ = crate::leanh::lean_ctor_get(v_b_5687_, 1);
                    v_fst_5690_ = crate::leanh::lean_ctor_get(v_b_5687_, 0);
                    v_isSharedCheck_5737_ = (!crate::leanh::lean_is_exclusive(v_b_5687_)) as u8;
                    if v_isSharedCheck_5737_ == 0 {
                        v___x_5692_ = v_b_5687_;
                        v_isShared_5693_ = v_isSharedCheck_5737_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5689_);
                        crate::leanh::lean_inc(v_fst_5690_);
                        crate::leanh::lean_dec(v_b_5687_);
                        v___x_5692_ = crate::leanh::lean_box(0);
                        v_isShared_5693_ = v_isSharedCheck_5737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5694_ = crate::leanh::lean_ctor_get(v_snd_5689_, 0);
                v_snd_5695_ = crate::leanh::lean_ctor_get(v_snd_5689_, 1);
                v_isSharedCheck_5736_ = (!crate::leanh::lean_is_exclusive(v_snd_5689_)) as u8;
                if v_isSharedCheck_5736_ == 0 {
                    v___x_5697_ = v_snd_5689_;
                    v_isShared_5698_ = v_isSharedCheck_5736_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5695_);
                    crate::leanh::lean_inc(v_fst_5694_);
                    crate::leanh::lean_dec(v_snd_5689_);
                    v___x_5697_ = crate::leanh::lean_box(0);
                    v_isShared_5698_ = v_isSharedCheck_5736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5699_ = lean_array_uget_borrowed(v_as_5684_, v_i_5686_);
                if v_isShared_5698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5697_, 1, v_fst_5694_);
                    crate::leanh::lean_ctor_set(v___x_5697_, 0, v_fst_5690_);
                    v___x_5701_ = v___x_5697_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_fst_5690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_fst_5694_);
                    v___x_5701_ = v_reuseFailAlloc_5735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5702_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_5682_, v___x_5683_, v_a_5699_, v___x_5701_);
                v_fst_5703_ = crate::leanh::lean_ctor_get(v___x_5702_, 0);
                v_snd_5704_ = crate::leanh::lean_ctor_get(v___x_5702_, 1);
                v_isSharedCheck_5734_ = (!crate::leanh::lean_is_exclusive(v___x_5702_)) as u8;
                if v_isSharedCheck_5734_ == 0 {
                    v___x_5706_ = v___x_5702_;
                    v_isShared_5707_ = v_isSharedCheck_5734_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5704_);
                    crate::leanh::lean_inc(v_fst_5703_);
                    crate::leanh::lean_dec(v___x_5702_);
                    v___x_5706_ = crate::leanh::lean_box(0);
                    v_isShared_5707_ = v_isSharedCheck_5734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5707_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5706_, 1, v_snd_5695_);
                    v___x_5709_ = v___x_5706_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_fst_5703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5733_, 1, v_snd_5695_);
                    v___x_5709_ = v_reuseFailAlloc_5733_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5710_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_5680_, v___x_5681_, v_a_5699_, v___x_5709_);
                v_fst_5711_ = crate::leanh::lean_ctor_get(v___x_5710_, 0);
                v_snd_5712_ = crate::leanh::lean_ctor_get(v___x_5710_, 1);
                v_isSharedCheck_5732_ = (!crate::leanh::lean_is_exclusive(v___x_5710_)) as u8;
                if v_isSharedCheck_5732_ == 0 {
                    v___x_5714_ = v___x_5710_;
                    v_isShared_5715_ = v_isSharedCheck_5732_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5712_);
                    crate::leanh::lean_inc(v_fst_5711_);
                    crate::leanh::lean_dec(v___x_5710_);
                    v___x_5714_ = crate::leanh::lean_box(0);
                    v_isShared_5715_ = v_isSharedCheck_5732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5716_ = 2;
                v___x_5717_ = crate::leanh::lean_box((v___x_5716_) as usize);
                crate::leanh::lean_inc(v_a_5699_);
                if v_isShared_5715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5714_, 1, v_a_5699_);
                    crate::leanh::lean_ctor_set(v___x_5714_, 0, v___x_5717_);
                    v___x_5719_ = v___x_5714_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 0, v___x_5717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 1, v_a_5699_);
                    v___x_5719_ = v_reuseFailAlloc_5731_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5720_ = lean_array_push(v_fst_5711_, v___x_5719_);
                v___x_5721_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5722_ = lean_nat_add(v_snd_5704_, v___x_5721_);
                crate::leanh::lean_dec(v_snd_5704_);
                v___x_5723_ = lean_nat_add(v_snd_5712_, v___x_5721_);
                crate::leanh::lean_dec(v_snd_5712_);
                if v_isShared_5693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5692_, 1, v___x_5723_);
                    crate::leanh::lean_ctor_set(v___x_5692_, 0, v___x_5722_);
                    v___x_5725_ = v___x_5692_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5730_, 0, v___x_5722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5730_, 1, v___x_5723_);
                    v___x_5725_ = v_reuseFailAlloc_5730_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5726_, 0, v___x_5720_);
                crate::leanh::lean_ctor_set(v___x_5726_, 1, v___x_5725_);
                v___x_5727_ = 1usize;
                v___x_5728_ = lean_usize_add(v_i_5686_, v___x_5727_);
                v___x_5729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_5682_, v___x_5683_, v_edited_5680_, v___x_5681_, v_as_5684_, v_sz_5685_, v___x_5728_, v___x_5726_);
                return v___x_5729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(
    mut v_edited_5738_: *mut crate::leanh::LeanObject,
    mut v___x_5739_: *mut crate::leanh::LeanObject,
    mut v_original_5740_: *mut crate::leanh::LeanObject,
    mut v___x_5741_: *mut crate::leanh::LeanObject,
    mut v_as_5742_: *mut crate::leanh::LeanObject,
    mut v_sz_5743_: *mut crate::leanh::LeanObject,
    mut v_i_5744_: *mut crate::leanh::LeanObject,
    mut v_b_5745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5746_: usize = 0;
    let mut v_i_boxed_5747_: usize = 0;
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5746_ = crate::leanh::lean_unbox_usize(v_sz_5743_);
    crate::leanh::lean_dec(v_sz_5743_);
    v_i_boxed_5747_ = crate::leanh::lean_unbox_usize(v_i_5744_);
    crate::leanh::lean_dec(v_i_5744_);
    v_res_5748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_5738_, v___x_5739_, v_original_5740_, v___x_5741_, v_as_5742_, v_sz_boxed_5746_, v_i_boxed_5747_, v_b_5745_);
    crate::leanh::lean_dec_ref(v_as_5742_);
    crate::leanh::lean_dec(v___x_5741_);
    crate::leanh::lean_dec_ref(v_original_5740_);
    crate::leanh::lean_dec(v___x_5739_);
    crate::leanh::lean_dec_ref(v_edited_5738_);
    return v_res_5748_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(
    mut v_a_5749_: *mut crate::leanh::LeanObject,
    mut v_b_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5757_: u8 = 0;
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5751_ = crate::leanh::lean_ctor_get(v_a_5749_, 0);
                v_start_5752_ = crate::leanh::lean_ctor_get(v_a_5749_, 1);
                v_stop_5753_ = crate::leanh::lean_ctor_get(v_a_5749_, 2);
                v_isSharedCheck_5766_ = (!crate::leanh::lean_is_exclusive(v_a_5749_)) as u8;
                if v_isSharedCheck_5766_ == 0 {
                    v___x_5755_ = v_a_5749_;
                    v_isShared_5756_ = v_isSharedCheck_5766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_5753_);
                    crate::leanh::lean_inc(v_start_5752_);
                    crate::leanh::lean_inc(v_array_5751_);
                    crate::leanh::lean_dec(v_a_5749_);
                    v___x_5755_ = crate::leanh::lean_box(0);
                    v_isShared_5756_ = v_isSharedCheck_5766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5757_ = lean_nat_dec_lt(v_start_5752_, v_stop_5753_);
                if v___x_5757_ == 0 {
                    crate::leanh::lean_del_object(v___x_5755_);
                    crate::leanh::lean_dec(v_stop_5753_);
                    crate::leanh::lean_dec(v_start_5752_);
                    crate::leanh::lean_dec_ref(v_array_5751_);
                    return v_b_5750_;
                } else {
                    v___x_5758_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5759_ = lean_nat_add(v_start_5752_, v___x_5758_);
                    crate::leanh::lean_inc_ref(v_array_5751_);
                    if v_isShared_5756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5755_, 1, v___x_5759_);
                        v___x_5761_ = v___x_5755_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_array_5751_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 1, v___x_5759_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 2, v_stop_5753_);
                        v___x_5761_ = v_reuseFailAlloc_5765_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5762_ = lean_array_fget(v_array_5751_, v_start_5752_);
                crate::leanh::lean_dec(v_start_5752_);
                crate::leanh::lean_dec_ref(v_array_5751_);
                v___x_5763_ = lean_array_push(v_b_5750_, v___x_5762_);
                v_a_5749_ = v___x_5761_;
                v_b_5750_ = v___x_5763_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(
    mut v_left_5767_: *mut crate::leanh::LeanObject,
    mut v_right_5768_: *mut crate::leanh::LeanObject,
    mut v_i_5769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v_start_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: u8 = 0;
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_5770_ = crate::leanh::lean_ctor_get(v_left_5767_, 1);
                v_stop_5771_ = crate::leanh::lean_ctor_get(v_left_5767_, 2);
                v___x_5772_ = lean_nat_sub(v_stop_5771_, v_start_5770_);
                v___x_5786_ = lean_nat_dec_lt(v_i_5769_, v___x_5772_);
                if v___x_5786_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_start_5787_ = crate::leanh::lean_ctor_get(v_right_5768_, 1);
                    v_stop_5788_ = crate::leanh::lean_ctor_get(v_right_5768_, 2);
                    v___x_5789_ = lean_nat_sub(v_stop_5788_, v_start_5787_);
                    v___x_5790_ = lean_nat_dec_lt(v_i_5769_, v___x_5789_);
                    if v___x_5790_ == 0 {
                        crate::leanh::lean_dec(v___x_5789_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5791_ = lean_nat_sub(v___x_5772_, v_i_5769_);
                        crate::leanh::lean_dec(v___x_5772_);
                        v___x_5792_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5793_ = lean_nat_sub(v___x_5791_, v___x_5792_);
                        v___x_5794_ = l_Subarray_get___redArg(v_left_5767_, v___x_5793_);
                        crate::leanh::lean_dec(v___x_5793_);
                        v___x_5795_ = lean_nat_sub(v___x_5789_, v_i_5769_);
                        crate::leanh::lean_dec(v___x_5789_);
                        v___x_5796_ = lean_nat_sub(v___x_5795_, v___x_5792_);
                        v___x_5797_ = l_Subarray_get___redArg(v_right_5768_, v___x_5796_);
                        crate::leanh::lean_dec(v___x_5796_);
                        v___x_5798_ = lean_string_dec_eq(v___x_5794_, v___x_5797_);
                        crate::leanh::lean_dec(v___x_5797_);
                        crate::leanh::lean_dec(v___x_5794_);
                        if v___x_5798_ == 0 {
                            crate::leanh::lean_dec(v_i_5769_);
                            crate::leanh::lean_inc_ref(v_left_5767_);
                            v___x_5799_ = l_Subarray_take___redArg(v_left_5767_, v___x_5791_);
                            v___x_5800_ = l_Subarray_take___redArg(v_right_5768_, v___x_5795_);
                            crate::leanh::lean_dec(v___x_5795_);
                            v___x_5801_ = l_Subarray_drop___redArg(v_left_5767_, v___x_5791_);
                            crate::leanh::lean_dec(v___x_5791_);
                            v___x_5802_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0;
                            v___x_5803_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_5801_, v___x_5802_);
                            v___x_5804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5804_, 0, v___x_5800_);
                            crate::leanh::lean_ctor_set(v___x_5804_, 1, v___x_5803_);
                            v___x_5805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5805_, 0, v___x_5799_);
                            crate::leanh::lean_ctor_set(v___x_5805_, 1, v___x_5804_);
                            return v___x_5805_;
                        } else {
                            crate::leanh::lean_dec(v___x_5795_);
                            crate::leanh::lean_dec(v___x_5791_);
                            v___x_5806_ = lean_nat_add(v_i_5769_, v___x_5792_);
                            crate::leanh::lean_dec(v_i_5769_);
                            v_i_5769_ = v___x_5806_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_start_5774_ = crate::leanh::lean_ctor_get(v_right_5768_, 1);
                v_stop_5775_ = crate::leanh::lean_ctor_get(v_right_5768_, 2);
                v___x_5776_ = lean_nat_sub(v___x_5772_, v_i_5769_);
                crate::leanh::lean_dec(v___x_5772_);
                crate::leanh::lean_inc_ref(v_left_5767_);
                v___x_5777_ = l_Subarray_take___redArg(v_left_5767_, v___x_5776_);
                v___x_5778_ = lean_nat_sub(v_stop_5775_, v_start_5774_);
                v___x_5779_ = lean_nat_sub(v___x_5778_, v_i_5769_);
                crate::leanh::lean_dec(v_i_5769_);
                crate::leanh::lean_dec(v___x_5778_);
                v___x_5780_ = l_Subarray_take___redArg(v_right_5768_, v___x_5779_);
                crate::leanh::lean_dec(v___x_5779_);
                v___x_5781_ = l_Subarray_drop___redArg(v_left_5767_, v___x_5776_);
                crate::leanh::lean_dec(v___x_5776_);
                v___x_5782_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0;
                v___x_5783_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_5781_, v___x_5782_);
                v___x_5784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5784_, 0, v___x_5780_);
                crate::leanh::lean_ctor_set(v___x_5784_, 1, v___x_5783_);
                v___x_5785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5785_, 0, v___x_5777_);
                crate::leanh::lean_ctor_set(v___x_5785_, 1, v___x_5784_);
                return v___x_5785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(
    mut v_left_5808_: *mut crate::leanh::LeanObject,
    mut v_right_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5810_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5811_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_5808_, v_right_5809_, v___x_5810_);
    return v___x_5811_;
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(
    mut v_left_5812_: *mut crate::leanh::LeanObject,
    mut v_right_5813_: *mut crate::leanh::LeanObject,
    mut v_pref_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v_start_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: u8 = 0;
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_5815_ = crate::leanh::lean_ctor_get(v_left_5812_, 1);
                v_stop_5816_ = crate::leanh::lean_ctor_get(v_left_5812_, 2);
                v_i_5817_ = lean_array_get_size(v_pref_5814_);
                v___x_5823_ = lean_nat_sub(v_stop_5816_, v_start_5815_);
                v___x_5824_ = lean_nat_dec_lt(v_i_5817_, v___x_5823_);
                crate::leanh::lean_dec(v___x_5823_);
                if v___x_5824_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_start_5825_ = crate::leanh::lean_ctor_get(v_right_5813_, 1);
                    v_stop_5826_ = crate::leanh::lean_ctor_get(v_right_5813_, 2);
                    v___x_5827_ = lean_nat_sub(v_stop_5826_, v_start_5825_);
                    v___x_5828_ = lean_nat_dec_lt(v_i_5817_, v___x_5827_);
                    crate::leanh::lean_dec(v___x_5827_);
                    if v___x_5828_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_5829_ = l_Subarray_get___redArg(v_left_5812_, v_i_5817_);
                        v___x_5830_ = l_Subarray_get___redArg(v_right_5813_, v_i_5817_);
                        v___x_5831_ = lean_string_dec_eq(v___x_5829_, v___x_5830_);
                        crate::leanh::lean_dec(v___x_5830_);
                        if v___x_5831_ == 0 {
                            crate::leanh::lean_dec(v___x_5829_);
                            v___x_5832_ = l_Subarray_drop___redArg(v_left_5812_, v_i_5817_);
                            v___x_5833_ = l_Subarray_drop___redArg(v_right_5813_, v_i_5817_);
                            v___x_5834_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5834_, 0, v___x_5832_);
                            crate::leanh::lean_ctor_set(v___x_5834_, 1, v___x_5833_);
                            v___x_5835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5835_, 0, v_pref_5814_);
                            crate::leanh::lean_ctor_set(v___x_5835_, 1, v___x_5834_);
                            return v___x_5835_;
                        } else {
                            v___x_5836_ = lean_array_push(v_pref_5814_, v___x_5829_);
                            v_pref_5814_ = v___x_5836_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5819_ = l_Subarray_drop___redArg(v_left_5812_, v_i_5817_);
                v___x_5820_ = l_Subarray_drop___redArg(v_right_5813_, v_i_5817_);
                v___x_5821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5821_, 0, v___x_5819_);
                crate::leanh::lean_ctor_set(v___x_5821_, 1, v___x_5820_);
                v___x_5822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5822_, 0, v_pref_5814_);
                crate::leanh::lean_ctor_set(v___x_5822_, 1, v___x_5821_);
                return v___x_5822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(
    mut v_left_5838_: *mut crate::leanh::LeanObject,
    mut v_right_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5840_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0;
    v___x_5841_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_5838_, v_right_5839_, v___x_5840_);
    return v___x_5841_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(
    mut v_as_x27_5842_: *mut crate::leanh::LeanObject,
    mut v_b_5843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftCount_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftCount_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: u8 = 0;
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v_unused_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5888_: u8 = 0;
    let mut v_unused_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5842_) == 0 {
                    return v_b_5843_;
                } else {
                    v_head_5844_ = crate::leanh::lean_ctor_get(v_as_x27_5842_, 0);
                    v_snd_5845_ = crate::leanh::lean_ctor_get(v_head_5844_, 1);
                    v_leftIndex_5846_ = crate::leanh::lean_ctor_get(v_snd_5845_, 1);
                    if crate::leanh::lean_obj_tag(v_leftIndex_5846_) == 1 {
                        v_rightIndex_5847_ = crate::leanh::lean_ctor_get(v_snd_5845_, 3);
                        if crate::leanh::lean_obj_tag(v_rightIndex_5847_) == 1 {
                            if crate::leanh::lean_obj_tag(v_b_5843_) == 0 {
                                v_tail_5848_ = crate::leanh::lean_ctor_get(v_as_x27_5842_, 1);
                                v_fst_5849_ = crate::leanh::lean_ctor_get(v_head_5844_, 0);
                                v_leftCount_5850_ = crate::leanh::lean_ctor_get(v_snd_5845_, 0);
                                v_rightCount_5851_ = crate::leanh::lean_ctor_get(v_snd_5845_, 2);
                                v_val_5852_ = crate::leanh::lean_ctor_get(v_leftIndex_5846_, 0);
                                v_val_5853_ = crate::leanh::lean_ctor_get(v_rightIndex_5847_, 0);
                                v___x_5854_ = lean_nat_add(v_leftCount_5850_, v_rightCount_5851_);
                                crate::leanh::lean_inc(v_val_5853_);
                                crate::leanh::lean_inc(v_val_5852_);
                                v___x_5855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5855_, 0, v_val_5852_);
                                crate::leanh::lean_ctor_set(v___x_5855_, 1, v_val_5853_);
                                crate::leanh::lean_inc(v_fst_5849_);
                                v___x_5856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5856_, 0, v_fst_5849_);
                                crate::leanh::lean_ctor_set(v___x_5856_, 1, v___x_5855_);
                                v___x_5857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5857_, 0, v___x_5854_);
                                crate::leanh::lean_ctor_set(v___x_5857_, 1, v___x_5856_);
                                v___x_5858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5858_, 0, v___x_5857_);
                                v_as_x27_5842_ = v_tail_5848_;
                                v_b_5843_ = v___x_5858_;
                                state = 0;
                                continue;
                            } else {
                                v_val_5860_ = crate::leanh::lean_ctor_get(v_b_5843_, 0);
                                crate::leanh::lean_inc(v_val_5860_);
                                v_tail_5861_ = crate::leanh::lean_ctor_get(v_as_x27_5842_, 1);
                                v_fst_5862_ = crate::leanh::lean_ctor_get(v_head_5844_, 0);
                                v_leftCount_5863_ = crate::leanh::lean_ctor_get(v_snd_5845_, 0);
                                v_rightCount_5864_ = crate::leanh::lean_ctor_get(v_snd_5845_, 2);
                                v_val_5865_ = crate::leanh::lean_ctor_get(v_leftIndex_5846_, 0);
                                v_val_5866_ = crate::leanh::lean_ctor_get(v_rightIndex_5847_, 0);
                                v_fst_5867_ = crate::leanh::lean_ctor_get(v_val_5860_, 0);
                                v_isSharedCheck_5888_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_5860_)) as u8;
                                if v_isSharedCheck_5888_ == 0 {
                                    v_unused_5889_ = crate::leanh::lean_ctor_get(v_val_5860_, 1);
                                    crate::leanh::lean_dec(v_unused_5889_);
                                    v___x_5869_ = v_val_5860_;
                                    v_isShared_5870_ = v_isSharedCheck_5888_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fst_5867_);
                                    crate::leanh::lean_dec(v_val_5860_);
                                    v___x_5869_ = crate::leanh::lean_box(0);
                                    v_isShared_5870_ = v_isSharedCheck_5888_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_tail_5890_ = crate::leanh::lean_ctor_get(v_as_x27_5842_, 1);
                            v_as_x27_5842_ = v_tail_5890_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_5892_ = crate::leanh::lean_ctor_get(v_as_x27_5842_, 1);
                        v_as_x27_5842_ = v_tail_5892_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5871_ = lean_nat_add(v_leftCount_5863_, v_rightCount_5864_);
                v___x_5872_ = lean_nat_dec_lt(v___x_5871_, v_fst_5867_);
                crate::leanh::lean_dec(v_fst_5867_);
                if v___x_5872_ == 0 {
                    crate::leanh::lean_dec(v___x_5871_);
                    crate::leanh::lean_del_object(v___x_5869_);
                    v_as_x27_5842_ = v_tail_5861_;
                    state = 0;
                    continue;
                } else {
                    v_isSharedCheck_5886_ = (!crate::leanh::lean_is_exclusive(v_b_5843_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v_unused_5887_ = crate::leanh::lean_ctor_get(v_b_5843_, 0);
                        crate::leanh::lean_dec(v_unused_5887_);
                        v___x_5875_ = v_b_5843_;
                        v_isShared_5876_ = v_isSharedCheck_5886_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_5843_);
                        v___x_5875_ = crate::leanh::lean_box(0);
                        v_isShared_5876_ = v_isSharedCheck_5886_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_val_5866_);
                crate::leanh::lean_inc(v_val_5865_);
                if v_isShared_5870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5869_, 1, v_val_5866_);
                    crate::leanh::lean_ctor_set(v___x_5869_, 0, v_val_5865_);
                    v___x_5878_ = v___x_5869_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_val_5865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 1, v_val_5866_);
                    v___x_5878_ = v_reuseFailAlloc_5885_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_fst_5862_);
                v___x_5879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5879_, 0, v_fst_5862_);
                crate::leanh::lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                v___x_5880_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5880_, 0, v___x_5871_);
                crate::leanh::lean_ctor_set(v___x_5880_, 1, v___x_5879_);
                if v_isShared_5876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5880_);
                    v___x_5882_ = v___x_5875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5880_);
                    v___x_5882_ = v_reuseFailAlloc_5884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_as_x27_5842_ = v_tail_5861_;
                v_b_5843_ = v___x_5882_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_5894_: *mut crate::leanh::LeanObject,
    mut v_b_5895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5896_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_5894_, v_b_5895_);
    crate::leanh::lean_dec(v_as_x27_5894_);
    return v_res_5896_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_b_5898_: *mut crate::leanh::LeanObject,
    mut v_x_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___x_5906_: u8 = 0;
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5914_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5899_) == 0 {
                    crate::leanh::lean_dec(v_b_5898_);
                    crate::leanh::lean_dec_ref(v_a_5897_);
                    return v_x_5899_;
                } else {
                    v_key_5900_ = crate::leanh::lean_ctor_get(v_x_5899_, 0);
                    v_value_5901_ = crate::leanh::lean_ctor_get(v_x_5899_, 1);
                    v_tail_5902_ = crate::leanh::lean_ctor_get(v_x_5899_, 2);
                    v_isSharedCheck_5914_ = (!crate::leanh::lean_is_exclusive(v_x_5899_)) as u8;
                    if v_isSharedCheck_5914_ == 0 {
                        v___x_5904_ = v_x_5899_;
                        v_isShared_5905_ = v_isSharedCheck_5914_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5902_);
                        crate::leanh::lean_inc(v_value_5901_);
                        crate::leanh::lean_inc(v_key_5900_);
                        crate::leanh::lean_dec(v_x_5899_);
                        v___x_5904_ = crate::leanh::lean_box(0);
                        v_isShared_5905_ = v_isSharedCheck_5914_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5906_ = lean_string_dec_eq(v_key_5900_, v_a_5897_);
                if v___x_5906_ == 0 {
                    v___x_5907_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_5897_, v_b_5898_, v_tail_5902_);
                    if v_isShared_5905_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5904_, 2, v___x_5907_);
                        v___x_5909_ = v___x_5904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5910_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_key_5900_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5910_, 1, v_value_5901_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5910_, 2, v___x_5907_);
                        v___x_5909_ = v_reuseFailAlloc_5910_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_5901_);
                    crate::leanh::lean_dec(v_key_5900_);
                    if v_isShared_5905_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5904_, 1, v_b_5898_);
                        crate::leanh::lean_ctor_set(v___x_5904_, 0, v_a_5897_);
                        v___x_5912_ = v___x_5904_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5913_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5897_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5913_, 1, v_b_5898_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5913_, 2, v_tail_5902_);
                        v___x_5912_ = v_reuseFailAlloc_5913_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5909_;
            }
            3 => {
                return v___x_5912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(
    mut v_a_5915_: *mut crate::leanh::LeanObject,
    mut v_x_5916_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5917_: u8 = 0;
    let mut v_key_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5916_) == 0 {
                    v___x_5917_ = 0;
                    return v___x_5917_;
                } else {
                    v_key_5918_ = crate::leanh::lean_ctor_get(v_x_5916_, 0);
                    v_tail_5919_ = crate::leanh::lean_ctor_get(v_x_5916_, 2);
                    v___x_5920_ = lean_string_dec_eq(v_key_5918_, v_a_5915_);
                    if v___x_5920_ == 0 {
                        v_x_5916_ = v_tail_5919_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5920_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(
    mut v_a_5922_: *mut crate::leanh::LeanObject,
    mut v_x_5923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5924_: u8 = 0;
    let mut v_r_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_5922_, v_x_5923_);
    crate::leanh::lean_dec(v_x_5923_);
    crate::leanh::lean_dec_ref(v_a_5922_);
    v_r_5925_ = crate::leanh::lean_box((v_res_5924_) as usize);
    return v_r_5925_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(
    mut v_x_5926_: *mut crate::leanh::LeanObject,
    mut v_x_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u64 = 0;
    let mut v___x_5936_: u64 = 0;
    let mut v___x_5937_: u64 = 0;
    let mut v_fold_5938_: u64 = 0;
    let mut v___x_5939_: u64 = 0;
    let mut v___x_5940_: u64 = 0;
    let mut v___x_5941_: u64 = 0;
    let mut v___x_5942_: usize = 0;
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: usize = 0;
    let mut v___x_5945_: usize = 0;
    let mut v___x_5946_: usize = 0;
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5927_) == 0 {
                    return v_x_5926_;
                } else {
                    v_key_5928_ = crate::leanh::lean_ctor_get(v_x_5927_, 0);
                    v_value_5929_ = crate::leanh::lean_ctor_get(v_x_5927_, 1);
                    v_tail_5930_ = crate::leanh::lean_ctor_get(v_x_5927_, 2);
                    v_isSharedCheck_5953_ = (!crate::leanh::lean_is_exclusive(v_x_5927_)) as u8;
                    if v_isSharedCheck_5953_ == 0 {
                        v___x_5932_ = v_x_5927_;
                        v_isShared_5933_ = v_isSharedCheck_5953_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5930_);
                        crate::leanh::lean_inc(v_value_5929_);
                        crate::leanh::lean_inc(v_key_5928_);
                        crate::leanh::lean_dec(v_x_5927_);
                        v___x_5932_ = crate::leanh::lean_box(0);
                        v_isShared_5933_ = v_isSharedCheck_5953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5934_ = lean_array_get_size(v_x_5926_);
                v___x_5935_ = lean_string_hash(v_key_5928_);
                v___x_5936_ = 32u64;
                v___x_5937_ = lean_uint64_shift_right(v___x_5935_, v___x_5936_);
                v_fold_5938_ = lean_uint64_xor(v___x_5935_, v___x_5937_);
                v___x_5939_ = 16u64;
                v___x_5940_ = lean_uint64_shift_right(v_fold_5938_, v___x_5939_);
                v___x_5941_ = lean_uint64_xor(v_fold_5938_, v___x_5940_);
                v___x_5942_ = lean_uint64_to_usize(v___x_5941_);
                v___x_5943_ = lean_usize_of_nat(v___x_5934_);
                v___x_5944_ = 1usize;
                v___x_5945_ = lean_usize_sub(v___x_5943_, v___x_5944_);
                v___x_5946_ = lean_usize_land(v___x_5942_, v___x_5945_);
                v___x_5947_ = lean_array_uget_borrowed(v_x_5926_, v___x_5946_);
                crate::leanh::lean_inc(v___x_5947_);
                if v_isShared_5933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5932_, 2, v___x_5947_);
                    v___x_5949_ = v___x_5932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5952_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_key_5928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5952_, 1, v_value_5929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5952_, 2, v___x_5947_);
                    v___x_5949_ = v_reuseFailAlloc_5952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5950_ = lean_array_uset(v_x_5926_, v___x_5946_, v___x_5949_);
                v_x_5926_ = v___x_5950_;
                v_x_5927_ = v_tail_5930_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(
    mut v_i_5954_: *mut crate::leanh::LeanObject,
    mut v_source_5955_: *mut crate::leanh::LeanObject,
    mut v_target_5956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: u8 = 0;
    let mut v_es_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5957_ = lean_array_get_size(v_source_5955_);
                v___x_5958_ = lean_nat_dec_lt(v_i_5954_, v___x_5957_);
                if v___x_5958_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5955_);
                    crate::leanh::lean_dec(v_i_5954_);
                    return v_target_5956_;
                } else {
                    v_es_5959_ = lean_array_fget(v_source_5955_, v_i_5954_);
                    v___x_5960_ = crate::leanh::lean_box(0);
                    v_source_5961_ = lean_array_fset(v_source_5955_, v_i_5954_, v___x_5960_);
                    v_target_5962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_5956_, v_es_5959_);
                    v___x_5963_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5964_ = lean_nat_add(v_i_5954_, v___x_5963_);
                    crate::leanh::lean_dec(v_i_5954_);
                    v_i_5954_ = v___x_5964_;
                    v_source_5955_ = v_source_5961_;
                    v_target_5956_ = v_target_5962_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(
    mut v_data_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5967_ = lean_array_get_size(v_data_5966_);
    v___x_5968_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5969_ = lean_nat_mul(v___x_5967_, v___x_5968_);
    v___x_5970_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5971_ = crate::leanh::lean_box(0);
    v___x_5972_ = lean_mk_array(v_nbuckets_5969_, v___x_5971_);
    v___x_5973_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_5970_, v_data_5966_, v___x_5972_);
    return v___x_5973_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(
    mut v_m_5974_: *mut crate::leanh::LeanObject,
    mut v_a_5975_: *mut crate::leanh::LeanObject,
    mut v_b_5976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5981_: u8 = 0;
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u64 = 0;
    let mut v___x_5984_: u64 = 0;
    let mut v___x_5985_: u64 = 0;
    let mut v_fold_5986_: u64 = 0;
    let mut v___x_5987_: u64 = 0;
    let mut v___x_5988_: u64 = 0;
    let mut v___x_5989_: u64 = 0;
    let mut v___x_5990_: usize = 0;
    let mut v___x_5991_: usize = 0;
    let mut v___x_5992_: usize = 0;
    let mut v___x_5993_: usize = 0;
    let mut v___x_5994_: usize = 0;
    let mut v_bkt_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: u8 = 0;
    let mut v_val_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5977_ = crate::leanh::lean_ctor_get(v_m_5974_, 0);
                v_buckets_5978_ = crate::leanh::lean_ctor_get(v_m_5974_, 1);
                v_isSharedCheck_6021_ = (!crate::leanh::lean_is_exclusive(v_m_5974_)) as u8;
                if v_isSharedCheck_6021_ == 0 {
                    v___x_5980_ = v_m_5974_;
                    v_isShared_5981_ = v_isSharedCheck_6021_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5978_);
                    crate::leanh::lean_inc(v_size_5977_);
                    crate::leanh::lean_dec(v_m_5974_);
                    v___x_5980_ = crate::leanh::lean_box(0);
                    v_isShared_5981_ = v_isSharedCheck_6021_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5982_ = lean_array_get_size(v_buckets_5978_);
                v___x_5983_ = lean_string_hash(v_a_5975_);
                v___x_5984_ = 32u64;
                v___x_5985_ = lean_uint64_shift_right(v___x_5983_, v___x_5984_);
                v_fold_5986_ = lean_uint64_xor(v___x_5983_, v___x_5985_);
                v___x_5987_ = 16u64;
                v___x_5988_ = lean_uint64_shift_right(v_fold_5986_, v___x_5987_);
                v___x_5989_ = lean_uint64_xor(v_fold_5986_, v___x_5988_);
                v___x_5990_ = lean_uint64_to_usize(v___x_5989_);
                v___x_5991_ = lean_usize_of_nat(v___x_5982_);
                v___x_5992_ = 1usize;
                v___x_5993_ = lean_usize_sub(v___x_5991_, v___x_5992_);
                v___x_5994_ = lean_usize_land(v___x_5990_, v___x_5993_);
                v_bkt_5995_ = lean_array_uget_borrowed(v_buckets_5978_, v___x_5994_);
                v___x_5996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_5975_, v_bkt_5995_);
                if v___x_5996_ == 0 {
                    v___x_5997_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5998_ = lean_nat_add(v_size_5977_, v___x_5997_);
                    crate::leanh::lean_dec(v_size_5977_);
                    crate::leanh::lean_inc(v_bkt_5995_);
                    v___x_5999_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5999_, 0, v_a_5975_);
                    crate::leanh::lean_ctor_set(v___x_5999_, 1, v_b_5976_);
                    crate::leanh::lean_ctor_set(v___x_5999_, 2, v_bkt_5995_);
                    v_buckets_x27_6000_ =
                        lean_array_uset(v_buckets_5978_, v___x_5994_, v___x_5999_);
                    v___x_6001_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_6002_ = lean_nat_mul(v_size_x27_5998_, v___x_6001_);
                    v___x_6003_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6004_ = lean_nat_div(v___x_6002_, v___x_6003_);
                    crate::leanh::lean_dec(v___x_6002_);
                    v___x_6005_ = lean_array_get_size(v_buckets_x27_6000_);
                    v___x_6006_ = lean_nat_dec_le(v___x_6004_, v___x_6005_);
                    crate::leanh::lean_dec(v___x_6004_);
                    if v___x_6006_ == 0 {
                        v_val_6007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_6000_);
                        if v_isShared_5981_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5980_, 1, v_val_6007_);
                            crate::leanh::lean_ctor_set(v___x_5980_, 0, v_size_x27_5998_);
                            v___x_6009_ = v___x_5980_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6010_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6010_,
                                0,
                                v_size_x27_5998_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 1, v_val_6007_);
                            v___x_6009_ = v_reuseFailAlloc_6010_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5981_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5980_, 1, v_buckets_x27_6000_);
                            crate::leanh::lean_ctor_set(v___x_5980_, 0, v_size_x27_5998_);
                            v___x_6012_ = v___x_5980_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6013_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6013_,
                                0,
                                v_size_x27_5998_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6013_,
                                1,
                                v_buckets_x27_6000_,
                            );
                            v___x_6012_ = v_reuseFailAlloc_6013_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5995_);
                    v___x_6014_ = crate::leanh::lean_box(0);
                    v_buckets_x27_6015_ =
                        lean_array_uset(v_buckets_5978_, v___x_5994_, v___x_6014_);
                    v___x_6016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_5975_, v_b_5976_, v_bkt_5995_);
                    v___x_6017_ = lean_array_uset(v_buckets_x27_6015_, v___x_5994_, v___x_6016_);
                    if v_isShared_5981_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5980_, 1, v___x_6017_);
                        v___x_6019_ = v___x_5980_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_size_5977_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6020_, 1, v___x_6017_);
                        v___x_6019_ = v_reuseFailAlloc_6020_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6009_;
            }
            3 => {
                return v___x_6012_;
            }
            4 => {
                return v___x_6019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(
    mut v_a_6022_: *mut crate::leanh::LeanObject,
    mut v_x_6023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6023_) == 0 {
                    v___x_6024_ = crate::leanh::lean_box(0);
                    return v___x_6024_;
                } else {
                    v_key_6025_ = crate::leanh::lean_ctor_get(v_x_6023_, 0);
                    v_value_6026_ = crate::leanh::lean_ctor_get(v_x_6023_, 1);
                    v_tail_6027_ = crate::leanh::lean_ctor_get(v_x_6023_, 2);
                    v___x_6028_ = lean_string_dec_eq(v_key_6025_, v_a_6022_);
                    if v___x_6028_ == 0 {
                        v_x_6023_ = v_tail_6027_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6026_);
                        v___x_6030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6030_, 0, v_value_6026_);
                        return v___x_6030_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(
    mut v_a_6031_: *mut crate::leanh::LeanObject,
    mut v_x_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6033_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_6031_, v_x_6032_);
    crate::leanh::lean_dec(v_x_6032_);
    crate::leanh::lean_dec_ref(v_a_6031_);
    return v_res_6033_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(
    mut v_m_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: u64 = 0;
    let mut v___x_6039_: u64 = 0;
    let mut v___x_6040_: u64 = 0;
    let mut v_fold_6041_: u64 = 0;
    let mut v___x_6042_: u64 = 0;
    let mut v___x_6043_: u64 = 0;
    let mut v___x_6044_: u64 = 0;
    let mut v___x_6045_: usize = 0;
    let mut v___x_6046_: usize = 0;
    let mut v___x_6047_: usize = 0;
    let mut v___x_6048_: usize = 0;
    let mut v___x_6049_: usize = 0;
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_6036_ = crate::leanh::lean_ctor_get(v_m_6034_, 1);
    v___x_6037_ = lean_array_get_size(v_buckets_6036_);
    v___x_6038_ = lean_string_hash(v_a_6035_);
    v___x_6039_ = 32u64;
    v___x_6040_ = lean_uint64_shift_right(v___x_6038_, v___x_6039_);
    v_fold_6041_ = lean_uint64_xor(v___x_6038_, v___x_6040_);
    v___x_6042_ = 16u64;
    v___x_6043_ = lean_uint64_shift_right(v_fold_6041_, v___x_6042_);
    v___x_6044_ = lean_uint64_xor(v_fold_6041_, v___x_6043_);
    v___x_6045_ = lean_uint64_to_usize(v___x_6044_);
    v___x_6046_ = lean_usize_of_nat(v___x_6037_);
    v___x_6047_ = 1usize;
    v___x_6048_ = lean_usize_sub(v___x_6046_, v___x_6047_);
    v___x_6049_ = lean_usize_land(v___x_6045_, v___x_6048_);
    v___x_6050_ = lean_array_uget_borrowed(v_buckets_6036_, v___x_6049_);
    v___x_6051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_6035_, v___x_6050_);
    return v___x_6051_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(
    mut v_m_6052_: *mut crate::leanh::LeanObject,
    mut v_a_6053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_6052_, v_a_6053_);
    crate::leanh::lean_dec_ref(v_a_6053_);
    crate::leanh::lean_dec_ref(v_m_6052_);
    return v_res_6054_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(
    mut v_histogram_6055_: *mut crate::leanh::LeanObject,
    mut v_index_6056_: *mut crate::leanh::LeanObject,
    mut v_val_6057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6068_: u8 = 0;
    let mut v_leftCount_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6084_: u8 = 0;
    let mut v_unused_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_6055_, v_val_6057_);
                if crate::leanh::lean_obj_tag(v___x_6058_) == 0 {
                    v___x_6059_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6060_, 0, v_index_6056_);
                    v___x_6061_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6062_ = crate::leanh::lean_box(0);
                    v___x_6063_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6063_, 0, v___x_6059_);
                    crate::leanh::lean_ctor_set(v___x_6063_, 1, v___x_6060_);
                    crate::leanh::lean_ctor_set(v___x_6063_, 2, v___x_6061_);
                    crate::leanh::lean_ctor_set(v___x_6063_, 3, v___x_6062_);
                    v___x_6064_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_6055_, v_val_6057_, v___x_6063_);
                    return v___x_6064_;
                } else {
                    v_val_6065_ = crate::leanh::lean_ctor_get(v___x_6058_, 0);
                    v_isSharedCheck_6086_ = (!crate::leanh::lean_is_exclusive(v___x_6058_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6067_ = v___x_6058_;
                        v_isShared_6068_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6065_);
                        crate::leanh::lean_dec(v___x_6058_);
                        v___x_6067_ = crate::leanh::lean_box(0);
                        v_isShared_6068_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_6069_ = crate::leanh::lean_ctor_get(v_val_6065_, 0);
                v_rightCount_6070_ = crate::leanh::lean_ctor_get(v_val_6065_, 2);
                v_rightIndex_6071_ = crate::leanh::lean_ctor_get(v_val_6065_, 3);
                v_isSharedCheck_6084_ = (!crate::leanh::lean_is_exclusive(v_val_6065_)) as u8;
                if v_isSharedCheck_6084_ == 0 {
                    v_unused_6085_ = crate::leanh::lean_ctor_get(v_val_6065_, 1);
                    crate::leanh::lean_dec(v_unused_6085_);
                    v___x_6073_ = v_val_6065_;
                    v_isShared_6074_ = v_isSharedCheck_6084_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rightIndex_6071_);
                    crate::leanh::lean_inc(v_rightCount_6070_);
                    crate::leanh::lean_inc(v_leftCount_6069_);
                    crate::leanh::lean_dec(v_val_6065_);
                    v___x_6073_ = crate::leanh::lean_box(0);
                    v_isShared_6074_ = v_isSharedCheck_6084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6075_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6076_ = lean_nat_add(v_leftCount_6069_, v___x_6075_);
                crate::leanh::lean_dec(v_leftCount_6069_);
                if v_isShared_6068_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6067_, 0, v_index_6056_);
                    v___x_6078_ = v___x_6067_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6083_, 0, v_index_6056_);
                    v___x_6078_ = v_reuseFailAlloc_6083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6073_, 1, v___x_6078_);
                    crate::leanh::lean_ctor_set(v___x_6073_, 0, v___x_6076_);
                    v___x_6080_ = v___x_6073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6082_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6082_, 0, v___x_6076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6082_, 1, v___x_6078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6082_, 2, v_rightCount_6070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6082_, 3, v_rightIndex_6071_);
                    v___x_6080_ = v_reuseFailAlloc_6082_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6081_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_6055_, v_val_6057_, v___x_6080_);
                return v___x_6081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(
    mut v_upperBound_6087_: *mut crate::leanh::LeanObject,
    mut v_fst_6088_: *mut crate::leanh::LeanObject,
    mut v___x_6089_: *mut crate::leanh::LeanObject,
    mut v_fst_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_b_6092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6093_: u8 = 0;
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6093_ = lean_nat_dec_lt(v_a_6091_, v_upperBound_6087_);
                if v___x_6093_ == 0 {
                    crate::leanh::lean_dec(v_a_6091_);
                    return v_b_6092_;
                } else {
                    v___x_6094_ = l_Subarray_get___redArg(v_fst_6090_, v_a_6091_);
                    crate::leanh::lean_inc(v_a_6091_);
                    v___x_6095_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_6092_, v_a_6091_, v___x_6094_);
                    v___x_6096_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6097_ = lean_nat_add(v_a_6091_, v___x_6096_);
                    crate::leanh::lean_dec(v_a_6091_);
                    v_a_6091_ = v___x_6097_;
                    v_b_6092_ = v___x_6095_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(
    mut v_upperBound_6099_: *mut crate::leanh::LeanObject,
    mut v_fst_6100_: *mut crate::leanh::LeanObject,
    mut v___x_6101_: *mut crate::leanh::LeanObject,
    mut v_fst_6102_: *mut crate::leanh::LeanObject,
    mut v_a_6103_: *mut crate::leanh::LeanObject,
    mut v_b_6104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_6099_, v_fst_6100_, v___x_6101_, v_fst_6102_, v_a_6103_, v_b_6104_);
    crate::leanh::lean_dec_ref(v_fst_6102_);
    crate::leanh::lean_dec(v___x_6101_);
    crate::leanh::lean_dec_ref(v_fst_6100_);
    crate::leanh::lean_dec(v_upperBound_6099_);
    return v_res_6105_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(
    mut v_x_6106_: *mut crate::leanh::LeanObject,
    mut v_x_6107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6107_) == 0 {
        crate::leanh::lean_inc(v_x_6106_);
        return v_x_6106_;
    } else {
        let mut v_key_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_6108_ = crate::leanh::lean_ctor_get(v_x_6107_, 0);
        v_value_6109_ = crate::leanh::lean_ctor_get(v_x_6107_, 1);
        v_tail_6110_ = crate::leanh::lean_ctor_get(v_x_6107_, 2);
        v___x_6111_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_6106_, v_tail_6110_);
        crate::leanh::lean_inc(v_value_6109_);
        crate::leanh::lean_inc(v_key_6108_);
        v___x_6112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6112_, 0, v_key_6108_);
        crate::leanh::lean_ctor_set(v___x_6112_, 1, v_value_6109_);
        v___x_6113_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6113_, 0, v___x_6112_);
        crate::leanh::lean_ctor_set(v___x_6113_, 1, v___x_6111_);
        return v___x_6113_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(
    mut v_x_6114_: *mut crate::leanh::LeanObject,
    mut v_x_6115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6116_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_6114_, v_x_6115_);
    crate::leanh::lean_dec(v_x_6115_);
    crate::leanh::lean_dec(v_x_6114_);
    return v_res_6116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(
    mut v_as_6117_: *mut crate::leanh::LeanObject,
    mut v_i_6118_: usize,
    mut v_stop_6119_: usize,
    mut v_b_6120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6121_: u8 = 0;
    let mut v___x_6122_: usize = 0;
    let mut v___x_6123_: usize = 0;
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6121_ = lean_usize_dec_eq(v_i_6118_, v_stop_6119_);
                if v___x_6121_ == 0 {
                    v___x_6122_ = 1usize;
                    v___x_6123_ = lean_usize_sub(v_i_6118_, v___x_6122_);
                    v___x_6124_ = lean_array_uget_borrowed(v_as_6117_, v___x_6123_);
                    v___x_6125_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_6120_, v___x_6124_);
                    crate::leanh::lean_dec(v_b_6120_);
                    v_i_6118_ = v___x_6123_;
                    v_b_6120_ = v___x_6125_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6120_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(
    mut v_as_6127_: *mut crate::leanh::LeanObject,
    mut v_i_6128_: *mut crate::leanh::LeanObject,
    mut v_stop_6129_: *mut crate::leanh::LeanObject,
    mut v_b_6130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6131_: usize = 0;
    let mut v_stop_boxed_6132_: usize = 0;
    let mut v_res_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6131_ = crate::leanh::lean_unbox_usize(v_i_6128_);
    crate::leanh::lean_dec(v_i_6128_);
    v_stop_boxed_6132_ = crate::leanh::lean_unbox_usize(v_stop_6129_);
    crate::leanh::lean_dec(v_stop_6129_);
    v_res_6133_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_6127_, v_i_boxed_6131_, v_stop_boxed_6132_, v_b_6130_);
    crate::leanh::lean_dec_ref(v_as_6127_);
    return v_res_6133_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(
    mut v_histogram_6134_: *mut crate::leanh::LeanObject,
    mut v_index_6135_: *mut crate::leanh::LeanObject,
    mut v_val_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6147_: u8 = 0;
    let mut v_leftCount_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6152_: u8 = 0;
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6162_: u8 = 0;
    let mut v_unused_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_6134_, v_val_6136_);
                if crate::leanh::lean_obj_tag(v___x_6137_) == 0 {
                    v___x_6138_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6139_ = crate::leanh::lean_box(0);
                    v___x_6140_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6141_, 0, v_index_6135_);
                    v___x_6142_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6138_);
                    crate::leanh::lean_ctor_set(v___x_6142_, 1, v___x_6139_);
                    crate::leanh::lean_ctor_set(v___x_6142_, 2, v___x_6140_);
                    crate::leanh::lean_ctor_set(v___x_6142_, 3, v___x_6141_);
                    v___x_6143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_6134_, v_val_6136_, v___x_6142_);
                    return v___x_6143_;
                } else {
                    v_val_6144_ = crate::leanh::lean_ctor_get(v___x_6137_, 0);
                    v_isSharedCheck_6165_ = (!crate::leanh::lean_is_exclusive(v___x_6137_)) as u8;
                    if v_isSharedCheck_6165_ == 0 {
                        v___x_6146_ = v___x_6137_;
                        v_isShared_6147_ = v_isSharedCheck_6165_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6144_);
                        crate::leanh::lean_dec(v___x_6137_);
                        v___x_6146_ = crate::leanh::lean_box(0);
                        v_isShared_6147_ = v_isSharedCheck_6165_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_6148_ = crate::leanh::lean_ctor_get(v_val_6144_, 0);
                v_leftIndex_6149_ = crate::leanh::lean_ctor_get(v_val_6144_, 1);
                v_isSharedCheck_6162_ = (!crate::leanh::lean_is_exclusive(v_val_6144_)) as u8;
                if v_isSharedCheck_6162_ == 0 {
                    v_unused_6163_ = crate::leanh::lean_ctor_get(v_val_6144_, 3);
                    crate::leanh::lean_dec(v_unused_6163_);
                    v_unused_6164_ = crate::leanh::lean_ctor_get(v_val_6144_, 2);
                    crate::leanh::lean_dec(v_unused_6164_);
                    v___x_6151_ = v_val_6144_;
                    v_isShared_6152_ = v_isSharedCheck_6162_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_leftIndex_6149_);
                    crate::leanh::lean_inc(v_leftCount_6148_);
                    crate::leanh::lean_dec(v_val_6144_);
                    v___x_6151_ = crate::leanh::lean_box(0);
                    v_isShared_6152_ = v_isSharedCheck_6162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6153_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6154_ = lean_nat_add(v_leftCount_6148_, v___x_6153_);
                if v_isShared_6147_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6146_, 0, v_index_6135_);
                    v___x_6156_ = v___x_6146_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6161_, 0, v_index_6135_);
                    v___x_6156_ = v_reuseFailAlloc_6161_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6151_, 3, v___x_6156_);
                    crate::leanh::lean_ctor_set(v___x_6151_, 2, v___x_6154_);
                    v___x_6158_ = v___x_6151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6160_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 0, v_leftCount_6148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 1, v_leftIndex_6149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 2, v___x_6154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 3, v___x_6156_);
                    v___x_6158_ = v_reuseFailAlloc_6160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6159_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_6134_, v_val_6136_, v___x_6158_);
                return v___x_6159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(
    mut v_upperBound_6166_: *mut crate::leanh::LeanObject,
    mut v___x_6167_: *mut crate::leanh::LeanObject,
    mut v_fst_6168_: *mut crate::leanh::LeanObject,
    mut v___x_6169_: *mut crate::leanh::LeanObject,
    mut v_a_6170_: *mut crate::leanh::LeanObject,
    mut v_b_6171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6172_: u8 = 0;
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6172_ = lean_nat_dec_lt(v_a_6170_, v_upperBound_6166_);
                if v___x_6172_ == 0 {
                    crate::leanh::lean_dec(v_a_6170_);
                    return v_b_6171_;
                } else {
                    v___x_6173_ = l_Subarray_get___redArg(v_fst_6168_, v_a_6170_);
                    crate::leanh::lean_inc(v_a_6170_);
                    v___x_6174_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_6171_, v_a_6170_, v___x_6173_);
                    v___x_6175_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6176_ = lean_nat_add(v_a_6170_, v___x_6175_);
                    crate::leanh::lean_dec(v_a_6170_);
                    v_a_6170_ = v___x_6176_;
                    v_b_6171_ = v___x_6174_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(
    mut v_upperBound_6178_: *mut crate::leanh::LeanObject,
    mut v___x_6179_: *mut crate::leanh::LeanObject,
    mut v_fst_6180_: *mut crate::leanh::LeanObject,
    mut v___x_6181_: *mut crate::leanh::LeanObject,
    mut v_a_6182_: *mut crate::leanh::LeanObject,
    mut v_b_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_6178_, v___x_6179_, v_fst_6180_, v___x_6181_, v_a_6182_, v_b_6183_);
    crate::leanh::lean_dec(v___x_6181_);
    crate::leanh::lean_dec_ref(v_fst_6180_);
    crate::leanh::lean_dec(v___x_6179_);
    crate::leanh::lean_dec(v_upperBound_6178_);
    return v_res_6184_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6185_ = crate::leanh::lean_box(0);
    v___x_6186_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6187_ = lean_mk_array(v___x_6186_, v___x_6185_);
    return v___x_6187_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once), _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
    v___x_6189_ = crate::leanh::lean_unsigned_to_nat(0);
    v_hist_6190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_hist_6190_, 0, v___x_6189_);
    crate::leanh::lean_ctor_set(v_hist_6190_, 1, v___x_6188_);
    return v_hist_6190_;
}
pub unsafe fn l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(
    mut v_left_6191_: *mut crate::leanh::LeanObject,
    mut v_right_6192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: u8 = 0;
    let mut v___x_6245_: usize = 0;
    let mut v___x_6246_: usize = 0;
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6193_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_6191_, v_right_6192_);
                v_snd_6194_ = crate::leanh::lean_ctor_get(v___x_6193_, 1);
                crate::leanh::lean_inc(v_snd_6194_);
                v_fst_6195_ = crate::leanh::lean_ctor_get(v___x_6193_, 0);
                crate::leanh::lean_inc(v_fst_6195_);
                crate::leanh::lean_dec_ref(v___x_6193_);
                v_fst_6196_ = crate::leanh::lean_ctor_get(v_snd_6194_, 0);
                crate::leanh::lean_inc(v_fst_6196_);
                v_snd_6197_ = crate::leanh::lean_ctor_get(v_snd_6194_, 1);
                crate::leanh::lean_inc(v_snd_6197_);
                crate::leanh::lean_dec(v_snd_6194_);
                v___x_6198_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_6196_, v_snd_6197_);
                v_snd_6199_ = crate::leanh::lean_ctor_get(v___x_6198_, 1);
                crate::leanh::lean_inc(v_snd_6199_);
                v_fst_6200_ = crate::leanh::lean_ctor_get(v___x_6198_, 0);
                crate::leanh::lean_inc(v_fst_6200_);
                crate::leanh::lean_dec_ref(v___x_6198_);
                v_fst_6201_ = crate::leanh::lean_ctor_get(v_snd_6199_, 0);
                crate::leanh::lean_inc(v_fst_6201_);
                v_snd_6202_ = crate::leanh::lean_ctor_get(v_snd_6199_, 1);
                crate::leanh::lean_inc(v_snd_6202_);
                crate::leanh::lean_dec(v_snd_6199_);
                v_start_6203_ = crate::leanh::lean_ctor_get(v_fst_6200_, 1);
                v_stop_6204_ = crate::leanh::lean_ctor_get(v_fst_6200_, 2);
                v___x_6205_ = crate::leanh::lean_unsigned_to_nat(0);
                v_hist_6206_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once), _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
                v___x_6207_ = lean_nat_sub(v_stop_6204_, v_start_6203_);
                v___x_6208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_6207_, v_fst_6201_, v___x_6207_, v_fst_6200_, v___x_6205_, v_hist_6206_);
                v_start_6209_ = crate::leanh::lean_ctor_get(v_fst_6201_, 1);
                v_stop_6210_ = crate::leanh::lean_ctor_get(v_fst_6201_, 2);
                v___x_6211_ = lean_nat_sub(v_stop_6210_, v_start_6209_);
                v___x_6212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_6211_, v___x_6211_, v_fst_6201_, v___x_6207_, v___x_6205_, v___x_6208_);
                crate::leanh::lean_dec(v___x_6207_);
                crate::leanh::lean_dec(v___x_6211_);
                v_buckets_6213_ = crate::leanh::lean_ctor_get(v___x_6212_, 1);
                crate::leanh::lean_inc_ref(v_buckets_6213_);
                crate::leanh::lean_dec_ref(v___x_6212_);
                v___x_6214_ = crate::leanh::lean_box(0);
                v___x_6242_ = crate::leanh::lean_box(0);
                v___x_6243_ = lean_array_get_size(v_buckets_6213_);
                v___x_6244_ = lean_nat_dec_lt(v___x_6205_, v___x_6243_);
                if v___x_6244_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_6213_);
                    v___y_6216_ = v___x_6242_;
                    state = 1;
                    continue;
                } else {
                    v___x_6245_ = lean_usize_of_nat(v___x_6243_);
                    v___x_6246_ = 0usize;
                    v___x_6247_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_6213_, v___x_6245_, v___x_6246_, v___x_6242_);
                    crate::leanh::lean_dec_ref(v_buckets_6213_);
                    v___y_6216_ = v___x_6247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6217_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_6216_, v___x_6214_);
                crate::leanh::lean_dec(v___y_6216_);
                if crate::leanh::lean_obj_tag(v___x_6217_) == 1 {
                    v_val_6218_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
                    crate::leanh::lean_inc(v_val_6218_);
                    crate::leanh::lean_dec_ref_known(v___x_6217_, 1);
                    v_snd_6219_ = crate::leanh::lean_ctor_get(v_val_6218_, 1);
                    crate::leanh::lean_inc(v_snd_6219_);
                    crate::leanh::lean_dec(v_val_6218_);
                    v_snd_6220_ = crate::leanh::lean_ctor_get(v_snd_6219_, 1);
                    crate::leanh::lean_inc(v_snd_6220_);
                    v_fst_6221_ = crate::leanh::lean_ctor_get(v_snd_6219_, 0);
                    crate::leanh::lean_inc(v_fst_6221_);
                    crate::leanh::lean_dec(v_snd_6219_);
                    v_fst_6222_ = crate::leanh::lean_ctor_get(v_snd_6220_, 0);
                    crate::leanh::lean_inc(v_fst_6222_);
                    v_snd_6223_ = crate::leanh::lean_ctor_get(v_snd_6220_, 1);
                    crate::leanh::lean_inc(v_snd_6223_);
                    crate::leanh::lean_dec(v_snd_6220_);
                    v___x_6224_ = l_Subarray_split___redArg(v_fst_6200_, v_fst_6222_);
                    crate::leanh::lean_dec(v_fst_6222_);
                    v_fst_6225_ = crate::leanh::lean_ctor_get(v___x_6224_, 0);
                    crate::leanh::lean_inc(v_fst_6225_);
                    v_snd_6226_ = crate::leanh::lean_ctor_get(v___x_6224_, 1);
                    crate::leanh::lean_inc(v_snd_6226_);
                    crate::leanh::lean_dec_ref(v___x_6224_);
                    v___x_6227_ = l_Subarray_split___redArg(v_fst_6201_, v_snd_6223_);
                    crate::leanh::lean_dec(v_snd_6223_);
                    v_fst_6228_ = crate::leanh::lean_ctor_get(v___x_6227_, 0);
                    crate::leanh::lean_inc(v_fst_6228_);
                    v_snd_6229_ = crate::leanh::lean_ctor_get(v___x_6227_, 1);
                    crate::leanh::lean_inc(v_snd_6229_);
                    crate::leanh::lean_dec_ref(v___x_6227_);
                    v___x_6230_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_6225_, v_fst_6228_);
                    v___x_6231_ = l_Array_append___redArg(v_fst_6195_, v___x_6230_);
                    crate::leanh::lean_dec_ref(v___x_6230_);
                    v___x_6232_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6233_ = lean_mk_empty_array_with_capacity(v___x_6232_);
                    v___x_6234_ = lean_array_push(v___x_6233_, v_fst_6221_);
                    v___x_6235_ = l_Array_append___redArg(v___x_6231_, v___x_6234_);
                    crate::leanh::lean_dec_ref(v___x_6234_);
                    v___x_6236_ = l_Subarray_drop___redArg(v_snd_6226_, v___x_6232_);
                    v___x_6237_ = l_Subarray_drop___redArg(v_snd_6229_, v___x_6232_);
                    v___x_6238_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_6236_, v___x_6237_);
                    v___x_6239_ = l_Array_append___redArg(v___x_6235_, v___x_6238_);
                    crate::leanh::lean_dec_ref(v___x_6238_);
                    v___x_6240_ = l_Array_append___redArg(v___x_6239_, v_snd_6202_);
                    crate::leanh::lean_dec(v_snd_6202_);
                    return v___x_6240_;
                } else {
                    crate::leanh::lean_dec(v___x_6217_);
                    crate::leanh::lean_dec(v_fst_6201_);
                    crate::leanh::lean_dec(v_fst_6200_);
                    v___x_6241_ = l_Array_append___redArg(v_fst_6195_, v_snd_6202_);
                    crate::leanh::lean_dec(v_snd_6202_);
                    return v___x_6241_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(
    mut v_sz_6248_: usize,
    mut v_i_6249_: usize,
    mut v_bs_6250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6251_: u8 = 0;
    let mut v_v_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: u8 = 0;
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: usize = 0;
    let mut v___x_6259_: usize = 0;
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6251_ = lean_usize_dec_lt(v_i_6249_, v_sz_6248_);
                if v___x_6251_ == 0 {
                    return v_bs_6250_;
                } else {
                    v_v_6252_ = lean_array_uget(v_bs_6250_, v_i_6249_);
                    v___x_6253_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6254_ = lean_array_uset(v_bs_6250_, v_i_6249_, v___x_6253_);
                    v___x_6255_ = 1;
                    v___x_6256_ = crate::leanh::lean_box((v___x_6255_) as usize);
                    v___x_6257_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6257_, 0, v___x_6256_);
                    crate::leanh::lean_ctor_set(v___x_6257_, 1, v_v_6252_);
                    v___x_6258_ = 1usize;
                    v___x_6259_ = lean_usize_add(v_i_6249_, v___x_6258_);
                    v___x_6260_ = lean_array_uset(v_bs_x27_6254_, v_i_6249_, v___x_6257_);
                    v_i_6249_ = v___x_6259_;
                    v_bs_6250_ = v___x_6260_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(
    mut v_sz_6262_: *mut crate::leanh::LeanObject,
    mut v_i_6263_: *mut crate::leanh::LeanObject,
    mut v_bs_6264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6265_: usize = 0;
    let mut v_i_boxed_6266_: usize = 0;
    let mut v_res_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6265_ = crate::leanh::lean_unbox_usize(v_sz_6262_);
    crate::leanh::lean_dec(v_sz_6262_);
    v_i_boxed_6266_ = crate::leanh::lean_unbox_usize(v_i_6263_);
    crate::leanh::lean_dec(v_i_6263_);
    v_res_6267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_6265_, v_i_boxed_6266_, v_bs_6264_);
    return v_res_6267_;
}
pub unsafe fn l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(
    mut v_original_6273_: *mut crate::leanh::LeanObject,
    mut v_edited_6274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: u8 = 0;
    let mut v_sz_6278_: usize = 0;
    let mut v___x_6279_: usize = 0;
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    let mut v_sz_6283_: usize = 0;
    let mut v___x_6284_: usize = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ds_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6290_: usize = 0;
    let mut v___x_6291_: usize = 0;
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6299_: u8 = 0;
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6312_: u8 = 0;
    let mut v_unused_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_i_6275_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6276_ = lean_array_get_size(v_original_6273_);
                v___x_6277_ = lean_nat_dec_lt(v_i_6275_, v___x_6276_);
                if v___x_6277_ == 0 {
                    crate::leanh::lean_dec_ref(v_original_6273_);
                    v_sz_6278_ = lean_array_size(v_edited_6274_);
                    v___x_6279_ = 0usize;
                    v___x_6280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_6278_, v___x_6279_, v_edited_6274_);
                    return v___x_6280_;
                } else {
                    v___x_6281_ = lean_array_get_size(v_edited_6274_);
                    v___x_6282_ = lean_nat_dec_lt(v_i_6275_, v___x_6281_);
                    if v___x_6282_ == 0 {
                        crate::leanh::lean_dec_ref(v_edited_6274_);
                        v_sz_6283_ = lean_array_size(v_original_6273_);
                        v___x_6284_ = 0usize;
                        v___x_6285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_6283_, v___x_6284_, v_original_6273_);
                        return v___x_6285_;
                    } else {
                        crate::leanh::lean_inc_ref(v_original_6273_);
                        v___x_6286_ =
                            l_Array_toSubarray___redArg(v_original_6273_, v_i_6275_, v___x_6276_);
                        crate::leanh::lean_inc_ref(v_edited_6274_);
                        v___x_6287_ =
                            l_Array_toSubarray___redArg(v_edited_6274_, v_i_6275_, v___x_6281_);
                        v_ds_6288_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_6286_, v___x_6287_);
                        v___x_6289_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1;
                        v_sz_6290_ = lean_array_size(v_ds_6288_);
                        v___x_6291_ = 0usize;
                        v___x_6292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_6274_, v___x_6281_, v_original_6273_, v___x_6276_, v_ds_6288_, v_sz_6290_, v___x_6291_, v___x_6289_);
                        crate::leanh::lean_dec_ref(v_ds_6288_);
                        v_snd_6293_ = crate::leanh::lean_ctor_get(v___x_6292_, 1);
                        crate::leanh::lean_inc(v_snd_6293_);
                        v_fst_6294_ = crate::leanh::lean_ctor_get(v___x_6292_, 0);
                        crate::leanh::lean_inc(v_fst_6294_);
                        crate::leanh::lean_dec_ref(v___x_6292_);
                        v_fst_6295_ = crate::leanh::lean_ctor_get(v_snd_6293_, 0);
                        v_snd_6296_ = crate::leanh::lean_ctor_get(v_snd_6293_, 1);
                        v_isSharedCheck_6315_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_6293_)) as u8;
                        if v_isSharedCheck_6315_ == 0 {
                            v___x_6298_ = v_snd_6293_;
                            v_isShared_6299_ = v_isSharedCheck_6315_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_6296_);
                            crate::leanh::lean_inc(v_fst_6295_);
                            crate::leanh::lean_dec(v_snd_6293_);
                            v___x_6298_ = crate::leanh::lean_box(0);
                            v_isShared_6299_ = v_isSharedCheck_6315_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6298_, 1, v_fst_6295_);
                    crate::leanh::lean_ctor_set(v___x_6298_, 0, v_fst_6294_);
                    v___x_6301_ = v___x_6298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_fst_6294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6314_, 1, v_fst_6295_);
                    v___x_6301_ = v_reuseFailAlloc_6314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6302_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_6276_, v_original_6273_, v___x_6301_);
                crate::leanh::lean_dec_ref(v_original_6273_);
                v_fst_6303_ = crate::leanh::lean_ctor_get(v___x_6302_, 0);
                v_isSharedCheck_6312_ = (!crate::leanh::lean_is_exclusive(v___x_6302_)) as u8;
                if v_isSharedCheck_6312_ == 0 {
                    v_unused_6313_ = crate::leanh::lean_ctor_get(v___x_6302_, 1);
                    crate::leanh::lean_dec(v_unused_6313_);
                    v___x_6305_ = v___x_6302_;
                    v_isShared_6306_ = v_isSharedCheck_6312_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6303_);
                    crate::leanh::lean_dec(v___x_6302_);
                    v___x_6305_ = crate::leanh::lean_box(0);
                    v_isShared_6306_ = v_isSharedCheck_6312_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6305_, 1, v_snd_6296_);
                    v___x_6308_ = v___x_6305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_fst_6303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6311_, 1, v_snd_6296_);
                    v___x_6308_ = v_reuseFailAlloc_6311_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6309_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_6281_, v_edited_6274_, v___x_6308_);
                crate::leanh::lean_dec_ref(v_edited_6274_);
                v_fst_6310_ = crate::leanh::lean_ctor_get(v___x_6309_, 0);
                crate::leanh::lean_inc(v_fst_6310_);
                crate::leanh::lean_dec_ref(v___x_6309_);
                return v_fst_6310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(
    mut v___x_6316_: *mut crate::leanh::LeanObject,
    mut v_inSubst_6317_: u8,
    mut v___x_6318_: *mut crate::leanh::LeanObject,
    mut v_____r_6319_: *mut crate::leanh::LeanObject,
    mut v_wssIdx_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6321_ = crate::leanh::lean_box((v_inSubst_6317_) as usize);
    v___x_6322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6322_, 0, v___x_6316_);
    crate::leanh::lean_ctor_set(v___x_6322_, 1, v___x_6321_);
    v___x_6323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6323_, 0, v_wssIdx_6320_);
    crate::leanh::lean_ctor_set(v___x_6323_, 1, v___x_6322_);
    v___x_6324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6324_, 0, v___x_6318_);
    crate::leanh::lean_ctor_set(v___x_6324_, 1, v___x_6323_);
    v___x_6325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6325_, 0, v___x_6324_);
    return v___x_6325_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(
    mut v___x_6326_: *mut crate::leanh::LeanObject,
    mut v_inSubst_6327_: *mut crate::leanh::LeanObject,
    mut v___x_6328_: *mut crate::leanh::LeanObject,
    mut v_____r_6329_: *mut crate::leanh::LeanObject,
    mut v_wssIdx_6330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inSubst_boxed_6331_: u8 = 0;
    let mut v_res_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inSubst_boxed_6331_ = (crate::leanh::lean_unbox(v_inSubst_6327_) as u8);
    v_res_6332_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_6326_, v_inSubst_boxed_6331_, v___x_6328_, v_____r_6329_, v_wssIdx_6330_);
    return v_res_6332_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(
    mut v_fst_6333_: *mut crate::leanh::LeanObject,
    mut v___x_6334_: u8,
    mut v_fst_6335_: *mut crate::leanh::LeanObject,
    mut v___x_6336_: *mut crate::leanh::LeanObject,
    mut v_00___6337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6338_ = crate::leanh::lean_box((v___x_6334_) as usize);
    v___x_6339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6339_, 0, v_fst_6333_);
    crate::leanh::lean_ctor_set(v___x_6339_, 1, v___x_6338_);
    v___x_6340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6340_, 0, v_fst_6335_);
    crate::leanh::lean_ctor_set(v___x_6340_, 1, v___x_6339_);
    v___x_6341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6341_, 0, v___x_6336_);
    crate::leanh::lean_ctor_set(v___x_6341_, 1, v___x_6340_);
    v___x_6342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6342_, 0, v___x_6341_);
    return v___x_6342_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(
    mut v_fst_6343_: *mut crate::leanh::LeanObject,
    mut v___x_6344_: *mut crate::leanh::LeanObject,
    mut v_fst_6345_: *mut crate::leanh::LeanObject,
    mut v___x_6346_: *mut crate::leanh::LeanObject,
    mut v_00___6347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9180__boxed_6348_: u8 = 0;
    let mut v_res_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9180__boxed_6348_ = (crate::leanh::lean_unbox(v___x_6344_) as u8);
    v_res_6349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_6343_, v___x_9180__boxed_6348_, v_fst_6345_, v___x_6346_, v_00___6347_);
    return v_res_6349_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(
    mut v_inSubst_6350_: u8,
    mut v_snd_6351_: *mut crate::leanh::LeanObject,
    mut v_fst_6352_: *mut crate::leanh::LeanObject,
    mut v_____r_6353_: *mut crate::leanh::LeanObject,
    mut v_withWs_6354_: *mut crate::leanh::LeanObject,
    mut v_wssIdx_6355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_wss_x27Idx_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: u8 = 0;
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6363_ = (crate::leanh::lean_unbox(v_snd_6351_) as u8);
                if v___x_6363_ == 0 {
                    v_wss_x27Idx_6357_ = v_fst_6352_;
                    state = 1;
                    continue;
                } else {
                    v___x_6364_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6365_ = lean_nat_add(v_fst_6352_, v___x_6364_);
                    crate::leanh::lean_dec(v_fst_6352_);
                    v_wss_x27Idx_6357_ = v___x_6365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6358_ = crate::leanh::lean_box((v_inSubst_6350_) as usize);
                v___x_6359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6359_, 0, v_wss_x27Idx_6357_);
                crate::leanh::lean_ctor_set(v___x_6359_, 1, v___x_6358_);
                v___x_6360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6360_, 0, v_wssIdx_6355_);
                crate::leanh::lean_ctor_set(v___x_6360_, 1, v___x_6359_);
                v___x_6361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6361_, 0, v_withWs_6354_);
                crate::leanh::lean_ctor_set(v___x_6361_, 1, v___x_6360_);
                v___x_6362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6362_, 0, v___x_6361_);
                return v___x_6362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(
    mut v_inSubst_6366_: *mut crate::leanh::LeanObject,
    mut v_snd_6367_: *mut crate::leanh::LeanObject,
    mut v_fst_6368_: *mut crate::leanh::LeanObject,
    mut v_____r_6369_: *mut crate::leanh::LeanObject,
    mut v_withWs_6370_: *mut crate::leanh::LeanObject,
    mut v_wssIdx_6371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inSubst_boxed_6372_: u8 = 0;
    let mut v_res_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inSubst_boxed_6372_ = (crate::leanh::lean_unbox(v_inSubst_6366_) as u8);
    v_res_6373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_6372_, v_snd_6367_, v_fst_6368_, v_____r_6369_, v_withWs_6370_, v_wssIdx_6371_);
    crate::leanh::lean_dec(v_snd_6367_);
    return v_res_6373_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(
    mut v_upperBound_6374_: *mut crate::leanh::LeanObject,
    mut v_diff_6375_: *mut crate::leanh::LeanObject,
    mut v_snd_6376_: *mut crate::leanh::LeanObject,
    mut v_snd_6377_: *mut crate::leanh::LeanObject,
    mut v_a_6378_: *mut crate::leanh::LeanObject,
    mut v_b_6379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: u8 = 0;
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6397_: u8 = 0;
    let mut v_fst_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6401_: u8 = 0;
    let mut v_fst_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6406_: u8 = 0;
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: u8 = 0;
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v_inSubst_6444_: u8 = 0;
    let mut v___y_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: u8 = 0;
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: u8 = 0;
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: u8 = 0;
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: u8 = 0;
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: u8 = 0;
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: u8 = 0;
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6529_: u8 = 0;
    let mut v_unused_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6531_: u8 = 0;
    let mut v_isSharedCheck_6532_: u8 = 0;
    let mut v_unused_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6534_: u8 = 0;
    let mut v_unused_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6389_ = lean_nat_dec_lt(v_a_6378_, v_upperBound_6374_);
                if v___x_6389_ == 0 {
                    crate::leanh::lean_dec(v_a_6378_);
                    return v_b_6379_;
                } else {
                    v___x_6390_ = lean_array_fget_borrowed(v_diff_6375_, v_a_6378_);
                    v_snd_6391_ = crate::leanh::lean_ctor_get(v_b_6379_, 1);
                    crate::leanh::lean_inc(v_snd_6391_);
                    v_snd_6392_ = crate::leanh::lean_ctor_get(v_snd_6391_, 1);
                    crate::leanh::lean_inc(v_snd_6392_);
                    v_fst_6393_ = crate::leanh::lean_ctor_get(v___x_6390_, 0);
                    v_fst_6394_ = crate::leanh::lean_ctor_get(v_b_6379_, 0);
                    v_isSharedCheck_6534_ = (!crate::leanh::lean_is_exclusive(v_b_6379_)) as u8;
                    if v_isSharedCheck_6534_ == 0 {
                        v_unused_6535_ = crate::leanh::lean_ctor_get(v_b_6379_, 1);
                        crate::leanh::lean_dec(v_unused_6535_);
                        v___x_6396_ = v_b_6379_;
                        v_isShared_6397_ = v_isSharedCheck_6534_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_6394_);
                        crate::leanh::lean_dec(v_b_6379_);
                        v___x_6396_ = crate::leanh::lean_box(0);
                        v_isShared_6397_ = v_isSharedCheck_6534_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6382_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6383_ = lean_nat_add(v_a_6378_, v___x_6382_);
                crate::leanh::lean_dec(v_a_6378_);
                v_a_6378_ = v___x_6383_;
                v_b_6379_ = v_a_6381_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_6386_) == 0 {
                    crate::leanh::lean_dec(v_a_6378_);
                    v_a_6387_ = crate::leanh::lean_ctor_get(v___y_6386_, 0);
                    crate::leanh::lean_inc(v_a_6387_);
                    crate::leanh::lean_dec_ref_known(v___y_6386_, 1);
                    return v_a_6387_;
                } else {
                    v_a_6388_ = crate::leanh::lean_ctor_get(v___y_6386_, 0);
                    crate::leanh::lean_inc(v_a_6388_);
                    crate::leanh::lean_dec_ref_known(v___y_6386_, 1);
                    v_a_6381_ = v_a_6388_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_fst_6398_ = crate::leanh::lean_ctor_get(v_snd_6391_, 0);
                v_isSharedCheck_6532_ = (!crate::leanh::lean_is_exclusive(v_snd_6391_)) as u8;
                if v_isSharedCheck_6532_ == 0 {
                    v_unused_6533_ = crate::leanh::lean_ctor_get(v_snd_6391_, 1);
                    crate::leanh::lean_dec(v_unused_6533_);
                    v___x_6400_ = v_snd_6391_;
                    v_isShared_6401_ = v_isSharedCheck_6532_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6398_);
                    crate::leanh::lean_dec(v_snd_6391_);
                    v___x_6400_ = crate::leanh::lean_box(0);
                    v_isShared_6401_ = v_isSharedCheck_6532_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fst_6402_ = crate::leanh::lean_ctor_get(v_snd_6392_, 0);
                v_snd_6403_ = crate::leanh::lean_ctor_get(v_snd_6392_, 1);
                v_isSharedCheck_6531_ = (!crate::leanh::lean_is_exclusive(v_snd_6392_)) as u8;
                if v_isSharedCheck_6531_ == 0 {
                    v___x_6405_ = v_snd_6392_;
                    v_isShared_6406_ = v_isSharedCheck_6531_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6403_);
                    crate::leanh::lean_inc(v_fst_6402_);
                    crate::leanh::lean_dec(v_snd_6392_);
                    v___x_6405_ = crate::leanh::lean_box(0);
                    v_isShared_6406_ = v_isSharedCheck_6531_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v___x_6390_);
                v___x_6407_ = lean_array_push(v_fst_6394_, v___x_6390_);
                v___x_6432_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6433_ = lean_nat_add(v_a_6378_, v___x_6432_);
                v___x_6434_ = lean_array_get_size(v_diff_6375_);
                v___x_6435_ = lean_nat_dec_lt(v___x_6433_, v___x_6434_);
                if v___x_6435_ == 0 {
                    crate::leanh::lean_dec(v___x_6433_);
                    crate::leanh::lean_del_object(v___x_6405_);
                    crate::leanh::lean_del_object(v___x_6400_);
                    crate::leanh::lean_del_object(v___x_6396_);
                    v___x_6436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6436_, 0, v_fst_6402_);
                    crate::leanh::lean_ctor_set(v___x_6436_, 1, v_snd_6403_);
                    v___x_6437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6437_, 0, v_fst_6398_);
                    crate::leanh::lean_ctor_set(v___x_6437_, 1, v___x_6436_);
                    v___x_6438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6438_, 0, v___x_6407_);
                    crate::leanh::lean_ctor_set(v___x_6438_, 1, v___x_6437_);
                    v_a_6381_ = v___x_6438_;
                    state = 1;
                    continue;
                } else {
                    v___x_6439_ = lean_array_fget(v_diff_6375_, v___x_6433_);
                    crate::leanh::lean_dec(v___x_6433_);
                    v_fst_6440_ = crate::leanh::lean_ctor_get(v___x_6439_, 0);
                    v_isSharedCheck_6529_ = (!crate::leanh::lean_is_exclusive(v___x_6439_)) as u8;
                    if v_isSharedCheck_6529_ == 0 {
                        v_unused_6530_ = crate::leanh::lean_ctor_get(v___x_6439_, 1);
                        crate::leanh::lean_dec(v_unused_6530_);
                        v___x_6442_ = v___x_6439_;
                        v_isShared_6443_ = v_isSharedCheck_6529_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_6440_);
                        crate::leanh::lean_dec(v___x_6439_);
                        v___x_6442_ = crate::leanh::lean_box(0);
                        v_isShared_6443_ = v_isSharedCheck_6529_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6410_ = l_Array_append___redArg(v___x_6407_, v___y_6409_);
                crate::leanh::lean_dec_ref(v___y_6409_);
                v___x_6411_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6412_ = lean_nat_add(v_fst_6398_, v___x_6411_);
                crate::leanh::lean_dec(v_fst_6398_);
                v___x_6413_ = lean_nat_add(v_fst_6402_, v___x_6411_);
                crate::leanh::lean_dec(v_fst_6402_);
                if v_isShared_6406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6405_, 0, v___x_6413_);
                    v___x_6415_ = v___x_6405_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6422_, 0, v___x_6413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6422_, 1, v_snd_6403_);
                    v___x_6415_ = v_reuseFailAlloc_6422_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6400_, 1, v___x_6415_);
                    crate::leanh::lean_ctor_set(v___x_6400_, 0, v___x_6412_);
                    v___x_6417_ = v___x_6400_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6421_, 0, v___x_6412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6421_, 1, v___x_6415_);
                    v___x_6417_ = v_reuseFailAlloc_6421_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6397_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6396_, 1, v___x_6417_);
                    crate::leanh::lean_ctor_set(v___x_6396_, 0, v___x_6410_);
                    v___x_6419_ = v___x_6396_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 0, v___x_6410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 1, v___x_6417_);
                    v___x_6419_ = v_reuseFailAlloc_6420_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_6381_ = v___x_6419_;
                state = 1;
                continue;
            }
            10 => {
                v___x_6425_ = l_Array_append___redArg(v___x_6407_, v___y_6424_);
                crate::leanh::lean_dec_ref(v___y_6424_);
                v___x_6426_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6427_ = lean_nat_add(v_fst_6398_, v___x_6426_);
                crate::leanh::lean_dec(v_fst_6398_);
                v___x_6428_ = lean_nat_add(v_fst_6402_, v___x_6426_);
                crate::leanh::lean_dec(v_fst_6402_);
                v___x_6429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6429_, 0, v___x_6428_);
                crate::leanh::lean_ctor_set(v___x_6429_, 1, v_snd_6403_);
                v___x_6430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6430_, 0, v___x_6427_);
                crate::leanh::lean_ctor_set(v___x_6430_, 1, v___x_6429_);
                v___x_6431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6431_, 0, v___x_6425_);
                crate::leanh::lean_ctor_set(v___x_6431_, 1, v___x_6430_);
                v_a_6381_ = v___x_6431_;
                state = 1;
                continue;
            }
            11 => {
                v_inSubst_6444_ = 0;
                v___x_6455_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
                v___x_6456_ = (crate::leanh::lean_unbox(v_fst_6393_) as u8);
                match v___x_6456_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_6405_);
                        crate::leanh::lean_del_object(v___x_6400_);
                        crate::leanh::lean_del_object(v___x_6396_);
                        v___x_6457_ = (crate::leanh::lean_unbox(v_fst_6440_) as u8);
                        match v___x_6457_ {
                            0 => {
                                v___x_6458_ =
                                    lean_array_get_borrowed(v___x_6455_, v_snd_6376_, v_fst_6402_);
                                crate::leanh::lean_inc(v___x_6458_);
                                if v_isShared_6443_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6458_);
                                    v___x_6460_ = v___x_6442_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6466_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6466_,
                                        0,
                                        v_fst_6440_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6466_,
                                        1,
                                        v___x_6458_,
                                    );
                                    v___x_6460_ = v_reuseFailAlloc_6466_;
                                    state = 13;
                                    continue;
                                }
                            }
                            1 => {
                                crate::leanh::lean_del_object(v___x_6442_);
                                crate::leanh::lean_dec(v_fst_6440_);
                                crate::leanh::lean_dec(v_snd_6403_);
                                v___x_6467_ = crate::leanh::lean_box(0);
                                v___x_6468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_6402_, v___x_6389_, v_fst_6398_, v___x_6407_, v___x_6467_);
                                v___y_6386_ = v___x_6468_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec(v_fst_6440_);
                                v___x_6469_ =
                                    lean_array_get_borrowed(v___x_6455_, v_snd_6376_, v_fst_6402_);
                                v___x_6470_ = (crate::leanh::lean_unbox(v_snd_6403_) as u8);
                                if v___x_6470_ == 0 {
                                    crate::leanh::lean_inc(v___x_6469_);
                                    crate::leanh::lean_inc(v_fst_6393_);
                                    if v_isShared_6443_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6469_);
                                        crate::leanh::lean_ctor_set(v___x_6442_, 0, v_fst_6393_);
                                        v___x_6472_ = v___x_6442_;
                                        state = 14;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6475_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6475_,
                                            0,
                                            v_fst_6393_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6475_,
                                            1,
                                            v___x_6469_,
                                        );
                                        v___x_6472_ = v_reuseFailAlloc_6475_;
                                        state = 14;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_6442_);
                                    v___x_6476_ = lean_array_get_borrowed(
                                        v___x_6455_,
                                        v_snd_6377_,
                                        v_fst_6398_,
                                    );
                                    crate::leanh::lean_inc(v___x_6469_);
                                    crate::leanh::lean_inc(v___x_6476_);
                                    v___x_6477_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_6476_, v___x_6469_);
                                    v___y_6446_ = v___x_6477_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_6405_);
                        crate::leanh::lean_del_object(v___x_6400_);
                        crate::leanh::lean_del_object(v___x_6396_);
                        v___x_6478_ = (crate::leanh::lean_unbox(v_fst_6440_) as u8);
                        match v___x_6478_ {
                            0 => {
                                crate::leanh::lean_del_object(v___x_6442_);
                                crate::leanh::lean_dec(v_fst_6440_);
                                crate::leanh::lean_dec(v_snd_6403_);
                                v___x_6479_ = crate::leanh::lean_box(0);
                                v___x_6480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_6402_, v___x_6389_, v_fst_6398_, v___x_6407_, v___x_6479_);
                                v___y_6386_ = v___x_6480_;
                                state = 2;
                                continue;
                            }
                            1 => {
                                v___x_6481_ =
                                    lean_array_get_borrowed(v___x_6455_, v_snd_6377_, v_fst_6398_);
                                crate::leanh::lean_inc(v___x_6481_);
                                if v_isShared_6443_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6481_);
                                    v___x_6483_ = v___x_6442_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6489_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6489_,
                                        0,
                                        v_fst_6440_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6489_,
                                        1,
                                        v___x_6481_,
                                    );
                                    v___x_6483_ = v_reuseFailAlloc_6489_;
                                    state = 15;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec(v_fst_6440_);
                                v___x_6493_ = (crate::leanh::lean_unbox(v_snd_6403_) as u8);
                                if v___x_6493_ == 0 {
                                    v___x_6494_ = lean_array_get_borrowed(
                                        v___x_6455_,
                                        v_snd_6377_,
                                        v_fst_6398_,
                                    );
                                    v___x_6495_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_6496_ = lean_string_utf8_byte_size(v___x_6494_);
                                    crate::leanh::lean_inc(v___x_6494_);
                                    v___x_6497_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6497_, 0, v___x_6494_);
                                    crate::leanh::lean_ctor_set(v___x_6497_, 1, v___x_6495_);
                                    crate::leanh::lean_ctor_set(v___x_6497_, 2, v___x_6496_);
                                    v___x_6498_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_6497_);
                                    crate::leanh::lean_dec_ref_known(v___x_6497_, 3);
                                    if v___x_6498_ == 0 {
                                        crate::leanh::lean_inc(v___x_6494_);
                                        crate::leanh::lean_inc(v_fst_6393_);
                                        if v_isShared_6443_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_6442_,
                                                1,
                                                v___x_6494_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_6442_,
                                                0,
                                                v_fst_6393_,
                                            );
                                            v___x_6500_ = v___x_6442_;
                                            state = 17;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6505_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6505_,
                                                0,
                                                v_fst_6393_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6505_,
                                                1,
                                                v___x_6494_,
                                            );
                                            v___x_6500_ = v_reuseFailAlloc_6505_;
                                            state = 17;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_del_object(v___x_6442_);
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_6442_);
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                    _ => {
                        v___x_6506_ = (crate::leanh::lean_unbox(v_fst_6440_) as u8);
                        if v___x_6506_ == 1 {
                            v___x_6507_ =
                                lean_array_get_borrowed(v___x_6455_, v_snd_6377_, v_fst_6398_);
                            v___x_6508_ = lean_array_get_size(v_snd_6376_);
                            v___x_6509_ = lean_nat_dec_lt(v_fst_6402_, v___x_6508_);
                            if v___x_6509_ == 0 {
                                crate::leanh::lean_inc(v___x_6507_);
                                if v_isShared_6443_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6507_);
                                    v___x_6511_ = v___x_6442_;
                                    state = 18;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6514_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6514_,
                                        0,
                                        v_fst_6440_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6514_,
                                        1,
                                        v___x_6507_,
                                    );
                                    v___x_6511_ = v_reuseFailAlloc_6514_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6442_);
                                crate::leanh::lean_dec(v_fst_6440_);
                                v___x_6515_ = lean_array_fget_borrowed(v_snd_6376_, v_fst_6402_);
                                crate::leanh::lean_inc(v___x_6515_);
                                crate::leanh::lean_inc(v___x_6507_);
                                v___x_6516_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_6507_, v___x_6515_);
                                v___y_6409_ = v___x_6516_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_6440_);
                            crate::leanh::lean_del_object(v___x_6405_);
                            crate::leanh::lean_del_object(v___x_6400_);
                            crate::leanh::lean_del_object(v___x_6396_);
                            v___x_6517_ =
                                lean_array_get_borrowed(v___x_6455_, v_snd_6376_, v_fst_6402_);
                            v___x_6518_ = lean_array_get_size(v_snd_6377_);
                            v___x_6519_ = lean_nat_dec_lt(v_fst_6398_, v___x_6518_);
                            if v___x_6519_ == 0 {
                                v___x_6520_ = 0;
                                v___x_6521_ = crate::leanh::lean_box((v___x_6520_) as usize);
                                crate::leanh::lean_inc(v___x_6517_);
                                if v_isShared_6443_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6517_);
                                    crate::leanh::lean_ctor_set(v___x_6442_, 0, v___x_6521_);
                                    v___x_6523_ = v___x_6442_;
                                    state = 19;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6526_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6526_,
                                        0,
                                        v___x_6521_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6526_,
                                        1,
                                        v___x_6517_,
                                    );
                                    v___x_6523_ = v_reuseFailAlloc_6526_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6442_);
                                v___x_6527_ = lean_array_fget_borrowed(v_snd_6377_, v_fst_6398_);
                                crate::leanh::lean_inc(v___x_6517_);
                                crate::leanh::lean_inc(v___x_6527_);
                                v___x_6528_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_6527_, v___x_6517_);
                                v___y_6424_ = v___x_6528_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            12 => {
                v___x_6447_ = l_Array_append___redArg(v___x_6407_, v___y_6446_);
                crate::leanh::lean_dec_ref(v___y_6446_);
                v___x_6448_ = lean_nat_add(v_fst_6402_, v___x_6432_);
                crate::leanh::lean_dec(v_fst_6402_);
                v___x_6449_ = (crate::leanh::lean_unbox(v_snd_6403_) as u8);
                crate::leanh::lean_dec(v_snd_6403_);
                if v___x_6449_ == 0 {
                    v___x_6450_ = crate::leanh::lean_box(0);
                    v___x_6451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_6448_, v_inSubst_6444_, v___x_6447_, v___x_6450_, v_fst_6398_);
                    v___y_6386_ = v___x_6451_;
                    state = 2;
                    continue;
                } else {
                    v___x_6452_ = lean_nat_add(v_fst_6398_, v___x_6432_);
                    crate::leanh::lean_dec(v_fst_6398_);
                    v___x_6453_ = crate::leanh::lean_box(0);
                    v___x_6454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_6448_, v_inSubst_6444_, v___x_6447_, v___x_6453_, v___x_6452_);
                    v___y_6386_ = v___x_6454_;
                    state = 2;
                    continue;
                }
            }
            13 => {
                v___x_6461_ = lean_array_push(v___x_6407_, v___x_6460_);
                v___x_6462_ = lean_nat_add(v_fst_6402_, v___x_6432_);
                crate::leanh::lean_dec(v_fst_6402_);
                v___x_6463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6463_, 0, v___x_6462_);
                crate::leanh::lean_ctor_set(v___x_6463_, 1, v_snd_6403_);
                v___x_6464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6464_, 0, v_fst_6398_);
                crate::leanh::lean_ctor_set(v___x_6464_, 1, v___x_6463_);
                v___x_6465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6465_, 0, v___x_6461_);
                crate::leanh::lean_ctor_set(v___x_6465_, 1, v___x_6464_);
                v_a_6381_ = v___x_6465_;
                state = 1;
                continue;
            }
            14 => {
                v___x_6473_ = lean_mk_empty_array_with_capacity(v___x_6432_);
                v___x_6474_ = lean_array_push(v___x_6473_, v___x_6472_);
                v___y_6446_ = v___x_6474_;
                state = 12;
                continue;
            }
            15 => {
                v___x_6484_ = lean_array_push(v___x_6407_, v___x_6483_);
                v___x_6485_ = lean_nat_add(v_fst_6398_, v___x_6432_);
                crate::leanh::lean_dec(v_fst_6398_);
                v___x_6486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6486_, 0, v_fst_6402_);
                crate::leanh::lean_ctor_set(v___x_6486_, 1, v_snd_6403_);
                v___x_6487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6487_, 0, v___x_6485_);
                crate::leanh::lean_ctor_set(v___x_6487_, 1, v___x_6486_);
                v___x_6488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6488_, 0, v___x_6484_);
                crate::leanh::lean_ctor_set(v___x_6488_, 1, v___x_6487_);
                v_a_6381_ = v___x_6488_;
                state = 1;
                continue;
            }
            16 => {
                v___x_6491_ = crate::leanh::lean_box(0);
                v___x_6492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_6444_, v_snd_6403_, v_fst_6402_, v___x_6491_, v___x_6407_, v_fst_6398_);
                crate::leanh::lean_dec(v_snd_6403_);
                v___y_6386_ = v___x_6492_;
                state = 2;
                continue;
            }
            17 => {
                v___x_6501_ = lean_array_push(v___x_6407_, v___x_6500_);
                v___x_6502_ = lean_nat_add(v_fst_6398_, v___x_6432_);
                crate::leanh::lean_dec(v_fst_6398_);
                v___x_6503_ = crate::leanh::lean_box(0);
                v___x_6504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_6444_, v_snd_6403_, v_fst_6402_, v___x_6503_, v___x_6501_, v___x_6502_);
                crate::leanh::lean_dec(v_snd_6403_);
                v___y_6386_ = v___x_6504_;
                state = 2;
                continue;
            }
            18 => {
                v___x_6512_ = lean_mk_empty_array_with_capacity(v___x_6432_);
                v___x_6513_ = lean_array_push(v___x_6512_, v___x_6511_);
                v___y_6409_ = v___x_6513_;
                state = 6;
                continue;
            }
            19 => {
                v___x_6524_ = lean_mk_empty_array_with_capacity(v___x_6432_);
                v___x_6525_ = lean_array_push(v___x_6524_, v___x_6523_);
                v___y_6424_ = v___x_6525_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(
    mut v_upperBound_6536_: *mut crate::leanh::LeanObject,
    mut v_diff_6537_: *mut crate::leanh::LeanObject,
    mut v_snd_6538_: *mut crate::leanh::LeanObject,
    mut v_snd_6539_: *mut crate::leanh::LeanObject,
    mut v_a_6540_: *mut crate::leanh::LeanObject,
    mut v_b_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_6536_, v_diff_6537_, v_snd_6538_, v_snd_6539_, v_a_6540_, v_b_6541_);
    crate::leanh::lean_dec_ref(v_snd_6539_);
    crate::leanh::lean_dec_ref(v_snd_6538_);
    crate::leanh::lean_dec_ref(v_diff_6537_);
    crate::leanh::lean_dec(v_upperBound_6536_);
    return v_res_6542_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(
    mut v_s_6553_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diff_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6568_: usize = 0;
    let mut v___x_6569_: usize = 0;
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6555_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_6553_);
    v_fst_6556_ = crate::leanh::lean_ctor_get(v___x_6555_, 0);
    crate::leanh::lean_inc(v_fst_6556_);
    v_snd_6557_ = crate::leanh::lean_ctor_get(v___x_6555_, 1);
    crate::leanh::lean_inc(v_snd_6557_);
    crate::leanh::lean_dec_ref(v___x_6555_);
    v___x_6558_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_6554_);
    v_fst_6559_ = crate::leanh::lean_ctor_get(v___x_6558_, 0);
    crate::leanh::lean_inc(v_fst_6559_);
    v_snd_6560_ = crate::leanh::lean_ctor_get(v___x_6558_, 1);
    crate::leanh::lean_inc(v_snd_6560_);
    crate::leanh::lean_dec_ref(v___x_6558_);
    v_diff_6561_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_6556_, v_fst_6559_);
    v___x_6562_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6563_ = lean_array_get_size(v_diff_6561_);
    v___x_6564_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2;
    v___x_6565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_6563_, v_diff_6561_, v_snd_6560_, v_snd_6557_, v___x_6562_, v___x_6564_);
    crate::leanh::lean_dec(v_snd_6557_);
    crate::leanh::lean_dec(v_snd_6560_);
    crate::leanh::lean_dec_ref(v_diff_6561_);
    v_fst_6566_ = crate::leanh::lean_ctor_get(v___x_6565_, 0);
    crate::leanh::lean_inc(v_fst_6566_);
    crate::leanh::lean_dec_ref(v___x_6565_);
    v___x_6567_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_6566_);
    crate::leanh::lean_dec(v_fst_6566_);
    v_sz_6568_ = lean_array_size(v___x_6567_);
    v___x_6569_ = 0usize;
    v___x_6570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_6568_, v___x_6569_, v___x_6567_);
    return v___x_6570_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(
    mut v_s_6571_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6573_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(
        v_s_6571_,
        v_s_x27_6572_,
    );
    crate::leanh::lean_dec_ref(v_s_x27_6572_);
    crate::leanh::lean_dec_ref(v_s_6571_);
    return v_res_6573_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(
    mut v_upperBound_6574_: *mut crate::leanh::LeanObject,
    mut v_diff_6575_: *mut crate::leanh::LeanObject,
    mut v_snd_6576_: *mut crate::leanh::LeanObject,
    mut v_snd_6577_: *mut crate::leanh::LeanObject,
    mut v_inst_6578_: *mut crate::leanh::LeanObject,
    mut v_R_6579_: *mut crate::leanh::LeanObject,
    mut v_a_6580_: *mut crate::leanh::LeanObject,
    mut v_b_6581_: *mut crate::leanh::LeanObject,
    mut v_c_6582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_6574_, v_diff_6575_, v_snd_6576_, v_snd_6577_, v_a_6580_, v_b_6581_);
    return v___x_6583_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(
    mut v_upperBound_6584_: *mut crate::leanh::LeanObject,
    mut v_diff_6585_: *mut crate::leanh::LeanObject,
    mut v_snd_6586_: *mut crate::leanh::LeanObject,
    mut v_snd_6587_: *mut crate::leanh::LeanObject,
    mut v_inst_6588_: *mut crate::leanh::LeanObject,
    mut v_R_6589_: *mut crate::leanh::LeanObject,
    mut v_a_6590_: *mut crate::leanh::LeanObject,
    mut v_b_6591_: *mut crate::leanh::LeanObject,
    mut v_c_6592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_6584_, v_diff_6585_, v_snd_6586_, v_snd_6587_, v_inst_6588_, v_R_6589_, v_a_6590_, v_b_6591_, v_c_6592_);
    crate::leanh::lean_dec_ref(v_snd_6587_);
    crate::leanh::lean_dec_ref(v_snd_6586_);
    crate::leanh::lean_dec_ref(v_diff_6585_);
    crate::leanh::lean_dec(v_upperBound_6584_);
    return v_res_6593_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(
    mut v_original_6594_: *mut crate::leanh::LeanObject,
    mut v___x_6595_: *mut crate::leanh::LeanObject,
    mut v_a_6596_: *mut crate::leanh::LeanObject,
    mut v_inst_6597_: *mut crate::leanh::LeanObject,
    mut v_a_6598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6599_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_6594_, v___x_6595_, v_a_6596_, v_a_6598_);
    return v___x_6599_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(
    mut v_original_6600_: *mut crate::leanh::LeanObject,
    mut v___x_6601_: *mut crate::leanh::LeanObject,
    mut v_a_6602_: *mut crate::leanh::LeanObject,
    mut v_inst_6603_: *mut crate::leanh::LeanObject,
    mut v_a_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6605_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_6600_, v___x_6601_, v_a_6602_, v_inst_6603_, v_a_6604_);
    crate::leanh::lean_dec_ref(v_a_6602_);
    crate::leanh::lean_dec(v___x_6601_);
    crate::leanh::lean_dec_ref(v_original_6600_);
    return v_res_6605_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(
    mut v_edited_6606_: *mut crate::leanh::LeanObject,
    mut v___x_6607_: *mut crate::leanh::LeanObject,
    mut v_a_6608_: *mut crate::leanh::LeanObject,
    mut v_inst_6609_: *mut crate::leanh::LeanObject,
    mut v_a_6610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6611_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_6606_, v___x_6607_, v_a_6608_, v_a_6610_);
    return v___x_6611_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(
    mut v_edited_6612_: *mut crate::leanh::LeanObject,
    mut v___x_6613_: *mut crate::leanh::LeanObject,
    mut v_a_6614_: *mut crate::leanh::LeanObject,
    mut v_inst_6615_: *mut crate::leanh::LeanObject,
    mut v_a_6616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6617_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_6612_, v___x_6613_, v_a_6614_, v_inst_6615_, v_a_6616_);
    crate::leanh::lean_dec_ref(v_a_6614_);
    crate::leanh::lean_dec(v___x_6613_);
    crate::leanh::lean_dec_ref(v_edited_6612_);
    return v_res_6617_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(
    mut v___x_6618_: *mut crate::leanh::LeanObject,
    mut v_original_6619_: *mut crate::leanh::LeanObject,
    mut v_inst_6620_: *mut crate::leanh::LeanObject,
    mut v_a_6621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6622_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_6618_, v_original_6619_, v_a_6621_);
    return v___x_6622_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(
    mut v___x_6623_: *mut crate::leanh::LeanObject,
    mut v_original_6624_: *mut crate::leanh::LeanObject,
    mut v_inst_6625_: *mut crate::leanh::LeanObject,
    mut v_a_6626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6627_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_6623_, v_original_6624_, v_inst_6625_, v_a_6626_);
    crate::leanh::lean_dec_ref(v_original_6624_);
    crate::leanh::lean_dec(v___x_6623_);
    return v_res_6627_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(
    mut v___x_6628_: *mut crate::leanh::LeanObject,
    mut v_edited_6629_: *mut crate::leanh::LeanObject,
    mut v_inst_6630_: *mut crate::leanh::LeanObject,
    mut v_a_6631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6632_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_6628_, v_edited_6629_, v_a_6631_);
    return v___x_6632_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(
    mut v___x_6633_: *mut crate::leanh::LeanObject,
    mut v_edited_6634_: *mut crate::leanh::LeanObject,
    mut v_inst_6635_: *mut crate::leanh::LeanObject,
    mut v_a_6636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6637_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_6633_, v_edited_6634_, v_inst_6635_, v_a_6636_);
    crate::leanh::lean_dec_ref(v_edited_6634_);
    crate::leanh::lean_dec(v___x_6633_);
    return v_res_6637_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(
    mut v_as_6638_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6639_: *mut crate::leanh::LeanObject,
    mut v_b_6640_: *mut crate::leanh::LeanObject,
    mut v_a_6641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6642_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_6639_, v_b_6640_);
    return v___x_6642_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(
    mut v_as_6643_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6644_: *mut crate::leanh::LeanObject,
    mut v_b_6645_: *mut crate::leanh::LeanObject,
    mut v_a_6646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6647_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_6643_, v_as_x27_6644_, v_b_6645_, v_a_6646_);
    crate::leanh::lean_dec(v_as_x27_6644_);
    crate::leanh::lean_dec(v_as_6643_);
    return v_res_6647_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(
    mut v_lsize_6648_: *mut crate::leanh::LeanObject,
    mut v_rsize_6649_: *mut crate::leanh::LeanObject,
    mut v_histogram_6650_: *mut crate::leanh::LeanObject,
    mut v_index_6651_: *mut crate::leanh::LeanObject,
    mut v_val_6652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6653_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_6650_, v_index_6651_, v_val_6652_);
    return v___x_6653_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(
    mut v_lsize_6654_: *mut crate::leanh::LeanObject,
    mut v_rsize_6655_: *mut crate::leanh::LeanObject,
    mut v_histogram_6656_: *mut crate::leanh::LeanObject,
    mut v_index_6657_: *mut crate::leanh::LeanObject,
    mut v_val_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6659_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_6654_, v_rsize_6655_, v_histogram_6656_, v_index_6657_, v_val_6658_);
    crate::leanh::lean_dec(v_rsize_6655_);
    crate::leanh::lean_dec(v_lsize_6654_);
    return v_res_6659_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(
    mut v_upperBound_6660_: *mut crate::leanh::LeanObject,
    mut v___x_6661_: *mut crate::leanh::LeanObject,
    mut v_fst_6662_: *mut crate::leanh::LeanObject,
    mut v___x_6663_: *mut crate::leanh::LeanObject,
    mut v_inst_6664_: *mut crate::leanh::LeanObject,
    mut v_R_6665_: *mut crate::leanh::LeanObject,
    mut v_a_6666_: *mut crate::leanh::LeanObject,
    mut v_b_6667_: *mut crate::leanh::LeanObject,
    mut v_c_6668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_6660_, v___x_6661_, v_fst_6662_, v___x_6663_, v_a_6666_, v_b_6667_);
    return v___x_6669_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(
    mut v_upperBound_6670_: *mut crate::leanh::LeanObject,
    mut v___x_6671_: *mut crate::leanh::LeanObject,
    mut v_fst_6672_: *mut crate::leanh::LeanObject,
    mut v___x_6673_: *mut crate::leanh::LeanObject,
    mut v_inst_6674_: *mut crate::leanh::LeanObject,
    mut v_R_6675_: *mut crate::leanh::LeanObject,
    mut v_a_6676_: *mut crate::leanh::LeanObject,
    mut v_b_6677_: *mut crate::leanh::LeanObject,
    mut v_c_6678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6679_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_6670_, v___x_6671_, v_fst_6672_, v___x_6673_, v_inst_6674_, v_R_6675_, v_a_6676_, v_b_6677_, v_c_6678_);
    crate::leanh::lean_dec(v___x_6673_);
    crate::leanh::lean_dec_ref(v_fst_6672_);
    crate::leanh::lean_dec(v___x_6671_);
    crate::leanh::lean_dec(v_upperBound_6670_);
    return v_res_6679_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(
    mut v_lsize_6680_: *mut crate::leanh::LeanObject,
    mut v_rsize_6681_: *mut crate::leanh::LeanObject,
    mut v_histogram_6682_: *mut crate::leanh::LeanObject,
    mut v_index_6683_: *mut crate::leanh::LeanObject,
    mut v_val_6684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6685_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_6682_, v_index_6683_, v_val_6684_);
    return v___x_6685_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(
    mut v_lsize_6686_: *mut crate::leanh::LeanObject,
    mut v_rsize_6687_: *mut crate::leanh::LeanObject,
    mut v_histogram_6688_: *mut crate::leanh::LeanObject,
    mut v_index_6689_: *mut crate::leanh::LeanObject,
    mut v_val_6690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6691_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_6686_, v_rsize_6687_, v_histogram_6688_, v_index_6689_, v_val_6690_);
    crate::leanh::lean_dec(v_rsize_6687_);
    crate::leanh::lean_dec(v_lsize_6686_);
    return v_res_6691_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(
    mut v_upperBound_6692_: *mut crate::leanh::LeanObject,
    mut v_fst_6693_: *mut crate::leanh::LeanObject,
    mut v___x_6694_: *mut crate::leanh::LeanObject,
    mut v_fst_6695_: *mut crate::leanh::LeanObject,
    mut v_inst_6696_: *mut crate::leanh::LeanObject,
    mut v_R_6697_: *mut crate::leanh::LeanObject,
    mut v_a_6698_: *mut crate::leanh::LeanObject,
    mut v_b_6699_: *mut crate::leanh::LeanObject,
    mut v_c_6700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_6692_, v_fst_6693_, v___x_6694_, v_fst_6695_, v_a_6698_, v_b_6699_);
    return v___x_6701_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(
    mut v_upperBound_6702_: *mut crate::leanh::LeanObject,
    mut v_fst_6703_: *mut crate::leanh::LeanObject,
    mut v___x_6704_: *mut crate::leanh::LeanObject,
    mut v_fst_6705_: *mut crate::leanh::LeanObject,
    mut v_inst_6706_: *mut crate::leanh::LeanObject,
    mut v_R_6707_: *mut crate::leanh::LeanObject,
    mut v_a_6708_: *mut crate::leanh::LeanObject,
    mut v_b_6709_: *mut crate::leanh::LeanObject,
    mut v_c_6710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_6702_, v_fst_6703_, v___x_6704_, v_fst_6705_, v_inst_6706_, v_R_6707_, v_a_6708_, v_b_6709_, v_c_6710_);
    crate::leanh::lean_dec_ref(v_fst_6705_);
    crate::leanh::lean_dec(v___x_6704_);
    crate::leanh::lean_dec_ref(v_fst_6703_);
    crate::leanh::lean_dec(v_upperBound_6702_);
    return v_res_6711_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(
    mut v_00_u03b2_6712_: *mut crate::leanh::LeanObject,
    mut v_m_6713_: *mut crate::leanh::LeanObject,
    mut v_a_6714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_6713_, v_a_6714_);
    return v___x_6715_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(
    mut v_00_u03b2_6716_: *mut crate::leanh::LeanObject,
    mut v_m_6717_: *mut crate::leanh::LeanObject,
    mut v_a_6718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_6716_, v_m_6717_, v_a_6718_);
    crate::leanh::lean_dec_ref(v_a_6718_);
    crate::leanh::lean_dec_ref(v_m_6717_);
    return v_res_6719_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(
    mut v_00_u03b2_6720_: *mut crate::leanh::LeanObject,
    mut v_m_6721_: *mut crate::leanh::LeanObject,
    mut v_a_6722_: *mut crate::leanh::LeanObject,
    mut v_b_6723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6724_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_6721_, v_a_6722_, v_b_6723_);
    return v___x_6724_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(
    mut v_inst_6725_: *mut crate::leanh::LeanObject,
    mut v_R_6726_: *mut crate::leanh::LeanObject,
    mut v_a_6727_: *mut crate::leanh::LeanObject,
    mut v_b_6728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6729_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_6727_, v_b_6728_);
    return v___x_6729_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(
    mut v_00_u03b2_6730_: *mut crate::leanh::LeanObject,
    mut v_a_6731_: *mut crate::leanh::LeanObject,
    mut v_x_6732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6733_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_6731_, v_x_6732_);
    return v___x_6733_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(
    mut v_00_u03b2_6734_: *mut crate::leanh::LeanObject,
    mut v_a_6735_: *mut crate::leanh::LeanObject,
    mut v_x_6736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_6734_, v_a_6735_, v_x_6736_);
    crate::leanh::lean_dec(v_x_6736_);
    crate::leanh::lean_dec_ref(v_a_6735_);
    return v_res_6737_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(
    mut v_00_u03b2_6738_: *mut crate::leanh::LeanObject,
    mut v_a_6739_: *mut crate::leanh::LeanObject,
    mut v_x_6740_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6741_: u8 = 0;
    v___x_6741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_6739_, v_x_6740_);
    return v___x_6741_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(
    mut v_00_u03b2_6742_: *mut crate::leanh::LeanObject,
    mut v_a_6743_: *mut crate::leanh::LeanObject,
    mut v_x_6744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6745_: u8 = 0;
    let mut v_r_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_6742_, v_a_6743_, v_x_6744_);
    crate::leanh::lean_dec(v_x_6744_);
    crate::leanh::lean_dec_ref(v_a_6743_);
    v_r_6746_ = crate::leanh::lean_box((v_res_6745_) as usize);
    return v_r_6746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(
    mut v_00_u03b2_6747_: *mut crate::leanh::LeanObject,
    mut v_data_6748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_6748_);
    return v___x_6749_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(
    mut v_00_u03b2_6750_: *mut crate::leanh::LeanObject,
    mut v_a_6751_: *mut crate::leanh::LeanObject,
    mut v_b_6752_: *mut crate::leanh::LeanObject,
    mut v_x_6753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6754_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_6751_, v_b_6752_, v_x_6753_);
    return v___x_6754_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(
    mut v_00_u03b2_6755_: *mut crate::leanh::LeanObject,
    mut v_i_6756_: *mut crate::leanh::LeanObject,
    mut v_source_6757_: *mut crate::leanh::LeanObject,
    mut v_target_6758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6759_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_6756_, v_source_6757_, v_target_6758_);
    return v___x_6759_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(
    mut v_00_u03b2_6760_: *mut crate::leanh::LeanObject,
    mut v_x_6761_: *mut crate::leanh::LeanObject,
    mut v_x_6762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_6761_, v_x_6762_);
    return v___x_6763_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(
    mut v_s_6764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6765_ = lean_string_data(v_s_6764_);
    v___x_6766_ = lean_array_mk(v___x_6765_);
    return v___x_6766_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(
    mut v_s_6767_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6769_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_6767_);
    v___x_6770_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_6768_);
    v___x_6771_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_6769_, v___x_6770_);
    v___x_6772_ =
        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_6771_);
    crate::leanh::lean_dec_ref(v___x_6771_);
    return v___x_6772_;
}
pub unsafe fn l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(
    mut v_s_6773_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6775_: u8 = 0;
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6775_ = 1;
    v___x_6776_ = crate::leanh::lean_box((v___x_6775_) as usize);
    v___x_6777_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6777_, 0, v___x_6776_);
    crate::leanh::lean_ctor_set(v___x_6777_, 1, v_s_6773_);
    v___x_6778_ = 0;
    v___x_6779_ = crate::leanh::lean_box((v___x_6778_) as usize);
    v___x_6780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6780_, 0, v___x_6779_);
    crate::leanh::lean_ctor_set(v___x_6780_, 1, v_s_x27_6774_);
    v___x_6781_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6782_ = lean_mk_empty_array_with_capacity(v___x_6781_);
    v___x_6783_ = lean_array_push(v___x_6782_, v___x_6777_);
    v___x_6784_ = lean_array_push(v___x_6783_, v___x_6780_);
    return v___x_6784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(
    mut v_as_6785_: *mut crate::leanh::LeanObject,
    mut v_i_6786_: usize,
    mut v_stop_6787_: usize,
    mut v_b_6788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: usize = 0;
    let mut v___x_6792_: usize = 0;
    let mut v___x_6794_: u8 = 0;
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: u8 = 0;
    let mut v___x_6798_: u8 = 0;
    let mut v___x_6799_: u8 = 0;
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6794_ = lean_usize_dec_eq(v_i_6786_, v_stop_6787_);
                if v___x_6794_ == 0 {
                    v___x_6795_ = lean_array_uget_borrowed(v_as_6785_, v_i_6786_);
                    v_fst_6796_ = crate::leanh::lean_ctor_get(v___x_6795_, 0);
                    v___x_6797_ = 2;
                    v___x_6798_ = (crate::leanh::lean_unbox(v_fst_6796_) as u8);
                    v___x_6799_ = l_Lean_Diff_instBEqAction_beq(v___x_6798_, v___x_6797_);
                    if v___x_6799_ == 0 {
                        crate::leanh::lean_inc(v___x_6795_);
                        v___x_6800_ = lean_array_push(v_b_6788_, v___x_6795_);
                        v___y_6790_ = v___x_6800_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6790_ = v_b_6788_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6788_;
                }
            }
            1 => {
                v___x_6791_ = 1usize;
                v___x_6792_ = lean_usize_add(v_i_6786_, v___x_6791_);
                v_i_6786_ = v___x_6792_;
                v_b_6788_ = v___y_6790_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(
    mut v_as_6801_: *mut crate::leanh::LeanObject,
    mut v_i_6802_: *mut crate::leanh::LeanObject,
    mut v_stop_6803_: *mut crate::leanh::LeanObject,
    mut v_b_6804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6805_: usize = 0;
    let mut v_stop_boxed_6806_: usize = 0;
    let mut v_res_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6805_ = crate::leanh::lean_unbox_usize(v_i_6802_);
    crate::leanh::lean_dec(v_i_6802_);
    v_stop_boxed_6806_ = crate::leanh::lean_unbox_usize(v_stop_6803_);
    crate::leanh::lean_dec(v_stop_6803_);
    v_res_6807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_6801_, v_i_boxed_6805_, v_stop_boxed_6806_, v_b_6804_);
    crate::leanh::lean_dec_ref(v_as_6801_);
    return v_res_6807_;
}
pub unsafe fn l_Lean_Meta_Hint_readableDiff(
    mut v_s_6808_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6809_: *mut crate::leanh::LeanObject,
    mut v_granularity_6810_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6815_: u8 = 0;
    let mut v___x_6816_: u8 = 0;
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6819_: usize = 0;
    let mut v___x_6820_: usize = 0;
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_approxEditDistance_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charArrDiff_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: u8 = 0;
    let mut v___x_6832_: u8 = 0;
    let mut v___y_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxWordDiffDistance_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charDiffRaw_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: u8 = 0;
    let mut v___x_6848_: usize = 0;
    let mut v___x_6849_: usize = 0;
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: usize = 0;
    let mut v___x_6852_: usize = 0;
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxCharDiffDistance_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: u8 = 0;
    let mut v___x_6863_: u8 = 0;
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: u8 = 0;
    let mut v___x_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_granularity_6810_ {
                0 => {
                    v___x_6854_ = lean_string_length(v_s_6808_);
                    v___x_6855_ = lean_string_length(v_s_x27_6809_);
                    v___x_6863_ = lean_nat_dec_le(v___x_6854_, v___x_6855_);
                    if v___x_6863_ == 0 {
                        v___y_6857_ = v___x_6855_;
                        state = 4;
                        continue;
                    } else {
                        v___y_6857_ = v___x_6854_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v___x_6864_ =
                        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(
                            v_s_6808_,
                            v_s_x27_6809_,
                        );
                    return v___x_6864_;
                }
                2 => {
                    v___x_6865_ =
                        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(
                            v_s_6808_,
                            v_s_x27_6809_,
                        );
                    crate::leanh::lean_dec_ref(v_s_x27_6809_);
                    crate::leanh::lean_dec_ref(v_s_6808_);
                    return v___x_6865_;
                }
                3 => {
                    v___x_6866_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(
                        v_s_6808_,
                        v_s_x27_6809_,
                    );
                    return v___x_6866_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_s_6808_);
                    v___x_6867_ = 0;
                    v___x_6868_ = crate::leanh::lean_box((v___x_6867_) as usize);
                    v___x_6869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6869_, 0, v___x_6868_);
                    crate::leanh::lean_ctor_set(v___x_6869_, 1, v_s_x27_6809_);
                    v___x_6870_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6871_ = lean_mk_empty_array_with_capacity(v___x_6870_);
                    v___x_6872_ = lean_array_push(v___x_6871_, v___x_6869_);
                    return v___x_6872_;
                }
            },
            1 => {
                if v___y_6815_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6812_);
                    v___x_6816_ = lean_nat_dec_le(v___y_6814_, v___y_6813_);
                    crate::leanh::lean_dec(v___y_6813_);
                    crate::leanh::lean_dec(v___y_6814_);
                    if v___x_6816_ == 0 {
                        v___x_6817_ =
                            l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(
                                v_s_6808_,
                                v_s_x27_6809_,
                            );
                        return v___x_6817_;
                    } else {
                        v___x_6818_ =
                            l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(
                                v_s_6808_,
                                v_s_x27_6809_,
                            );
                        crate::leanh::lean_dec_ref(v_s_x27_6809_);
                        crate::leanh::lean_dec_ref(v_s_6808_);
                        return v___x_6818_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6814_);
                    crate::leanh::lean_dec(v___y_6813_);
                    crate::leanh::lean_dec_ref(v_s_x27_6809_);
                    crate::leanh::lean_dec_ref(v_s_6808_);
                    v_sz_6819_ = lean_array_size(v___y_6812_);
                    v___x_6820_ = 0usize;
                    v___x_6821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_6819_, v___x_6820_, v___y_6812_);
                    return v___x_6821_;
                }
            }
            2 => {
                v_approxEditDistance_6827_ = lean_array_get_size(v___y_6826_);
                crate::leanh::lean_dec_ref(v___y_6826_);
                v_charArrDiff_6828_ =
                    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(
                        v___y_6823_,
                    );
                crate::leanh::lean_dec_ref(v___y_6823_);
                v___x_6829_ = lean_array_get_size(v_charArrDiff_6828_);
                v___x_6830_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6831_ = lean_nat_dec_le(v___x_6829_, v___x_6830_);
                if v___x_6831_ == 0 {
                    v___x_6832_ = lean_nat_dec_le(v_approxEditDistance_6827_, v___y_6824_);
                    crate::leanh::lean_dec(v___y_6824_);
                    v___y_6812_ = v_charArrDiff_6828_;
                    v___y_6813_ = v___y_6825_;
                    v___y_6814_ = v_approxEditDistance_6827_;
                    v___y_6815_ = v___x_6832_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6824_);
                    v___y_6812_ = v_charArrDiff_6828_;
                    v___y_6813_ = v___y_6825_;
                    v___y_6814_ = v_approxEditDistance_6827_;
                    v___y_6815_ = v___x_6831_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6838_ = lean_nat_shiftr(v___y_6837_, v___y_6834_);
                crate::leanh::lean_dec(v___y_6837_);
                v_maxWordDiffDistance_6839_ = lean_nat_add(v___y_6836_, v___x_6838_);
                crate::leanh::lean_dec(v___x_6838_);
                crate::leanh::lean_dec(v___y_6836_);
                crate::leanh::lean_inc_ref(v_s_6808_);
                v___x_6840_ =
                    l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_6808_);
                crate::leanh::lean_inc_ref(v_s_x27_6809_);
                v___x_6841_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(
                    v_s_x27_6809_,
                );
                v_charDiffRaw_6842_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_6840_, v___x_6841_);
                v___x_6843_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6844_ = lean_array_get_size(v_charDiffRaw_6842_);
                v___x_6845_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0;
                v___x_6846_ = lean_nat_dec_lt(v___x_6843_, v___x_6844_);
                if v___x_6846_ == 0 {
                    v___y_6823_ = v_charDiffRaw_6842_;
                    v___y_6824_ = v___y_6835_;
                    v___y_6825_ = v_maxWordDiffDistance_6839_;
                    v___y_6826_ = v___x_6845_;
                    state = 2;
                    continue;
                } else {
                    v___x_6847_ = lean_nat_dec_le(v___x_6844_, v___x_6844_);
                    if v___x_6847_ == 0 {
                        if v___x_6846_ == 0 {
                            v___y_6823_ = v_charDiffRaw_6842_;
                            v___y_6824_ = v___y_6835_;
                            v___y_6825_ = v_maxWordDiffDistance_6839_;
                            v___y_6826_ = v___x_6845_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6848_ = 0usize;
                            v___x_6849_ = lean_usize_of_nat(v___x_6844_);
                            v___x_6850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_6842_, v___x_6848_, v___x_6849_, v___x_6845_);
                            v___y_6823_ = v_charDiffRaw_6842_;
                            v___y_6824_ = v___y_6835_;
                            v___y_6825_ = v_maxWordDiffDistance_6839_;
                            v___y_6826_ = v___x_6850_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_6851_ = 0usize;
                        v___x_6852_ = lean_usize_of_nat(v___x_6844_);
                        v___x_6853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_6842_, v___x_6851_, v___x_6852_, v___x_6845_);
                        v___y_6823_ = v_charDiffRaw_6842_;
                        v___y_6824_ = v___y_6835_;
                        v___y_6825_ = v_maxWordDiffDistance_6839_;
                        v___y_6826_ = v___x_6853_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6858_ = crate::leanh::lean_unsigned_to_nat(5);
                v_maxCharDiffDistance_6859_ = lean_nat_div(v___y_6857_, v___x_6858_);
                v___x_6860_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6861_ = lean_nat_shiftr(v___y_6857_, v___x_6860_);
                crate::leanh::lean_dec(v___y_6857_);
                v___x_6862_ = lean_nat_dec_le(v___x_6854_, v___x_6855_);
                if v___x_6862_ == 0 {
                    v___y_6834_ = v___x_6860_;
                    v___y_6835_ = v_maxCharDiffDistance_6859_;
                    v___y_6836_ = v___x_6861_;
                    v___y_6837_ = v___x_6854_;
                    state = 3;
                    continue;
                } else {
                    v___y_6834_ = v___x_6860_;
                    v___y_6835_ = v_maxCharDiffDistance_6859_;
                    v___y_6836_ = v___x_6861_;
                    v___y_6837_ = v___x_6855_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Hint_readableDiff___boxed(
    mut v_s_6873_: *mut crate::leanh::LeanObject,
    mut v_s_x27_6874_: *mut crate::leanh::LeanObject,
    mut v_granularity_6875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_granularity_boxed_6876_: u8 = 0;
    let mut v_res_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_granularity_boxed_6876_ = (crate::leanh::lean_unbox(v_granularity_6875_) as u8);
    v_res_6877_ =
        l_Lean_Meta_Hint_readableDiff(v_s_6873_, v_s_x27_6874_, v_granularity_boxed_6876_);
    return v_res_6877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(
    mut v_as_6878_: *mut crate::leanh::LeanObject,
    mut v_i_6879_: usize,
    mut v_stop_6880_: usize,
    mut v_b_6881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6882_: u8 = 0;
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: usize = 0;
    let mut v___x_6887_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6882_ = lean_usize_dec_eq(v_i_6879_, v_stop_6880_);
                if v___x_6882_ == 0 {
                    v___x_6883_ = lean_array_uget_borrowed(v_as_6878_, v_i_6879_);
                    v_snd_6884_ = crate::leanh::lean_ctor_get(v___x_6883_, 1);
                    v___x_6885_ = lean_string_append(v_b_6881_, v_snd_6884_);
                    v___x_6886_ = 1usize;
                    v___x_6887_ = lean_usize_add(v_i_6879_, v___x_6886_);
                    v_i_6879_ = v___x_6887_;
                    v_b_6881_ = v___x_6885_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6881_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(
    mut v_as_6889_: *mut crate::leanh::LeanObject,
    mut v_i_6890_: *mut crate::leanh::LeanObject,
    mut v_stop_6891_: *mut crate::leanh::LeanObject,
    mut v_b_6892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6893_: usize = 0;
    let mut v_stop_boxed_6894_: usize = 0;
    let mut v_res_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6893_ = crate::leanh::lean_unbox_usize(v_i_6890_);
    crate::leanh::lean_dec(v_i_6890_);
    v_stop_boxed_6894_ = crate::leanh::lean_unbox_usize(v_stop_6891_);
    crate::leanh::lean_dec(v_stop_6891_);
    v_res_6895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_6889_, v_i_boxed_6893_, v_stop_boxed_6894_, v_b_6892_);
    crate::leanh::lean_dec_ref(v_as_6889_);
    return v_res_6895_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(
    mut v_t_6896_: *mut crate::leanh::LeanObject,
    mut v___y_6897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6901_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6916_: u8 = 0;
    let mut v_enabled_6917_: u8 = 0;
    let mut v_assignment_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6923_: u8 = 0;
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut v_isSharedCheck_6935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6899_ = lean_st_ref_get(v___y_6897_);
                v_infoState_6900_ = crate::leanh::lean_ctor_get(v___x_6899_, 7);
                crate::leanh::lean_inc_ref(v_infoState_6900_);
                crate::leanh::lean_dec(v___x_6899_);
                v_enabled_6901_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_6900_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_6900_);
                if v_enabled_6901_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_6896_);
                    v___x_6902_ = crate::leanh::lean_box(0);
                    v___x_6903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6903_, 0, v___x_6902_);
                    return v___x_6903_;
                } else {
                    v___x_6904_ = lean_st_ref_take(v___y_6897_);
                    v_infoState_6905_ = crate::leanh::lean_ctor_get(v___x_6904_, 7);
                    v_env_6906_ = crate::leanh::lean_ctor_get(v___x_6904_, 0);
                    v_nextMacroScope_6907_ = crate::leanh::lean_ctor_get(v___x_6904_, 1);
                    v_ngen_6908_ = crate::leanh::lean_ctor_get(v___x_6904_, 2);
                    v_auxDeclNGen_6909_ = crate::leanh::lean_ctor_get(v___x_6904_, 3);
                    v_traceState_6910_ = crate::leanh::lean_ctor_get(v___x_6904_, 4);
                    v_cache_6911_ = crate::leanh::lean_ctor_get(v___x_6904_, 5);
                    v_messages_6912_ = crate::leanh::lean_ctor_get(v___x_6904_, 6);
                    v_snapshotTasks_6913_ = crate::leanh::lean_ctor_get(v___x_6904_, 8);
                    v_isSharedCheck_6935_ = (!crate::leanh::lean_is_exclusive(v___x_6904_)) as u8;
                    if v_isSharedCheck_6935_ == 0 {
                        v___x_6915_ = v___x_6904_;
                        v_isShared_6916_ = v_isSharedCheck_6935_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_6913_);
                        crate::leanh::lean_inc(v_infoState_6905_);
                        crate::leanh::lean_inc(v_messages_6912_);
                        crate::leanh::lean_inc(v_cache_6911_);
                        crate::leanh::lean_inc(v_traceState_6910_);
                        crate::leanh::lean_inc(v_auxDeclNGen_6909_);
                        crate::leanh::lean_inc(v_ngen_6908_);
                        crate::leanh::lean_inc(v_nextMacroScope_6907_);
                        crate::leanh::lean_inc(v_env_6906_);
                        crate::leanh::lean_dec(v___x_6904_);
                        v___x_6915_ = crate::leanh::lean_box(0);
                        v_isShared_6916_ = v_isSharedCheck_6935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_6917_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_6905_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_6918_ = crate::leanh::lean_ctor_get(v_infoState_6905_, 0);
                v_lazyAssignment_6919_ = crate::leanh::lean_ctor_get(v_infoState_6905_, 1);
                v_trees_6920_ = crate::leanh::lean_ctor_get(v_infoState_6905_, 2);
                v_isSharedCheck_6934_ = (!crate::leanh::lean_is_exclusive(v_infoState_6905_)) as u8;
                if v_isSharedCheck_6934_ == 0 {
                    v___x_6922_ = v_infoState_6905_;
                    v_isShared_6923_ = v_isSharedCheck_6934_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_6920_);
                    crate::leanh::lean_inc(v_lazyAssignment_6919_);
                    crate::leanh::lean_inc(v_assignment_6918_);
                    crate::leanh::lean_dec(v_infoState_6905_);
                    v___x_6922_ = crate::leanh::lean_box(0);
                    v_isShared_6923_ = v_isSharedCheck_6934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6924_ = l_Lean_PersistentArray_push___redArg(v_trees_6920_, v_t_6896_);
                if v_isShared_6923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6922_, 2, v___x_6924_);
                    v___x_6926_ = v___x_6922_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6933_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_assignment_6918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 1, v_lazyAssignment_6919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 2, v___x_6924_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6933_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_6917_,
                    );
                    v___x_6926_ = v_reuseFailAlloc_6933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6915_, 7, v___x_6926_);
                    v___x_6928_ = v___x_6915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6932_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 0, v_env_6906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 1, v_nextMacroScope_6907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 2, v_ngen_6908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 3, v_auxDeclNGen_6909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 4, v_traceState_6910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 5, v_cache_6911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 6, v_messages_6912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 7, v___x_6926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 8, v_snapshotTasks_6913_);
                    v___x_6928_ = v_reuseFailAlloc_6932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6929_ = lean_st_ref_set(v___y_6897_, v___x_6928_);
                v___x_6930_ = crate::leanh::lean_box(0);
                v___x_6931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6931_, 0, v___x_6930_);
                return v___x_6931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(
    mut v_t_6936_: *mut crate::leanh::LeanObject,
    mut v___y_6937_: *mut crate::leanh::LeanObject,
    mut v___y_6938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6939_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_6936_, v___y_6937_);
    crate::leanh::lean_dec(v___y_6937_);
    return v_res_6939_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6940_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6941_ = lean_mk_empty_array_with_capacity(v___x_6940_);
    v___x_6942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6942_, 0, v___x_6941_);
    return v___x_6942_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6943_: usize = 0;
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ = 5usize;
    v___x_6944_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6945_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6946_ = lean_mk_empty_array_with_capacity(v___x_6945_);
    v___x_6947_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
    v___x_6948_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6948_, 0, v___x_6947_);
    crate::leanh::lean_ctor_set(v___x_6948_, 1, v___x_6946_);
    crate::leanh::lean_ctor_set(v___x_6948_, 2, v___x_6944_);
    crate::leanh::lean_ctor_set(v___x_6948_, 3, v___x_6944_);
    crate::leanh::lean_ctor_set_usize(v___x_6948_, 4, v___x_6943_);
    return v___x_6948_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(
    mut v_t_6949_: *mut crate::leanh::LeanObject,
    mut v___y_6950_: *mut crate::leanh::LeanObject,
    mut v___y_6951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6955_: u8 = 0;
    v___x_6953_ = lean_st_ref_get(v___y_6951_);
    v_infoState_6954_ = crate::leanh::lean_ctor_get(v___x_6953_, 7);
    crate::leanh::lean_inc_ref(v_infoState_6954_);
    crate::leanh::lean_dec(v___x_6953_);
    v_enabled_6955_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_6954_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_6954_);
    if v_enabled_6955_ == 0 {
        let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_6949_);
        v___x_6956_ = crate::leanh::lean_box(0);
        v___x_6957_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6957_, 0, v___x_6956_);
        return v___x_6957_;
    } else {
        let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
        v___x_6959_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6959_, 0, v_t_6949_);
        crate::leanh::lean_ctor_set(v___x_6959_, 1, v___x_6958_);
        v___x_6960_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_6959_, v___y_6951_);
        return v___x_6960_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(
    mut v_t_6961_: *mut crate::leanh::LeanObject,
    mut v___y_6962_: *mut crate::leanh::LeanObject,
    mut v___y_6963_: *mut crate::leanh::LeanObject,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6965_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(
        v_t_6961_,
        v___y_6962_,
        v___y_6963_,
    );
    crate::leanh::lean_dec(v___y_6963_);
    crate::leanh::lean_dec_ref(v___y_6962_);
    return v_res_6965_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(
    mut v___x_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6968_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6968_, 0, v___x_6966_);
    crate::leanh::lean_ctor_set(v___x_6968_, 1, v___y_6967_);
    return v___x_6968_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0;
    v___x_6971_ = l_Lean_stringToMessageData(v___x_6970_);
    return v___x_6971_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2;
    v___x_6974_ = l_Lean_stringToMessageData(v___x_6973_);
    return v___x_6974_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28;
    v___x_7024_ = l_Lean_Json_mkObj(v___x_7023_);
    return v___x_7024_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7025_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
    v___x_7026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19;
    v___x_7027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7027_, 0, v___x_7026_);
    crate::leanh::lean_ctor_set(v___x_7027_, 1, v___x_7025_);
    return v___x_7027_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7028_ = crate::leanh::lean_box(0);
    v___x_7029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
    v___x_7030_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7030_, 0, v___x_7029_);
    crate::leanh::lean_ctor_set(v___x_7030_, 1, v___x_7028_);
    return v___x_7030_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32;
    v___x_7034_ = l_Lean_MessageData_ofFormat(v___x_7033_);
    return v___x_7034_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34;
    v___x_7037_ = l_Lean_stringToMessageData(v___x_7036_);
    return v___x_7037_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(
    mut v_suggestions_7039_: *mut crate::leanh::LeanObject,
    mut v_forceList_7040_: u8,
    mut v_codeActionPrefix_x3f_7041_: *mut crate::leanh::LeanObject,
    mut v_ref_7042_: *mut crate::leanh::LeanObject,
    mut v_as_7043_: *mut crate::leanh::LeanObject,
    mut v_sz_7044_: usize,
    mut v_i_7045_: usize,
    mut v_b_7046_: *mut crate::leanh::LeanObject,
    mut v___y_7047_: *mut crate::leanh::LeanObject,
    mut v___y_7048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: usize = 0;
    let mut v___x_7053_: usize = 0;
    let mut v___y_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_7080_: u64 = 0;
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: u8 = 0;
    let mut v___x_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: u8 = 0;
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_span_x3f_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7105_: u8 = 0;
    let mut v___y_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: u8 = 0;
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: usize = 0;
    let mut v___x_7128_: usize = 0;
    let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: usize = 0;
    let mut v___x_7131_: usize = 0;
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7140_: u8 = 0;
    let mut v___y_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_7143_: u64 = 0;
    let mut v_suggestion_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageData_x3f_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7172_: u8 = 0;
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7177_: u8 = 0;
    let mut v_val_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7187_: u8 = 0;
    let mut v_messageData_x3f_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7196_: u8 = 0;
    let mut v___y_7197_: u8 = 0;
    let mut v___y_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postInfo_x3f_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7206_: u8 = 0;
    let mut v___y_7207_: u8 = 0;
    let mut v___y_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7215_: u8 = 0;
    let mut v___y_7216_: u8 = 0;
    let mut v_edits_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preInfo_x3f_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postInfo_x3f_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postInfo_x3f_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7229_: u8 = 0;
    let mut v___y_7230_: u8 = 0;
    let mut v___y_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edits_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v_source_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: u8 = 0;
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7246_: u8 = 0;
    let mut v___y_7247_: u8 = 0;
    let mut v___y_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edits_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: u8 = 0;
    let mut v_fileMap_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7261_: u8 = 0;
    let mut v___x_7262_: u8 = 0;
    let mut v_source_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: u8 = 0;
    let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7274_: u8 = 0;
    let mut v___x_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7284_: u8 = 0;
    let mut v___y_7285_: u8 = 0;
    let mut v___y_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageData_x3f_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: u8 = 0;
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7316_: u8 = 0;
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7320_: u8 = 0;
    let mut v___y_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7328_: u8 = 0;
    let mut v___y_7329_: u8 = 0;
    let mut v___y_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCodeActionTitle_x3f_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: u8 = 0;
    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTryThisSuggestion_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_previewSpan_x3f_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffGranularity_7346_: u8 = 0;
    let mut v___x_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7356_: u8 = 0;
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7360_: u8 = 0;
    let mut v_val_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7095_ = lean_usize_dec_lt(v_i_7045_, v_sz_7044_);
                if v___x_7095_ == 0 {
                    crate::leanh::lean_dec(v_ref_7042_);
                    crate::leanh::lean_dec(v_codeActionPrefix_x3f_7041_);
                    v___x_7096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7096_, 0, v_b_7046_);
                    return v___x_7096_;
                } else {
                    v_a_7097_ = lean_array_uget_borrowed(v_as_7043_, v_i_7045_);
                    v_span_x3f_7098_ = crate::leanh::lean_ctor_get(v_a_7097_, 1);
                    v___x_7099_ =
                        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
                    v___x_7275_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
                    if crate::leanh::lean_obj_tag(v_span_x3f_7098_) == 0 {
                        crate::leanh::lean_inc(v_ref_7042_);
                        v___y_7340_ = v_ref_7042_;
                        state = 22;
                        continue;
                    } else {
                        v_val_7361_ = crate::leanh::lean_ctor_get(v_span_x3f_7098_, 0);
                        crate::leanh::lean_inc(v_val_7361_);
                        v___y_7340_ = v_val_7361_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7052_ = 1usize;
                v___x_7053_ = lean_usize_add(v_i_7045_, v___x_7052_);
                v_i_7045_ = v___x_7053_;
                v_b_7046_ = v_a_7051_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7057_ = l_Lean_MessageData_nestD(v___y_7056_);
                v___x_7058_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7058_, 0, v_b_7046_);
                crate::leanh::lean_ctor_set(v___x_7058_, 1, v___x_7057_);
                v_a_7051_ = v___x_7058_;
                state = 1;
                continue;
            }
            3 => {
                v___x_7063_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7063_, 0, v___y_7061_);
                crate::leanh::lean_ctor_set(v___x_7063_, 1, v___y_7062_);
                v___x_7064_ = l_Lean_stringToMessageData(v___y_7060_);
                v___x_7065_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7065_, 0, v___x_7063_);
                crate::leanh::lean_ctor_set(v___x_7065_, 1, v___x_7064_);
                v___y_7056_ = v___x_7065_;
                state = 2;
                continue;
            }
            4 => {
                v___x_7068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
                v___x_7069_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
                v___x_7071_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7071_, 0, v___x_7070_);
                crate::leanh::lean_ctor_set(v___x_7071_, 1, v___y_7067_);
                v___x_7072_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7072_, 0, v___x_7069_);
                crate::leanh::lean_ctor_set(v___x_7072_, 1, v___x_7071_);
                v___x_7073_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7073_, 0, v___x_7068_);
                crate::leanh::lean_ctor_set(v___x_7073_, 1, v___x_7072_);
                v___y_7056_ = v___x_7073_;
                state = 2;
                continue;
            }
            5 => {
                v___x_7079_ = l_Lean_Meta_Hint_tryThisDiffWidget;
                v_javascriptHash_7080_ = crate::leanh::lean_ctor_get_uint64(
                    v___x_7079_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_7081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8;
                v___x_7082_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_7082_, 0, v___x_7081_);
                crate::leanh::lean_ctor_set(v___x_7082_, 1, v___y_7077_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_7082_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_javascriptHash_7080_,
                );
                v___x_7083_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7083_, 0, v___y_7078_);
                v___x_7084_ = l_Lean_MessageData_ofFormat(v___x_7083_);
                v___x_7085_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7085_, 0, v___x_7082_);
                crate::leanh::lean_ctor_set(v___x_7085_, 1, v___x_7084_);
                v___x_7086_ = l_Lean_stringToMessageData(v___y_7075_);
                v___x_7087_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7087_, 0, v___x_7086_);
                crate::leanh::lean_ctor_set(v___x_7087_, 1, v___x_7085_);
                v___x_7088_ = l_Lean_stringToMessageData(v___y_7076_);
                v___x_7089_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7089_, 0, v___x_7087_);
                crate::leanh::lean_ctor_set(v___x_7089_, 1, v___x_7088_);
                v___x_7090_ = lean_array_get_size(v_suggestions_7039_);
                v___x_7091_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7092_ = lean_nat_dec_eq(v___x_7090_, v___x_7091_);
                if v___x_7092_ == 0 {
                    v___y_7067_ = v___x_7089_;
                    state = 4;
                    continue;
                } else {
                    if v_forceList_7040_ == 0 {
                        if v___x_7092_ == 0 {
                            v___y_7067_ = v___x_7089_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
                            v___x_7094_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7094_, 0, v___x_7093_);
                            crate::leanh::lean_ctor_set(v___x_7094_, 1, v___x_7089_);
                            v___y_7056_ = v___x_7094_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_7067_ = v___x_7089_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_7103_);
                v___x_7107_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_7103_);
                v___x_7108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9;
                v___x_7109_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7109_, 0, v___x_7108_);
                crate::leanh::lean_ctor_set(v___x_7109_, 1, v___x_7107_);
                v___x_7110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10;
                v___x_7111_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7111_, 0, v___y_7104_);
                v___x_7112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7112_, 0, v___x_7110_);
                crate::leanh::lean_ctor_set(v___x_7112_, 1, v___x_7111_);
                v___x_7113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11;
                v___x_7114_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_7101_);
                v___x_7115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7115_, 0, v___x_7113_);
                crate::leanh::lean_ctor_set(v___x_7115_, 1, v___x_7114_);
                v___x_7116_ = crate::leanh::lean_box(0);
                v___x_7117_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7117_, 0, v___x_7115_);
                crate::leanh::lean_ctor_set(v___x_7117_, 1, v___x_7116_);
                v___x_7118_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7118_, 0, v___x_7112_);
                crate::leanh::lean_ctor_set(v___x_7118_, 1, v___x_7117_);
                v___x_7119_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7119_, 0, v___x_7109_);
                crate::leanh::lean_ctor_set(v___x_7119_, 1, v___x_7118_);
                v___x_7120_ = l_Lean_Json_mkObj(v___x_7119_);
                crate::leanh::lean_dec_ref_known(v___x_7119_, 2);
                v___f_7121_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_7121_, 0, v___x_7120_);
                if v___y_7105_ == 0 {
                    v___x_7122_ =
                        l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_7103_);
                    v___y_7075_ = v___y_7102_;
                    v___y_7076_ = v___y_7106_;
                    v___y_7077_ = v___f_7121_;
                    v___y_7078_ = v___x_7122_;
                    state = 5;
                    continue;
                } else {
                    v___x_7123_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7124_ = lean_array_get_size(v___y_7103_);
                    v___x_7125_ = lean_nat_dec_lt(v___x_7123_, v___x_7124_);
                    if v___x_7125_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_7103_);
                        v___y_7075_ = v___y_7102_;
                        v___y_7076_ = v___y_7106_;
                        v___y_7077_ = v___f_7121_;
                        v___y_7078_ = v___x_7099_;
                        state = 5;
                        continue;
                    } else {
                        v___x_7126_ = lean_nat_dec_le(v___x_7124_, v___x_7124_);
                        if v___x_7126_ == 0 {
                            if v___x_7125_ == 0 {
                                crate::leanh::lean_dec_ref(v___y_7103_);
                                v___y_7075_ = v___y_7102_;
                                v___y_7076_ = v___y_7106_;
                                v___y_7077_ = v___f_7121_;
                                v___y_7078_ = v___x_7099_;
                                state = 5;
                                continue;
                            } else {
                                v___x_7127_ = 0usize;
                                v___x_7128_ = lean_usize_of_nat(v___x_7124_);
                                v___x_7129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_7103_, v___x_7127_, v___x_7128_, v___x_7099_);
                                crate::leanh::lean_dec_ref(v___y_7103_);
                                v___y_7075_ = v___y_7102_;
                                v___y_7076_ = v___y_7106_;
                                v___y_7077_ = v___f_7121_;
                                v___y_7078_ = v___x_7129_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_7130_ = 0usize;
                            v___x_7131_ = lean_usize_of_nat(v___x_7124_);
                            v___x_7132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_7103_, v___x_7130_, v___x_7131_, v___x_7099_);
                            crate::leanh::lean_dec_ref(v___y_7103_);
                            v___y_7075_ = v___y_7102_;
                            v___y_7076_ = v___y_7106_;
                            v___y_7077_ = v___f_7121_;
                            v___y_7078_ = v___x_7132_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_7138_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_7136_);
                    v___x_7142_ = l_Lean_Meta_Hint_textInsertionWidget;
                    v_javascriptHash_7143_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_7142_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_suggestion_7144_ = crate::leanh::lean_ctor_get(v___y_7137_, 0);
                    crate::leanh::lean_inc_ref(v_suggestion_7144_);
                    v_messageData_x3f_7145_ = crate::leanh::lean_ctor_get(v___y_7137_, 4);
                    crate::leanh::lean_inc(v_messageData_x3f_7145_);
                    crate::leanh::lean_dec_ref(v___y_7137_);
                    v___x_7146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18;
                    v___x_7147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11;
                    v___x_7148_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_7134_);
                    v___x_7149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7149_, 0, v___x_7147_);
                    crate::leanh::lean_ctor_set(v___x_7149_, 1, v___x_7148_);
                    v___x_7150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10;
                    v___x_7151_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7151_, 0, v___y_7139_);
                    v___x_7152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7152_, 0, v___x_7150_);
                    crate::leanh::lean_ctor_set(v___x_7152_, 1, v___x_7151_);
                    v___x_7153_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
                    v___x_7154_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7154_, 0, v___x_7152_);
                    crate::leanh::lean_ctor_set(v___x_7154_, 1, v___x_7153_);
                    v___x_7155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7155_, 0, v___x_7149_);
                    crate::leanh::lean_ctor_set(v___x_7155_, 1, v___x_7154_);
                    v___x_7156_ = l_Lean_Json_mkObj(v___x_7155_);
                    crate::leanh::lean_dec_ref_known(v___x_7155_, 2);
                    v___f_7157_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_7157_, 0, v___x_7156_);
                    v___x_7158_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
                    crate::leanh::lean_ctor_set(v___x_7158_, 0, v___x_7146_);
                    crate::leanh::lean_ctor_set(v___x_7158_, 1, v___f_7157_);
                    crate::leanh::lean_ctor_set_uint64(
                        v___x_7158_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_javascriptHash_7143_,
                    );
                    v___x_7159_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
                    v___x_7160_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7160_, 0, v___x_7158_);
                    crate::leanh::lean_ctor_set(v___x_7160_, 1, v___x_7159_);
                    v___x_7161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
                    v___x_7162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7162_, 0, v___x_7161_);
                    crate::leanh::lean_ctor_set(v___x_7162_, 1, v___x_7160_);
                    v___x_7163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
                    v___x_7164_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7164_, 0, v___x_7162_);
                    crate::leanh::lean_ctor_set(v___x_7164_, 1, v___x_7163_);
                    v___x_7165_ = l_Lean_stringToMessageData(v___y_7135_);
                    v___x_7166_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7166_, 0, v___x_7164_);
                    crate::leanh::lean_ctor_set(v___x_7166_, 1, v___x_7165_);
                    if crate::leanh::lean_obj_tag(v_messageData_x3f_7145_) == 0 {
                        if crate::leanh::lean_obj_tag(v_suggestion_7144_) == 0 {
                            v_a_7167_ = crate::leanh::lean_ctor_get(v_suggestion_7144_, 1);
                            crate::leanh::lean_inc(v_a_7167_);
                            crate::leanh::lean_dec_ref_known(v_suggestion_7144_, 2);
                            v___x_7168_ = l_Lean_MessageData_ofSyntax(v_a_7167_);
                            v___y_7060_ = v___y_7141_;
                            v___y_7061_ = v___x_7166_;
                            v___y_7062_ = v___x_7168_;
                            state = 3;
                            continue;
                        } else {
                            v_a_7169_ = crate::leanh::lean_ctor_get(v_suggestion_7144_, 0);
                            v_isSharedCheck_7177_ =
                                (!crate::leanh::lean_is_exclusive(v_suggestion_7144_)) as u8;
                            if v_isSharedCheck_7177_ == 0 {
                                v___x_7171_ = v_suggestion_7144_;
                                v_isShared_7172_ = v_isSharedCheck_7177_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7169_);
                                crate::leanh::lean_dec(v_suggestion_7144_);
                                v___x_7171_ = crate::leanh::lean_box(0);
                                v_isShared_7172_ = v_isSharedCheck_7177_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_suggestion_7144_);
                        v_val_7178_ = crate::leanh::lean_ctor_get(v_messageData_x3f_7145_, 0);
                        crate::leanh::lean_inc(v_val_7178_);
                        crate::leanh::lean_dec_ref_known(v_messageData_x3f_7145_, 1);
                        v___y_7060_ = v___y_7141_;
                        v___y_7061_ = v___x_7166_;
                        v___y_7062_ = v_val_7178_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_7138_, 1);
                    crate::leanh::lean_dec_ref(v___y_7137_);
                    v___y_7101_ = v___y_7134_;
                    v___y_7102_ = v___y_7135_;
                    v___y_7103_ = v___y_7136_;
                    v___y_7104_ = v___y_7139_;
                    v___y_7105_ = v___y_7140_;
                    v___y_7106_ = v___y_7141_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_7172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7171_, 3);
                    v___x_7174_ = v___x_7171_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7176_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_a_7169_);
                    v___x_7174_ = v_reuseFailAlloc_7176_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7175_ = l_Lean_MessageData_ofFormat(v___x_7174_);
                v___y_7060_ = v___y_7141_;
                v___y_7061_ = v___x_7166_;
                v___y_7062_ = v___x_7175_;
                state = 3;
                continue;
            }
            10 => {
                if v___y_7187_ == 0 {
                    v_messageData_x3f_7188_ = crate::leanh::lean_ctor_get(v___y_7184_, 4);
                    if crate::leanh::lean_obj_tag(v_messageData_x3f_7188_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_7184_);
                        crate::leanh::lean_dec(v___y_7183_);
                        v___y_7101_ = v___y_7180_;
                        v___y_7102_ = v___y_7181_;
                        v___y_7103_ = v___y_7182_;
                        v___y_7104_ = v___y_7185_;
                        v___y_7105_ = v___y_7187_;
                        v___y_7106_ = v___y_7186_;
                        state = 6;
                        continue;
                    } else {
                        v___y_7134_ = v___y_7180_;
                        v___y_7135_ = v___y_7181_;
                        v___y_7136_ = v___y_7182_;
                        v___y_7137_ = v___y_7184_;
                        v___y_7138_ = v___y_7183_;
                        v___y_7139_ = v___y_7185_;
                        v___y_7140_ = v___y_7187_;
                        v___y_7141_ = v___y_7186_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_7134_ = v___y_7180_;
                    v___y_7135_ = v___y_7181_;
                    v___y_7136_ = v___y_7182_;
                    v___y_7137_ = v___y_7184_;
                    v___y_7138_ = v___y_7183_;
                    v___y_7139_ = v___y_7185_;
                    v___y_7140_ = v___y_7187_;
                    v___y_7141_ = v___y_7186_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                if v___y_7196_ == 4 {
                    v___y_7180_ = v___y_7190_;
                    v___y_7181_ = v___y_7191_;
                    v___y_7182_ = v___y_7192_;
                    v___y_7183_ = v___y_7194_;
                    v___y_7184_ = v___y_7193_;
                    v___y_7185_ = v___y_7195_;
                    v___y_7186_ = v___y_7198_;
                    v___y_7187_ = v___x_7095_;
                    state = 10;
                    continue;
                } else {
                    v___y_7180_ = v___y_7190_;
                    v___y_7181_ = v___y_7191_;
                    v___y_7182_ = v___y_7192_;
                    v___y_7183_ = v___y_7194_;
                    v___y_7184_ = v___y_7193_;
                    v___y_7185_ = v___y_7195_;
                    v___y_7186_ = v___y_7198_;
                    v___y_7187_ = v___y_7197_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_postInfo_x3f_7204_) == 0 {
                    v___y_7190_ = v___y_7200_;
                    v___y_7191_ = v___y_7208_;
                    v___y_7192_ = v___y_7201_;
                    v___y_7193_ = v___y_7203_;
                    v___y_7194_ = v___y_7202_;
                    v___y_7195_ = v___y_7205_;
                    v___y_7196_ = v___y_7206_;
                    v___y_7197_ = v___y_7207_;
                    v___y_7198_ = v___x_7099_;
                    state = 11;
                    continue;
                } else {
                    v_val_7209_ = crate::leanh::lean_ctor_get(v_postInfo_x3f_7204_, 0);
                    crate::leanh::lean_inc(v_val_7209_);
                    crate::leanh::lean_dec_ref_known(v_postInfo_x3f_7204_, 1);
                    v___y_7190_ = v___y_7200_;
                    v___y_7191_ = v___y_7208_;
                    v___y_7192_ = v___y_7201_;
                    v___y_7193_ = v___y_7203_;
                    v___y_7194_ = v___y_7202_;
                    v___y_7195_ = v___y_7205_;
                    v___y_7196_ = v___y_7206_;
                    v___y_7197_ = v___y_7207_;
                    v___y_7198_ = v_val_7209_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v_preInfo_x3f_7218_ = crate::leanh::lean_ctor_get(v___y_7212_, 1);
                if crate::leanh::lean_obj_tag(v_preInfo_x3f_7218_) == 0 {
                    v_postInfo_x3f_7219_ = crate::leanh::lean_ctor_get(v___y_7212_, 2);
                    crate::leanh::lean_inc(v_postInfo_x3f_7219_);
                    v___y_7200_ = v___y_7211_;
                    v___y_7201_ = v_edits_7217_;
                    v___y_7202_ = v___y_7213_;
                    v___y_7203_ = v___y_7212_;
                    v_postInfo_x3f_7204_ = v_postInfo_x3f_7219_;
                    v___y_7205_ = v___y_7214_;
                    v___y_7206_ = v___y_7215_;
                    v___y_7207_ = v___y_7216_;
                    v___y_7208_ = v___x_7099_;
                    state = 12;
                    continue;
                } else {
                    v_postInfo_x3f_7220_ = crate::leanh::lean_ctor_get(v___y_7212_, 2);
                    crate::leanh::lean_inc(v_postInfo_x3f_7220_);
                    v_val_7221_ = crate::leanh::lean_ctor_get(v_preInfo_x3f_7218_, 0);
                    crate::leanh::lean_inc(v_val_7221_);
                    v___y_7200_ = v___y_7211_;
                    v___y_7201_ = v_edits_7217_;
                    v___y_7202_ = v___y_7213_;
                    v___y_7203_ = v___y_7212_;
                    v_postInfo_x3f_7204_ = v_postInfo_x3f_7220_;
                    v___y_7205_ = v___y_7214_;
                    v___y_7206_ = v___y_7215_;
                    v___y_7207_ = v___y_7216_;
                    v___y_7208_ = v_val_7221_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_7233_ = lean_nat_dec_lt(v___y_7231_, v_stop_7224_);
                if v___x_7233_ == 0 {
                    crate::leanh::lean_dec(v___y_7231_);
                    crate::leanh::lean_dec(v_stop_7224_);
                    v___y_7211_ = v___y_7223_;
                    v___y_7212_ = v___y_7227_;
                    v___y_7213_ = v___y_7226_;
                    v___y_7214_ = v___y_7228_;
                    v___y_7215_ = v___y_7229_;
                    v___y_7216_ = v___y_7230_;
                    v_edits_7217_ = v_edits_7232_;
                    state = 13;
                    continue;
                } else {
                    v_source_7234_ = crate::leanh::lean_ctor_get(v___y_7225_, 0);
                    v___x_7235_ = 2;
                    v___x_7236_ =
                        lean_string_utf8_extract(v_source_7234_, v___y_7231_, v_stop_7224_);
                    crate::leanh::lean_dec(v_stop_7224_);
                    crate::leanh::lean_dec(v___y_7231_);
                    v___x_7237_ = crate::leanh::lean_box((v___x_7235_) as usize);
                    v___x_7238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7238_, 0, v___x_7237_);
                    crate::leanh::lean_ctor_set(v___x_7238_, 1, v___x_7236_);
                    v___x_7239_ = lean_array_push(v_edits_7232_, v___x_7238_);
                    v___y_7211_ = v___y_7223_;
                    v___y_7212_ = v___y_7227_;
                    v___y_7213_ = v___y_7226_;
                    v___y_7214_ = v___y_7228_;
                    v___y_7215_ = v___y_7229_;
                    v___y_7216_ = v___y_7230_;
                    v_edits_7217_ = v___x_7239_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_7244_) == 0 {
                    crate::leanh::lean_dec(v___y_7249_);
                    crate::leanh::lean_dec(v___y_7248_);
                    crate::leanh::lean_dec_ref(v___y_7241_);
                    v___y_7211_ = v___y_7242_;
                    v___y_7212_ = v___y_7243_;
                    v___y_7213_ = v___y_7244_;
                    v___y_7214_ = v___y_7245_;
                    v___y_7215_ = v___y_7246_;
                    v___y_7216_ = v___y_7247_;
                    v_edits_7217_ = v_edits_7250_;
                    state = 13;
                    continue;
                } else {
                    v_val_7252_ = crate::leanh::lean_ctor_get(v___y_7244_, 0);
                    v___x_7253_ = l_Lean_Syntax_getRange_x3f(v_val_7252_, v___y_7247_);
                    if crate::leanh::lean_obj_tag(v___x_7253_) == 1 {
                        v_val_7254_ = crate::leanh::lean_ctor_get(v___x_7253_, 0);
                        crate::leanh::lean_inc(v_val_7254_);
                        crate::leanh::lean_dec_ref_known(v___x_7253_, 1);
                        v___x_7255_ = l_Lean_Syntax_Range_includes(
                            v_val_7254_,
                            v___y_7241_,
                            v___y_7247_,
                            v___y_7247_,
                        );
                        crate::leanh::lean_dec_ref(v___y_7241_);
                        if v___x_7255_ == 0 {
                            crate::leanh::lean_dec(v_val_7254_);
                            crate::leanh::lean_dec(v___y_7249_);
                            crate::leanh::lean_dec(v___y_7248_);
                            v___y_7211_ = v___y_7242_;
                            v___y_7212_ = v___y_7243_;
                            v___y_7213_ = v___y_7244_;
                            v___y_7214_ = v___y_7245_;
                            v___y_7215_ = v___y_7246_;
                            v___y_7216_ = v___y_7247_;
                            v_edits_7217_ = v_edits_7250_;
                            state = 13;
                            continue;
                        } else {
                            v_fileMap_7256_ = crate::leanh::lean_ctor_get(v___y_7251_, 1);
                            v_start_7257_ = crate::leanh::lean_ctor_get(v_val_7254_, 0);
                            v_stop_7258_ = crate::leanh::lean_ctor_get(v_val_7254_, 1);
                            v_isSharedCheck_7274_ =
                                (!crate::leanh::lean_is_exclusive(v_val_7254_)) as u8;
                            if v_isSharedCheck_7274_ == 0 {
                                v___x_7260_ = v_val_7254_;
                                v_isShared_7261_ = v_isSharedCheck_7274_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_stop_7258_);
                                crate::leanh::lean_inc(v_start_7257_);
                                crate::leanh::lean_dec(v_val_7254_);
                                v___x_7260_ = crate::leanh::lean_box(0);
                                v_isShared_7261_ = v_isSharedCheck_7274_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7253_);
                        crate::leanh::lean_dec(v___y_7249_);
                        crate::leanh::lean_dec(v___y_7248_);
                        crate::leanh::lean_dec_ref(v___y_7241_);
                        v___y_7211_ = v___y_7242_;
                        v___y_7212_ = v___y_7243_;
                        v___y_7213_ = v___y_7244_;
                        v___y_7214_ = v___y_7245_;
                        v___y_7215_ = v___y_7246_;
                        v___y_7216_ = v___y_7247_;
                        v_edits_7217_ = v_edits_7250_;
                        state = 13;
                        continue;
                    }
                }
            }
            16 => {
                v___x_7262_ = lean_nat_dec_lt(v_start_7257_, v___y_7249_);
                if v___x_7262_ == 0 {
                    crate::leanh::lean_del_object(v___x_7260_);
                    crate::leanh::lean_dec(v_start_7257_);
                    crate::leanh::lean_dec(v___y_7249_);
                    v___y_7223_ = v___y_7242_;
                    v_stop_7224_ = v_stop_7258_;
                    v___y_7225_ = v_fileMap_7256_;
                    v___y_7226_ = v___y_7244_;
                    v___y_7227_ = v___y_7243_;
                    v___y_7228_ = v___y_7245_;
                    v___y_7229_ = v___y_7246_;
                    v___y_7230_ = v___y_7247_;
                    v___y_7231_ = v___y_7248_;
                    v_edits_7232_ = v_edits_7250_;
                    state = 14;
                    continue;
                } else {
                    v_source_7263_ = crate::leanh::lean_ctor_get(v_fileMap_7256_, 0);
                    v___x_7264_ = 2;
                    v___x_7265_ =
                        lean_string_utf8_extract(v_source_7263_, v_start_7257_, v___y_7249_);
                    crate::leanh::lean_dec(v___y_7249_);
                    crate::leanh::lean_dec(v_start_7257_);
                    v___x_7266_ = crate::leanh::lean_box((v___x_7264_) as usize);
                    if v_isShared_7261_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7260_, 1, v___x_7265_);
                        crate::leanh::lean_ctor_set(v___x_7260_, 0, v___x_7266_);
                        v___x_7268_ = v___x_7260_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_7273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 0, v___x_7266_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 1, v___x_7265_);
                        v___x_7268_ = v_reuseFailAlloc_7273_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_7269_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7270_ = lean_mk_empty_array_with_capacity(v___x_7269_);
                v___x_7271_ = lean_array_push(v___x_7270_, v___x_7268_);
                v___x_7272_ = l_Array_append___redArg(v___x_7271_, v_edits_7250_);
                crate::leanh::lean_dec_ref(v_edits_7250_);
                v___y_7223_ = v___y_7242_;
                v_stop_7224_ = v_stop_7258_;
                v___y_7225_ = v_fileMap_7256_;
                v___y_7226_ = v___y_7244_;
                v___y_7227_ = v___y_7243_;
                v___y_7228_ = v___y_7245_;
                v___y_7229_ = v___y_7246_;
                v___y_7230_ = v___y_7247_;
                v___y_7231_ = v___y_7248_;
                v_edits_7232_ = v___x_7272_;
                state = 14;
                continue;
            }
            18 => {
                crate::leanh::lean_inc_ref(v___y_7282_);
                v___x_7287_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7287_, 0, v___y_7280_);
                crate::leanh::lean_ctor_set(v___x_7287_, 1, v___y_7286_);
                crate::leanh::lean_ctor_set(v___x_7287_, 2, v___y_7282_);
                v___x_7288_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7288_, 0, v___x_7275_);
                crate::leanh::lean_ctor_set(v___x_7288_, 1, v___x_7287_);
                v___x_7289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7289_, 0, v___y_7279_);
                crate::leanh::lean_ctor_set(v___x_7289_, 1, v___x_7288_);
                v___x_7290_ = crate::leanh::lean_alloc_ctor(10, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7290_, 0, v___x_7289_);
                v___x_7291_ =
                    l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(
                        v___x_7290_,
                        v___y_7047_,
                        v___y_7048_,
                    );
                if crate::leanh::lean_obj_tag(v___x_7291_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7291_, 1);
                    v_messageData_x3f_7292_ = crate::leanh::lean_ctor_get(v___y_7282_, 4);
                    if crate::leanh::lean_obj_tag(v_messageData_x3f_7292_) == 1 {
                        v_start_7293_ = crate::leanh::lean_ctor_get(v___y_7278_, 0);
                        crate::leanh::lean_inc(v_start_7293_);
                        v_stop_7294_ = crate::leanh::lean_ctor_get(v___y_7278_, 1);
                        crate::leanh::lean_inc(v_stop_7294_);
                        v_val_7295_ = crate::leanh::lean_ctor_get(v_messageData_x3f_7292_, 0);
                        v___x_7296_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_val_7295_);
                        v___x_7297_ = l_Lean_MessageData_format(v_val_7295_, v___x_7296_);
                        v___x_7298_ = 0;
                        v___x_7299_ = l_Std_Format_defWidth;
                        v___x_7300_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7301_ =
                            l_Std_Format_pretty(v___x_7297_, v___x_7299_, v___x_7300_, v___x_7300_);
                        v___x_7302_ = crate::leanh::lean_box((v___x_7298_) as usize);
                        v___x_7303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7303_, 0, v___x_7302_);
                        crate::leanh::lean_ctor_set(v___x_7303_, 1, v___x_7301_);
                        v___x_7304_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7305_ = lean_mk_empty_array_with_capacity(v___x_7304_);
                        v___x_7306_ = lean_array_push(v___x_7305_, v___x_7303_);
                        v___y_7241_ = v___y_7278_;
                        v___y_7242_ = v___y_7277_;
                        v___y_7243_ = v___y_7282_;
                        v___y_7244_ = v___y_7281_;
                        v___y_7245_ = v___y_7283_;
                        v___y_7246_ = v___y_7284_;
                        v___y_7247_ = v___y_7285_;
                        v___y_7248_ = v_stop_7294_;
                        v___y_7249_ = v_start_7293_;
                        v_edits_7250_ = v___x_7306_;
                        v___y_7251_ = v___y_7047_;
                        state = 15;
                        continue;
                    } else {
                        v_fileMap_7307_ = crate::leanh::lean_ctor_get(v___y_7047_, 1);
                        v_start_7308_ = crate::leanh::lean_ctor_get(v___y_7278_, 0);
                        crate::leanh::lean_inc(v_start_7308_);
                        v_stop_7309_ = crate::leanh::lean_ctor_get(v___y_7278_, 1);
                        crate::leanh::lean_inc(v_stop_7309_);
                        v_source_7310_ = crate::leanh::lean_ctor_get(v_fileMap_7307_, 0);
                        v___x_7311_ =
                            lean_string_utf8_extract(v_source_7310_, v_start_7308_, v_stop_7309_);
                        crate::leanh::lean_inc_ref(v___y_7283_);
                        v___x_7312_ =
                            l_Lean_Meta_Hint_readableDiff(v___x_7311_, v___y_7283_, v___y_7284_);
                        v___y_7241_ = v___y_7278_;
                        v___y_7242_ = v___y_7277_;
                        v___y_7243_ = v___y_7282_;
                        v___y_7244_ = v___y_7281_;
                        v___y_7245_ = v___y_7283_;
                        v___y_7246_ = v___y_7284_;
                        v___y_7247_ = v___y_7285_;
                        v___y_7248_ = v_stop_7309_;
                        v___y_7249_ = v_start_7308_;
                        v_edits_7250_ = v___x_7312_;
                        v___y_7251_ = v___y_7047_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_7283_);
                    crate::leanh::lean_dec_ref(v___y_7282_);
                    crate::leanh::lean_dec(v___y_7281_);
                    crate::leanh::lean_dec_ref(v___y_7278_);
                    crate::leanh::lean_dec_ref(v___y_7277_);
                    crate::leanh::lean_dec_ref(v_b_7046_);
                    crate::leanh::lean_dec(v_ref_7042_);
                    crate::leanh::lean_dec(v_codeActionPrefix_x3f_7041_);
                    v_a_7313_ = crate::leanh::lean_ctor_get(v___x_7291_, 0);
                    v_isSharedCheck_7320_ = (!crate::leanh::lean_is_exclusive(v___x_7291_)) as u8;
                    if v_isSharedCheck_7320_ == 0 {
                        v___x_7315_ = v___x_7291_;
                        v_isShared_7316_ = v_isSharedCheck_7320_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7313_);
                        crate::leanh::lean_dec(v___x_7291_);
                        v___x_7315_ = crate::leanh::lean_box(0);
                        v_isShared_7316_ = v_isSharedCheck_7320_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_7316_ == 0 {
                    v___x_7318_ = v___x_7315_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7319_, 0, v_a_7313_);
                    v___x_7318_ = v_reuseFailAlloc_7319_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7318_;
            }
            21 => {
                v_toCodeActionTitle_x3f_7331_ = crate::leanh::lean_ctor_get(v___y_7326_, 5);
                v___x_7332_ = l_Lean_Syntax_ofRange(v___y_7330_, v___x_7095_);
                if crate::leanh::lean_obj_tag(v_toCodeActionTitle_x3f_7331_) == 0 {
                    if crate::leanh::lean_obj_tag(v_codeActionPrefix_x3f_7041_) == 0 {
                        v___x_7333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36;
                        v___x_7334_ = lean_string_append(v___x_7333_, v___y_7327_);
                        v___y_7277_ = v___y_7324_;
                        v___y_7278_ = v___y_7323_;
                        v___y_7279_ = v___x_7332_;
                        v___y_7280_ = v___y_7322_;
                        v___y_7281_ = v___y_7325_;
                        v___y_7282_ = v___y_7326_;
                        v___y_7283_ = v___y_7327_;
                        v___y_7284_ = v___y_7328_;
                        v___y_7285_ = v___y_7329_;
                        v___y_7286_ = v___x_7334_;
                        state = 18;
                        continue;
                    } else {
                        v_val_7335_ = crate::leanh::lean_ctor_get(v_codeActionPrefix_x3f_7041_, 0);
                        crate::leanh::lean_inc(v_val_7335_);
                        v___x_7336_ = lean_string_append(v_val_7335_, v___y_7327_);
                        v___y_7277_ = v___y_7324_;
                        v___y_7278_ = v___y_7323_;
                        v___y_7279_ = v___x_7332_;
                        v___y_7280_ = v___y_7322_;
                        v___y_7281_ = v___y_7325_;
                        v___y_7282_ = v___y_7326_;
                        v___y_7283_ = v___y_7327_;
                        v___y_7284_ = v___y_7328_;
                        v___y_7285_ = v___y_7329_;
                        v___y_7286_ = v___x_7336_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_val_7337_ = crate::leanh::lean_ctor_get(v_toCodeActionTitle_x3f_7331_, 0);
                    crate::leanh::lean_inc(v_val_7337_);
                    crate::leanh::lean_inc_ref(v___y_7327_);
                    v___x_7338_ = crate::leanh::lean_apply_1(v_val_7337_, v___y_7327_);
                    v___y_7277_ = v___y_7324_;
                    v___y_7278_ = v___y_7323_;
                    v___y_7279_ = v___x_7332_;
                    v___y_7280_ = v___y_7322_;
                    v___y_7281_ = v___y_7325_;
                    v___y_7282_ = v___y_7326_;
                    v___y_7283_ = v___y_7327_;
                    v___y_7284_ = v___y_7328_;
                    v___y_7285_ = v___y_7329_;
                    v___y_7286_ = v___x_7338_;
                    state = 18;
                    continue;
                }
            }
            22 => {
                v___x_7341_ = 0;
                v___x_7342_ = l_Lean_Syntax_getRange_x3f(v___y_7340_, v___x_7341_);
                crate::leanh::lean_dec(v___y_7340_);
                if crate::leanh::lean_obj_tag(v___x_7342_) == 1 {
                    v_val_7343_ = crate::leanh::lean_ctor_get(v___x_7342_, 0);
                    crate::leanh::lean_inc_n(v_val_7343_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_7342_, 1);
                    v_toTryThisSuggestion_7344_ = crate::leanh::lean_ctor_get(v_a_7097_, 0);
                    v_previewSpan_x3f_7345_ = crate::leanh::lean_ctor_get(v_a_7097_, 2);
                    v_diffGranularity_7346_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_7097_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_toTryThisSuggestion_7344_);
                    v___x_7347_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(
                        v_toTryThisSuggestion_7344_,
                        v_val_7343_,
                        v___y_7047_,
                        v___y_7048_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7347_) == 0 {
                        v_a_7348_ = crate::leanh::lean_ctor_get(v___x_7347_, 0);
                        crate::leanh::lean_inc(v_a_7348_);
                        crate::leanh::lean_dec_ref_known(v___x_7347_, 1);
                        v_range_7349_ = crate::leanh::lean_ctor_get(v_a_7348_, 0);
                        crate::leanh::lean_inc_ref(v_range_7349_);
                        v_newText_7350_ = crate::leanh::lean_ctor_get(v_a_7348_, 1);
                        crate::leanh::lean_inc_ref(v_newText_7350_);
                        v___x_7351_ = l_Lean_Syntax_getRange_x3f(v_ref_7042_, v___x_7341_);
                        if crate::leanh::lean_obj_tag(v___x_7351_) == 0 {
                            crate::leanh::lean_inc_ref(v_toTryThisSuggestion_7344_);
                            crate::leanh::lean_inc(v_previewSpan_x3f_7345_);
                            crate::leanh::lean_inc(v_val_7343_);
                            v___y_7322_ = v_a_7348_;
                            v___y_7323_ = v_val_7343_;
                            v___y_7324_ = v_range_7349_;
                            v___y_7325_ = v_previewSpan_x3f_7345_;
                            v___y_7326_ = v_toTryThisSuggestion_7344_;
                            v___y_7327_ = v_newText_7350_;
                            v___y_7328_ = v_diffGranularity_7346_;
                            v___y_7329_ = v___x_7341_;
                            v___y_7330_ = v_val_7343_;
                            state = 21;
                            continue;
                        } else {
                            v_val_7352_ = crate::leanh::lean_ctor_get(v___x_7351_, 0);
                            crate::leanh::lean_inc(v_val_7352_);
                            crate::leanh::lean_dec_ref_known(v___x_7351_, 1);
                            crate::leanh::lean_inc_ref(v_toTryThisSuggestion_7344_);
                            crate::leanh::lean_inc(v_previewSpan_x3f_7345_);
                            v___y_7322_ = v_a_7348_;
                            v___y_7323_ = v_val_7343_;
                            v___y_7324_ = v_range_7349_;
                            v___y_7325_ = v_previewSpan_x3f_7345_;
                            v___y_7326_ = v_toTryThisSuggestion_7344_;
                            v___y_7327_ = v_newText_7350_;
                            v___y_7328_ = v_diffGranularity_7346_;
                            v___y_7329_ = v___x_7341_;
                            v___y_7330_ = v_val_7352_;
                            state = 21;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_7343_);
                        crate::leanh::lean_dec_ref(v_b_7046_);
                        crate::leanh::lean_dec(v_ref_7042_);
                        crate::leanh::lean_dec(v_codeActionPrefix_x3f_7041_);
                        v_a_7353_ = crate::leanh::lean_ctor_get(v___x_7347_, 0);
                        v_isSharedCheck_7360_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7347_)) as u8;
                        if v_isSharedCheck_7360_ == 0 {
                            v___x_7355_ = v___x_7347_;
                            v_isShared_7356_ = v_isSharedCheck_7360_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7353_);
                            crate::leanh::lean_dec(v___x_7347_);
                            v___x_7355_ = crate::leanh::lean_box(0);
                            v_isShared_7356_ = v_isSharedCheck_7360_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7342_);
                    v_a_7051_ = v_b_7046_;
                    state = 1;
                    continue;
                }
            }
            23 => {
                if v_isShared_7356_ == 0 {
                    v___x_7358_ = v___x_7355_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7359_, 0, v_a_7353_);
                    v___x_7358_ = v_reuseFailAlloc_7359_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(
    mut v_suggestions_7362_: *mut crate::leanh::LeanObject,
    mut v_forceList_7363_: *mut crate::leanh::LeanObject,
    mut v_codeActionPrefix_x3f_7364_: *mut crate::leanh::LeanObject,
    mut v_ref_7365_: *mut crate::leanh::LeanObject,
    mut v_as_7366_: *mut crate::leanh::LeanObject,
    mut v_sz_7367_: *mut crate::leanh::LeanObject,
    mut v_i_7368_: *mut crate::leanh::LeanObject,
    mut v_b_7369_: *mut crate::leanh::LeanObject,
    mut v___y_7370_: *mut crate::leanh::LeanObject,
    mut v___y_7371_: *mut crate::leanh::LeanObject,
    mut v___y_7372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_forceList_boxed_7373_: u8 = 0;
    let mut v_sz_boxed_7374_: usize = 0;
    let mut v_i_boxed_7375_: usize = 0;
    let mut v_res_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_forceList_boxed_7373_ = (crate::leanh::lean_unbox(v_forceList_7363_) as u8);
    v_sz_boxed_7374_ = crate::leanh::lean_unbox_usize(v_sz_7367_);
    crate::leanh::lean_dec(v_sz_7367_);
    v_i_boxed_7375_ = crate::leanh::lean_unbox_usize(v_i_7368_);
    crate::leanh::lean_dec(v_i_7368_);
    v_res_7376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_7362_, v_forceList_boxed_7373_, v_codeActionPrefix_x3f_7364_, v_ref_7365_, v_as_7366_, v_sz_boxed_7374_, v_i_boxed_7375_, v_b_7369_, v___y_7370_, v___y_7371_);
    crate::leanh::lean_dec(v___y_7371_);
    crate::leanh::lean_dec_ref(v___y_7370_);
    crate::leanh::lean_dec_ref(v_as_7366_);
    crate::leanh::lean_dec_ref(v_suggestions_7362_);
    return v_res_7376_;
}
pub unsafe fn _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7377_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0;
    v_msg_7378_ = l_Lean_stringToMessageData(v___x_7377_);
    return v_msg_7378_;
}
pub unsafe fn l_Lean_Meta_Hint_mkSuggestionsMessage(
    mut v_suggestions_7379_: *mut crate::leanh::LeanObject,
    mut v_ref_7380_: *mut crate::leanh::LeanObject,
    mut v_codeActionPrefix_x3f_7381_: *mut crate::leanh::LeanObject,
    mut v_forceList_7382_: u8,
    mut v_a_7383_: *mut crate::leanh::LeanObject,
    mut v_a_7384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msg_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7387_: usize = 0;
    let mut v___x_7388_: usize = 0;
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_msg_7386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once),
        _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0,
    );
    v_sz_7387_ = lean_array_size(v_suggestions_7379_);
    v___x_7388_ = 0usize;
    v___x_7389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_7379_, v_forceList_7382_, v_codeActionPrefix_x3f_7381_, v_ref_7380_, v_suggestions_7379_, v_sz_7387_, v___x_7388_, v_msg_7386_, v_a_7383_, v_a_7384_);
    return v___x_7389_;
}
pub unsafe fn l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(
    mut v_suggestions_7390_: *mut crate::leanh::LeanObject,
    mut v_ref_7391_: *mut crate::leanh::LeanObject,
    mut v_codeActionPrefix_x3f_7392_: *mut crate::leanh::LeanObject,
    mut v_forceList_7393_: *mut crate::leanh::LeanObject,
    mut v_a_7394_: *mut crate::leanh::LeanObject,
    mut v_a_7395_: *mut crate::leanh::LeanObject,
    mut v_a_7396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_forceList_boxed_7397_: u8 = 0;
    let mut v_res_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_forceList_boxed_7397_ = (crate::leanh::lean_unbox(v_forceList_7393_) as u8);
    v_res_7398_ = l_Lean_Meta_Hint_mkSuggestionsMessage(
        v_suggestions_7390_,
        v_ref_7391_,
        v_codeActionPrefix_x3f_7392_,
        v_forceList_boxed_7397_,
        v_a_7394_,
        v_a_7395_,
    );
    crate::leanh::lean_dec(v_a_7395_);
    crate::leanh::lean_dec_ref(v_a_7394_);
    crate::leanh::lean_dec_ref(v_suggestions_7390_);
    return v_res_7398_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(
    mut v_t_7399_: *mut crate::leanh::LeanObject,
    mut v___y_7400_: *mut crate::leanh::LeanObject,
    mut v___y_7401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7403_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_7399_, v___y_7401_);
    return v___x_7403_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(
    mut v_t_7404_: *mut crate::leanh::LeanObject,
    mut v___y_7405_: *mut crate::leanh::LeanObject,
    mut v___y_7406_: *mut crate::leanh::LeanObject,
    mut v___y_7407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7408_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_7404_, v___y_7405_, v___y_7406_);
    crate::leanh::lean_dec(v___y_7406_);
    crate::leanh::lean_dec_ref(v___y_7405_);
    return v_res_7408_;
}
pub unsafe fn _init_l_Lean_MessageData_hint___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7413_ = l_Lean_MessageData_hint___closed__2;
    v___x_7414_ = l_Lean_stringToMessageData(v___x_7413_);
    return v___x_7414_;
}
pub unsafe fn l_Lean_MessageData_hint(
    mut v_hint_7415_: *mut crate::leanh::LeanObject,
    mut v_suggestions_7416_: *mut crate::leanh::LeanObject,
    mut v_ref_x3f_7417_: *mut crate::leanh::LeanObject,
    mut v_codeActionPrefix_x3f_7418_: *mut crate::leanh::LeanObject,
    mut v_forceList_7419_: u8,
    mut v_a_7420_: *mut crate::leanh::LeanObject,
    mut v_a_7421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7429_: u8 = 0;
    let mut v___x_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7438_: u8 = 0;
    let mut v_ref_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_ref_x3f_7417_) == 0 {
                    v_ref_7439_ = crate::leanh::lean_ctor_get(v_a_7420_, 5);
                    crate::leanh::lean_inc(v_ref_7439_);
                    v___y_7424_ = v_ref_7439_;
                    state = 1;
                    continue;
                } else {
                    v_val_7440_ = crate::leanh::lean_ctor_get(v_ref_x3f_7417_, 0);
                    crate::leanh::lean_inc(v_val_7440_);
                    crate::leanh::lean_dec_ref_known(v_ref_x3f_7417_, 1);
                    v___y_7424_ = v_val_7440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7425_ = l_Lean_Meta_Hint_mkSuggestionsMessage(
                    v_suggestions_7416_,
                    v___y_7424_,
                    v_codeActionPrefix_x3f_7418_,
                    v_forceList_7419_,
                    v_a_7420_,
                    v_a_7421_,
                );
                if crate::leanh::lean_obj_tag(v___x_7425_) == 0 {
                    v_a_7426_ = crate::leanh::lean_ctor_get(v___x_7425_, 0);
                    v_isSharedCheck_7438_ = (!crate::leanh::lean_is_exclusive(v___x_7425_)) as u8;
                    if v_isSharedCheck_7438_ == 0 {
                        v___x_7428_ = v___x_7425_;
                        v_isShared_7429_ = v_isSharedCheck_7438_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7426_);
                        crate::leanh::lean_dec(v___x_7425_);
                        v___x_7428_ = crate::leanh::lean_box(0);
                        v_isShared_7429_ = v_isSharedCheck_7438_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_hint_7415_);
                    return v___x_7425_;
                }
            }
            2 => {
                v___x_7430_ = l_Lean_MessageData_hint___closed__1;
                v___x_7431_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MessageData_hint___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MessageData_hint___closed__3_once),
                    _init_l_Lean_MessageData_hint___closed__3,
                );
                v___x_7432_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7432_, 0, v___x_7431_);
                crate::leanh::lean_ctor_set(v___x_7432_, 1, v_hint_7415_);
                v___x_7433_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7433_, 0, v___x_7432_);
                crate::leanh::lean_ctor_set(v___x_7433_, 1, v_a_7426_);
                v___x_7434_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7434_, 0, v___x_7430_);
                crate::leanh::lean_ctor_set(v___x_7434_, 1, v___x_7433_);
                if v_isShared_7429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7428_, 0, v___x_7434_);
                    v___x_7436_ = v___x_7428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 0, v___x_7434_);
                    v___x_7436_ = v_reuseFailAlloc_7437_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MessageData_hint___boxed(
    mut v_hint_7441_: *mut crate::leanh::LeanObject,
    mut v_suggestions_7442_: *mut crate::leanh::LeanObject,
    mut v_ref_x3f_7443_: *mut crate::leanh::LeanObject,
    mut v_codeActionPrefix_x3f_7444_: *mut crate::leanh::LeanObject,
    mut v_forceList_7445_: *mut crate::leanh::LeanObject,
    mut v_a_7446_: *mut crate::leanh::LeanObject,
    mut v_a_7447_: *mut crate::leanh::LeanObject,
    mut v_a_7448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_forceList_boxed_7449_: u8 = 0;
    let mut v_res_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_forceList_boxed_7449_ = (crate::leanh::lean_unbox(v_forceList_7445_) as u8);
    v_res_7450_ = l_Lean_MessageData_hint(
        v_hint_7441_,
        v_suggestions_7442_,
        v_ref_x3f_7443_,
        v_codeActionPrefix_x3f_7444_,
        v_forceList_boxed_7449_,
        v_a_7446_,
        v_a_7447_,
    );
    crate::leanh::lean_dec(v_a_7447_);
    crate::leanh::lean_dec_ref(v_a_7446_);
    crate::leanh::lean_dec_ref(v_suggestions_7442_);
    return v_res_7450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Hint(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Diff(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Hint_textInsertionWidget = _init_l_Lean_Meta_Hint_textInsertionWidget();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Hint_textInsertionWidget);
    l_Lean_Meta_Hint_tryThisDiffWidget = _init_l_Lean_Meta_Hint_tryThisDiffWidget();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Hint_tryThisDiffWidget);
    l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1 = _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1);
    l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1 = _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1);
    l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1 = _init_l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Hint(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Hint(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Diff(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Hint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Hint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Hint(builtin);
}
