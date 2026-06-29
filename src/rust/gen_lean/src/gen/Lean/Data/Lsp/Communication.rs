// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: Lean.Data.JsonRpc Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.Iterators.Consumers.Collect
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prevn, l_String_Slice_posGE___redArg,
};
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_beq, l_String_Slice_intercalate, l_String_Slice_toNat_x3f,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjVal_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromInt,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_Structured_toJson, l_Lean_Json_toStructured_x3f___redArg,
};
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Json::Stream::l_IO_FS_Stream_readUTF8;
use crate::r#gen::Lean::Data::JsonRpc::{
    initialize_Lean_Data_JsonRpc, l_IO_FS_Stream_readMessage,
    l_IO_FS_Stream_readNotificationAs___redArg, l_IO_FS_Stream_readRequestAs___redArg,
    l_IO_FS_Stream_readResponseAs___redArg, runtime_initialize_Lean_Data_JsonRpc,
};
use crate::ffi::{lean_int_neg, lean_nat_to_int};
use crate::ffi::{
    lean_string_utf8_extract, lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_get_byte_fast;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint8_dec_eq,
};
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2: u8 = 0;
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [13, 10, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 101, 113, 95, 110, 117, 109, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 104, 101, 97, 100, 101, 114, 32, 102, 105, 101, 108, 100, 58, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value: crate::leanh::LeanStringObject<176> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 176, m_capacity: 176, m_length: 175, m_data: [65, 32, 76, 101, 97, 110, 32, 51, 32, 114, 101, 113, 117, 101, 115, 116, 32, 119, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 46, 32, 80, 108, 101, 97, 115, 101, 32, 101, 110, 115, 117, 114, 101, 32, 116, 104, 97, 116, 32, 121, 111, 117, 114, 32, 101, 100, 105, 116, 111, 114, 32, 104, 97, 115, 32, 97, 32, 76, 101, 97, 110, 32, 52, 32, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 105, 110, 115, 116, 97, 108, 108, 101, 100, 46, 32, 70, 111, 114, 32, 86, 83, 67, 111, 100, 101, 44, 32, 116, 104, 105, 115, 32, 105, 115, 10, 10, 32, 32, 32, 32, 104, 116, 116, 112, 115, 58, 47, 47, 103, 105, 116, 104, 117, 98, 46, 99, 111, 109, 47, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 118, 115, 99, 111, 100, 101, 45, 108, 101, 97, 110, 52, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 116, 114, 101, 97, 109, 32, 119, 97, 115, 32, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [78, 111, 32, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 32, 102, 105, 101, 108, 100, 32, 105, 110, 32, 104, 101, 97, 100, 101, 114, 58, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 32, 104, 101, 97, 100, 101, 114, 32, 102, 105, 101, 108, 100, 32, 118, 97, 108, 117, 101, 32, 39, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [39, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 78, 97, 116, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_readLspMessage___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            67, 97, 110, 110, 111, 116, 32, 114, 101, 97, 100, 32, 76, 83, 80, 32, 109, 101, 115,
            115, 97, 103, 101, 58, 32, 0,
        ],
    };
static mut l_IO_FS_Stream_readLspMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 114, 101, 97, 100, 32, 76, 83, 80, 32, 114, 101, 113, 117,
        101, 115, 116, 58, 32, 0,
    ],
};
static mut l_IO_FS_Stream_readLspRequestAs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value:
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
        67, 97, 110, 110, 111, 116, 32, 114, 101, 97, 100, 32, 76, 83, 80, 32, 110, 111, 116, 105,
        102, 105, 99, 97, 116, 105, 111, 110, 58, 32, 0,
    ],
};
static mut l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 114, 101, 97, 100, 32, 76, 83, 80, 32, 114, 101, 115, 112,
        111, 110, 115, 101, 58, 32, 0,
    ],
};
static mut l_IO_FS_Stream_readLspResponseAs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value:
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
        67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 0,
    ],
};
static mut l_IO_FS_Stream_writeSerializedLspMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [13, 10, 13, 10, 0],
};
static mut l_IO_FS_Stream_writeSerializedLspMessage___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [106, 115, 111, 110, 114, 112, 99, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [50, 46, 48, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 100, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__5_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 101, 116, 104, 111, 100, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__6_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [112, 97, 114, 97, 109, 115, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__7_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [114, 101, 115, 117, 108, 116, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__8_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [109, 101, 115, 115, 97, 103, 101, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__9_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 97, 116, 97, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [101, 114, 114, 111, 114, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__11_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 111, 100, 101, 0],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_IO_FS_Stream_writeLspMessage___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__43_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__49_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__52_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__53_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__54_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__55_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__57_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__59_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
    v___x_1056_ = lean_string_utf8_byte_size(v___x_1055_);
    return v___x_1056_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2()
-> u8 {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
    v___x_1057_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
    v___x_1059_ = lean_nat_dec_eq(v___x_1058_, v___x_1057_);
    return v___x_1059_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
    v___x_1061_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1062_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
    v___x_1063_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1063_, 0, v___x_1062_);
    crate::leanh::lean_ctor_set(v___x_1063_, 1, v___x_1061_);
    crate::leanh::lean_ctor_set(v___x_1063_, 2, v___x_1060_);
    return v___x_1063_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
    v___x_1065_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4);
    v___x_1068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
    v___x_1069_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    crate::leanh::lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    crate::leanh::lean_ctor_set(v___x_1069_, 2, v___x_1066_);
    crate::leanh::lean_ctor_set(v___x_1069_, 3, v___x_1066_);
    return v___x_1069_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5);
    v___x_1071_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
    crate::leanh::lean_ctor_set(v___x_1072_, 1, v___x_1070_);
    return v___x_1072_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(
    mut v_s_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: u8 = 0;
    v___x_1079_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2);
    if v___x_1079_ == 0 {
        let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1080_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6);
        return v___x_1080_;
    } else {
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1081_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8;
        return v___x_1081_;
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(
    mut v_s_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v_s_1082_);
    crate::leanh::lean_dec_ref(v_s_1082_);
    return v_res_1083_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(
    mut v_s_1084_: *mut crate::leanh::LeanObject,
    mut v___x_1085_: *mut crate::leanh::LeanObject,
    mut v___x_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_b_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v_it_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v_nextIt_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1126_: u8 = 0;
    let mut v_startInclusive_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v_pos_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1144_: u8 = 0;
    let mut v_needle_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v_str_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1161_: u8 = 0;
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1087_) == 0 {
                    v_currPos_1096_ = crate::leanh::lean_ctor_get(v_a_1087_, 0);
                    v_searcher_1097_ = crate::leanh::lean_ctor_get(v_a_1087_, 1);
                    v_isSharedCheck_1201_ = (!crate::leanh::lean_is_exclusive(v_a_1087_)) as u8;
                    if v_isSharedCheck_1201_ == 0 {
                        v___x_1099_ = v_a_1087_;
                        v_isShared_1100_ = v_isSharedCheck_1201_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1097_);
                        crate::leanh::lean_inc(v_currPos_1096_);
                        crate::leanh::lean_dec(v_a_1087_);
                        v___x_1099_ = crate::leanh::lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1201_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1086_);
                    crate::leanh::lean_dec_ref(v_s_1084_);
                    return v_b_1088_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_1084_);
                v___x_1093_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1093_, 0, v_s_1084_);
                crate::leanh::lean_ctor_set(v___x_1093_, 1, v_startInclusive_1091_);
                crate::leanh::lean_ctor_set(v___x_1093_, 2, v_endExclusive_1092_);
                v___x_1094_ = lean_array_push(v_b_1088_, v___x_1093_);
                v_a_1087_ = v_it_1090_;
                v_b_1088_ = v___x_1094_;
                state = 0;
                continue;
            }
            2 => match crate::leanh::lean_obj_tag(v_searcher_1097_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_1099_);
                    v_pos_1123_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_isSharedCheck_1135_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1135_ == 0 {
                        v___x_1125_ = v_searcher_1097_;
                        v_isShared_1126_ = v_isSharedCheck_1135_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1123_);
                        crate::leanh::lean_dec(v_searcher_1097_);
                        v___x_1125_ = crate::leanh::lean_box(0);
                        v_isShared_1126_ = v_isSharedCheck_1135_;
                        state = 9;
                        continue;
                    }
                }
                1 => {
                    v_pos_1136_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_isSharedCheck_1144_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1144_ == 0 {
                        v___x_1138_ = v_searcher_1097_;
                        v_isShared_1139_ = v_isSharedCheck_1144_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1136_);
                        crate::leanh::lean_dec(v_searcher_1097_);
                        v___x_1138_ = crate::leanh::lean_box(0);
                        v_isShared_1139_ = v_isSharedCheck_1144_;
                        state = 11;
                        continue;
                    }
                }
                2 => {
                    v_needle_1145_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_table_1146_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 1);
                    v_stackPos_1147_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 2);
                    v_needlePos_1148_ = crate::leanh::lean_ctor_get(v_searcher_1097_, 3);
                    v_isSharedCheck_1200_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1200_ == 0 {
                        v___x_1150_ = v_searcher_1097_;
                        v_isShared_1151_ = v_isSharedCheck_1200_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_needlePos_1148_);
                        crate::leanh::lean_inc(v_stackPos_1147_);
                        crate::leanh::lean_inc(v_table_1146_);
                        crate::leanh::lean_inc(v_needle_1145_);
                        crate::leanh::lean_dec(v_searcher_1097_);
                        v___x_1150_ = crate::leanh::lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1200_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_1099_);
                    state = 8;
                    continue;
                }
            },
            3 => {
                if v_isShared_1100_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1099_, 1, v_it_1102_);
                    v___x_1104_ = v___x_1099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_currPos_1096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_it_1102_);
                    v___x_1104_ = v_reuseFailAlloc_1106_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1087_ = v___x_1104_;
                state = 0;
                continue;
            }
            5 => {
                v_slice_1111_ =
                    l_String_Slice_subslice_x21(v___x_1085_, v_currPos_1096_, v_startPos_1109_);
                v_startInclusive_1112_ = crate::leanh::lean_ctor_get(v_slice_1111_, 0);
                v_endExclusive_1113_ = crate::leanh::lean_ctor_get(v_slice_1111_, 1);
                v_isSharedCheck_1120_ = (!crate::leanh::lean_is_exclusive(v_slice_1111_)) as u8;
                if v_isSharedCheck_1120_ == 0 {
                    v___x_1115_ = v_slice_1111_;
                    v_isShared_1116_ = v_isSharedCheck_1120_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_1113_);
                    crate::leanh::lean_inc(v_startInclusive_1112_);
                    crate::leanh::lean_dec(v_slice_1111_);
                    v___x_1115_ = crate::leanh::lean_box(0);
                    v_isShared_1116_ = v_isSharedCheck_1120_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1115_, 1, v_it_1108_);
                    crate::leanh::lean_ctor_set(v___x_1115_, 0, v_endPos_1110_);
                    v_nextIt_1118_ = v___x_1115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_endPos_1110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_it_1108_);
                    v_nextIt_1118_ = v_reuseFailAlloc_1119_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_it_1090_ = v_nextIt_1118_;
                v_startInclusive_1091_ = v_startInclusive_1112_;
                v_endExclusive_1092_ = v_endExclusive_1113_;
                state = 1;
                continue;
            }
            8 => {
                v___x_1122_ = crate::leanh::lean_box(1);
                crate::leanh::lean_inc(v___x_1086_);
                v_it_1090_ = v___x_1122_;
                v_startInclusive_1091_ = v_currPos_1096_;
                v_endExclusive_1092_ = v___x_1086_;
                state = 1;
                continue;
            }
            9 => {
                v_startInclusive_1127_ = crate::leanh::lean_ctor_get(v___x_1085_, 1);
                v_endExclusive_1128_ = crate::leanh::lean_ctor_get(v___x_1085_, 2);
                v___x_1129_ = lean_nat_sub(v_endExclusive_1128_, v_startInclusive_1127_);
                v___x_1130_ = lean_nat_dec_eq(v_pos_1123_, v___x_1129_);
                crate::leanh::lean_dec(v___x_1129_);
                if v___x_1130_ == 0 {
                    crate::leanh::lean_inc(v_pos_1123_);
                    if v_isShared_1126_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1125_, 1);
                        v___x_1132_ = v___x_1125_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_pos_1123_);
                        v___x_1132_ = v_reuseFailAlloc_1133_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1125_);
                    v___x_1134_ = crate::leanh::lean_box(3);
                    crate::leanh::lean_inc(v_pos_1123_);
                    v_it_1108_ = v___x_1134_;
                    v_startPos_1109_ = v_pos_1123_;
                    v_endPos_1110_ = v_pos_1123_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc(v_pos_1123_);
                v_it_1108_ = v___x_1132_;
                v_startPos_1109_ = v_pos_1123_;
                v_endPos_1110_ = v_pos_1123_;
                state = 5;
                continue;
            }
            11 => {
                v___x_1140_ = lean_string_utf8_next_fast(v_s_1084_, v_pos_1136_);
                crate::leanh::lean_dec(v_pos_1136_);
                if v_isShared_1139_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1138_, 0);
                    crate::leanh::lean_ctor_set(v___x_1138_, 0, v___x_1140_);
                    v___x_1142_ = v___x_1138_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
                    v___x_1142_ = v_reuseFailAlloc_1143_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_it_1102_ = v___x_1142_;
                state = 3;
                continue;
            }
            13 => {
                v_str_1152_ = crate::leanh::lean_ctor_get(v_needle_1145_, 0);
                v_startInclusive_1153_ = crate::leanh::lean_ctor_get(v_needle_1145_, 1);
                v_endExclusive_1154_ = crate::leanh::lean_ctor_get(v_needle_1145_, 2);
                v_basePos_1155_ = lean_nat_sub(v_stackPos_1147_, v_needlePos_1148_);
                v___x_1156_ = lean_nat_sub(v_endExclusive_1154_, v_startInclusive_1153_);
                v___x_1157_ = lean_nat_add(v_basePos_1155_, v___x_1156_);
                v___x_1158_ = lean_nat_dec_le(v___x_1157_, v___x_1086_);
                crate::leanh::lean_dec(v___x_1157_);
                if v___x_1158_ == 0 {
                    crate::leanh::lean_dec(v___x_1156_);
                    crate::leanh::lean_del_object(v___x_1150_);
                    crate::leanh::lean_dec(v_needlePos_1148_);
                    crate::leanh::lean_dec(v_stackPos_1147_);
                    crate::leanh::lean_dec_ref(v_table_1146_);
                    crate::leanh::lean_dec_ref(v_needle_1145_);
                    v___x_1159_ = lean_nat_dec_lt(v_basePos_1155_, v___x_1086_);
                    crate::leanh::lean_dec(v_basePos_1155_);
                    if v___x_1159_ == 0 {
                        crate::leanh::lean_del_object(v___x_1099_);
                        state = 8;
                        continue;
                    } else {
                        v___x_1160_ = crate::leanh::lean_box(3);
                        v_it_1102_ = v___x_1160_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_basePos_1155_);
                    crate::leanh::lean_inc(v_stackPos_1147_);
                    v_stackByte_1161_ = lean_string_get_byte_fast(v_s_1084_, v_stackPos_1147_);
                    v___x_1162_ = lean_nat_add(v_startInclusive_1153_, v_needlePos_1148_);
                    v_patByte_1163_ = lean_string_get_byte_fast(v_str_1152_, v___x_1162_);
                    v___x_1164_ = lean_uint8_dec_eq(v_stackByte_1161_, v_patByte_1163_);
                    if v___x_1164_ == 0 {
                        crate::leanh::lean_dec(v___x_1156_);
                        v___x_1165_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1166_ = lean_nat_dec_eq(v_needlePos_1148_, v___x_1165_);
                        if v___x_1166_ == 0 {
                            v___x_1167_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1168_ = lean_nat_sub(v_needlePos_1148_, v___x_1167_);
                            crate::leanh::lean_dec(v_needlePos_1148_);
                            v_newNeedlePos_1169_ =
                                lean_array_fget_borrowed(v_table_1146_, v___x_1168_);
                            crate::leanh::lean_dec(v___x_1168_);
                            v___x_1170_ = lean_nat_dec_eq(v_newNeedlePos_1169_, v___x_1165_);
                            if v___x_1170_ == 0 {
                                crate::leanh::lean_inc(v_newNeedlePos_1169_);
                                if v_isShared_1151_ == 0 {
                                    crate::leanh::lean_ctor_set(
                                        v___x_1150_,
                                        3,
                                        v_newNeedlePos_1169_,
                                    );
                                    v___x_1172_ = v___x_1150_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1173_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        0,
                                        v_needle_1145_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        1,
                                        v_table_1146_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        2,
                                        v_stackPos_1147_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        3,
                                        v_newNeedlePos_1169_,
                                    );
                                    v___x_1172_ = v_reuseFailAlloc_1173_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1174_ =
                                    l_String_Slice_posGE___redArg(v___x_1085_, v_stackPos_1147_);
                                if v_isShared_1151_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1150_, 3, v___x_1165_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_1150_,
                                        2,
                                        v_nextStackPos_1174_,
                                    );
                                    v___x_1176_ = v___x_1150_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1177_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        0,
                                        v_needle_1145_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        1,
                                        v_table_1146_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        2,
                                        v_nextStackPos_1174_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        3,
                                        v___x_1165_,
                                    );
                                    v___x_1176_ = v_reuseFailAlloc_1177_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_needlePos_1148_);
                            v___x_1178_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1179_ = lean_nat_add(v_stackPos_1147_, v___x_1178_);
                            crate::leanh::lean_dec(v_stackPos_1147_);
                            v_nextStackPos_1180_ =
                                l_String_Slice_posGE___redArg(v___x_1085_, v___x_1179_);
                            if v_isShared_1151_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1150_, 3, v___x_1165_);
                                crate::leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1180_);
                                v___x_1182_ = v___x_1150_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1183_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    0,
                                    v_needle_1145_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    1,
                                    v_table_1146_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    2,
                                    v_nextStackPos_1180_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___x_1165_);
                                v___x_1182_ = v_reuseFailAlloc_1183_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1099_);
                        v___x_1184_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1185_ = lean_nat_add(v_stackPos_1147_, v___x_1184_);
                        crate::leanh::lean_dec(v_stackPos_1147_);
                        v_nextNeedlePos_1186_ = lean_nat_add(v_needlePos_1148_, v___x_1184_);
                        crate::leanh::lean_dec(v_needlePos_1148_);
                        v___x_1187_ = lean_nat_dec_eq(v_nextNeedlePos_1186_, v___x_1156_);
                        crate::leanh::lean_dec(v___x_1156_);
                        if v___x_1187_ == 0 {
                            if v_isShared_1151_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1150_, 3, v_nextNeedlePos_1186_);
                                crate::leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1185_);
                                v___x_1189_ = v___x_1150_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_1192_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    0,
                                    v_needle_1145_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    1,
                                    v_table_1146_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    2,
                                    v_nextStackPos_1185_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    3,
                                    v_nextNeedlePos_1186_,
                                );
                                v___x_1189_ = v_reuseFailAlloc_1192_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_1193_ = lean_nat_sub(v_nextStackPos_1185_, v_nextNeedlePos_1186_);
                            crate::leanh::lean_dec(v_nextNeedlePos_1186_);
                            v___x_1194_ = l_String_Slice_pos_x21(v___x_1085_, v___x_1193_);
                            crate::leanh::lean_dec(v___x_1193_);
                            v___x_1195_ = l_String_Slice_pos_x21(v___x_1085_, v_nextStackPos_1185_);
                            v___x_1196_ = crate::leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1151_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1150_, 3, v___x_1196_);
                                crate::leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1185_);
                                v___x_1198_ = v___x_1150_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_1199_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    0,
                                    v_needle_1145_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    1,
                                    v_table_1146_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    2,
                                    v_nextStackPos_1185_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 3, v___x_1196_);
                                v___x_1198_ = v_reuseFailAlloc_1199_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v_it_1102_ = v___x_1172_;
                state = 3;
                continue;
            }
            15 => {
                v_it_1102_ = v___x_1176_;
                state = 3;
                continue;
            }
            16 => {
                v_it_1102_ = v___x_1182_;
                state = 3;
                continue;
            }
            17 => {
                v___x_1190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1190_, 0, v_currPos_1096_);
                crate::leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v_a_1087_ = v___x_1190_;
                state = 0;
                continue;
            }
            18 => {
                v_it_1108_ = v___x_1198_;
                v_startPos_1109_ = v___x_1194_;
                v_endPos_1110_ = v___x_1195_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(
    mut v_s_1202_: *mut crate::leanh::LeanObject,
    mut v___x_1203_: *mut crate::leanh::LeanObject,
    mut v___x_1204_: *mut crate::leanh::LeanObject,
    mut v_a_1205_: *mut crate::leanh::LeanObject,
    mut v_b_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1202_, v___x_1203_, v___x_1204_, v_a_1205_, v_b_1206_);
    crate::leanh::lean_dec_ref(v___x_1203_);
    return v_res_1207_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
    v___x_1211_ = lean_string_utf8_byte_size(v___x_1210_);
    return v___x_1211_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
    v___x_1213_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1214_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
    v___x_1215_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
    crate::leanh::lean_ctor_set(v___x_1215_, 1, v___x_1213_);
    crate::leanh::lean_ctor_set(v___x_1215_, 2, v___x_1212_);
    return v___x_1215_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(
    mut v_s_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_unused_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1219_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
                v___x_1220_ = lean_string_dec_eq(v_s_1218_, v___x_1219_);
                if v___x_1220_ == 0 {
                    v___x_1221_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1222_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1223_ = lean_string_utf8_byte_size(v_s_1218_);
                    crate::leanh::lean_inc_ref_n(v_s_1218_, 2);
                    v___x_1224_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1224_, 0, v_s_1218_);
                    crate::leanh::lean_ctor_set(v___x_1224_, 1, v___x_1222_);
                    crate::leanh::lean_ctor_set(v___x_1224_, 2, v___x_1223_);
                    v___x_1225_ = l_String_Slice_Pos_prevn(v___x_1224_, v___x_1223_, v___x_1221_);
                    crate::leanh::lean_dec_ref_known(v___x_1224_, 3);
                    crate::leanh::lean_inc(v___x_1225_);
                    v___x_1226_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v_s_1218_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 2, v___x_1223_);
                    v___x_1227_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
                    v___x_1228_ = l_String_Slice_beq(v___x_1226_, v___x_1227_);
                    crate::leanh::lean_dec_ref_known(v___x_1226_, 3);
                    if v___x_1228_ == 0 {
                        crate::leanh::lean_dec(v___x_1225_);
                        crate::leanh::lean_dec_ref(v_s_1218_);
                        v___x_1229_ = crate::leanh::lean_box(0);
                        return v___x_1229_;
                    } else {
                        crate::leanh::lean_inc(v___x_1225_);
                        crate::leanh::lean_inc_ref(v_s_1218_);
                        v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1230_, 0, v_s_1218_);
                        crate::leanh::lean_ctor_set(v___x_1230_, 1, v___x_1222_);
                        crate::leanh::lean_ctor_set(v___x_1230_, 2, v___x_1225_);
                        v___x_1231_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v___x_1230_);
                        v___x_1232_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
                        v___x_1233_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1218_, v___x_1230_, v___x_1225_, v___x_1231_, v___x_1232_);
                        crate::leanh::lean_dec_ref_known(v___x_1230_, 3);
                        v___x_1234_ = lean_array_to_list(v___x_1233_);
                        if crate::leanh::lean_obj_tag(v___x_1234_) == 0 {
                            v___x_1235_ = crate::leanh::lean_box(0);
                            return v___x_1235_;
                        } else {
                            v_tail_1236_ = crate::leanh::lean_ctor_get(v___x_1234_, 1);
                            crate::leanh::lean_inc(v_tail_1236_);
                            if crate::leanh::lean_obj_tag(v_tail_1236_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1234_, 2);
                                v___x_1237_ = crate::leanh::lean_box(0);
                                return v___x_1237_;
                            } else {
                                v_head_1238_ = crate::leanh::lean_ctor_get(v___x_1234_, 0);
                                crate::leanh::lean_inc(v_head_1238_);
                                crate::leanh::lean_dec_ref_known(v___x_1234_, 2);
                                v_str_1239_ = crate::leanh::lean_ctor_get(v_head_1238_, 0);
                                crate::leanh::lean_inc_ref(v_str_1239_);
                                v_startInclusive_1240_ =
                                    crate::leanh::lean_ctor_get(v_head_1238_, 1);
                                crate::leanh::lean_inc(v_startInclusive_1240_);
                                v_endExclusive_1241_ = crate::leanh::lean_ctor_get(v_head_1238_, 2);
                                crate::leanh::lean_inc(v_endExclusive_1241_);
                                crate::leanh::lean_dec(v_head_1238_);
                                v___x_1242_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
                                v___x_1243_ = l_String_Slice_intercalate(v___x_1242_, v_tail_1236_);
                                v_isSharedCheck_1252_ =
                                    (!crate::leanh::lean_is_exclusive(v_tail_1236_)) as u8;
                                if v_isSharedCheck_1252_ == 0 {
                                    v_unused_1253_ = crate::leanh::lean_ctor_get(v_tail_1236_, 1);
                                    crate::leanh::lean_dec(v_unused_1253_);
                                    v_unused_1254_ = crate::leanh::lean_ctor_get(v_tail_1236_, 0);
                                    crate::leanh::lean_dec(v_unused_1254_);
                                    v___x_1245_ = v_tail_1236_;
                                    v_isShared_1246_ = v_isSharedCheck_1252_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_tail_1236_);
                                    v___x_1245_ = crate::leanh::lean_box(0);
                                    v_isShared_1246_ = v_isSharedCheck_1252_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_1218_);
                    v___x_1255_ = crate::leanh::lean_box(0);
                    return v___x_1255_;
                }
            }
            1 => {
                v___x_1247_ = lean_string_utf8_extract(
                    v_str_1239_,
                    v_startInclusive_1240_,
                    v_endExclusive_1241_,
                );
                crate::leanh::lean_dec(v_endExclusive_1241_);
                crate::leanh::lean_dec(v_startInclusive_1240_);
                crate::leanh::lean_dec_ref(v_str_1239_);
                if v_isShared_1246_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1245_, 0);
                    crate::leanh::lean_ctor_set(v___x_1245_, 1, v___x_1243_);
                    crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1243_);
                    v___x_1249_ = v_reuseFailAlloc_1251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(
    mut v_s_1256_: *mut crate::leanh::LeanObject,
    mut v___x_1257_: *mut crate::leanh::LeanObject,
    mut v___x_1258_: *mut crate::leanh::LeanObject,
    mut v_inst_1259_: *mut crate::leanh::LeanObject,
    mut v_R_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_b_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1256_, v___x_1257_, v___x_1258_, v_a_1261_, v_b_1262_);
    return v___x_1263_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(
    mut v_s_1264_: *mut crate::leanh::LeanObject,
    mut v___x_1265_: *mut crate::leanh::LeanObject,
    mut v___x_1266_: *mut crate::leanh::LeanObject,
    mut v_inst_1267_: *mut crate::leanh::LeanObject,
    mut v_R_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_b_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(v_s_1264_, v___x_1265_, v___x_1266_, v_inst_1267_, v_R_1268_, v_a_1269_, v_b_1270_);
    crate::leanh::lean_dec_ref(v___x_1265_);
    return v_res_1271_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(
    mut v_s_1274_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Json_parse(v_s_1274_);
    if crate::leanh::lean_obj_tag(v___x_1275_) == 0 {
        let mut v___x_1276_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_1275_, 1);
        v___x_1276_ = 0;
        return v___x_1276_;
    } else {
        let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1277_ = crate::leanh::lean_ctor_get(v___x_1275_, 0);
        crate::leanh::lean_inc_n(v_a_1277_, 2);
        crate::leanh::lean_dec_ref_known(v___x_1275_, 1);
        v___x_1278_ =
            l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
        v___x_1279_ = l_Lean_Json_getObjVal_x3f(v_a_1277_, v___x_1278_);
        if crate::leanh::lean_obj_tag(v___x_1279_) == 0 {
            let mut v___x_1280_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v___x_1279_, 1);
            crate::leanh::lean_dec(v_a_1277_);
            v___x_1280_ = 0;
            return v___x_1280_;
        } else {
            let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1279_, 1);
            v___x_1281_ =
                l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
            v___x_1282_ = l_Lean_Json_getObjVal_x3f(v_a_1277_, v___x_1281_);
            if crate::leanh::lean_obj_tag(v___x_1282_) == 0 {
                let mut v___x_1283_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v___x_1282_, 1);
                v___x_1283_ = 0;
                return v___x_1283_;
            } else {
                let mut v___x_1284_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v___x_1282_, 1);
                v___x_1284_ = 1;
                return v___x_1284_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(
    mut v_s_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1286_: u8 = 0;
    let mut v_r_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_s_1285_);
    v_r_1287_ = crate::leanh::lean_box((v_res_1286_) as usize);
    return v_r_1287_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
    v___x_1291_ = lean_mk_io_user_error(v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3;
    v___x_1294_ = lean_mk_io_user_error(v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(
    mut v_h_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getLine_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getLine_1297_ = crate::leanh::lean_ctor_get(v_h_1295_, 3);
                crate::leanh::lean_inc_ref(v_getLine_1297_);
                v___x_1298_ =
                    crate::leanh::lean_apply_1(v_getLine_1297_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1298_) == 0 {
                    v_a_1299_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                    v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v___x_1298_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1301_ = v___x_1298_;
                        v_isShared_1302_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1299_);
                        crate::leanh::lean_dec(v___x_1298_);
                        v___x_1301_ = crate::leanh::lean_box(0);
                        v_isShared_1302_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_1295_);
                    v_a_1344_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                    v_isSharedCheck_1351_ = (!crate::leanh::lean_is_exclusive(v___x_1298_)) as u8;
                    if v_isSharedCheck_1351_ == 0 {
                        v___x_1346_ = v___x_1298_;
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1344_);
                        crate::leanh::lean_dec(v___x_1298_);
                        v___x_1346_ = crate::leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1303_ = lean_string_utf8_byte_size(v_a_1299_);
                v___x_1304_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1305_ = lean_nat_dec_eq(v___x_1303_, v___x_1304_);
                if v___x_1305_ == 0 {
                    v___x_1306_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
                    v___x_1307_ = lean_string_dec_eq(v_a_1299_, v___x_1306_);
                    if v___x_1307_ == 0 {
                        crate::leanh::lean_inc(v_a_1299_);
                        v___x_1308_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(v_a_1299_);
                        if crate::leanh::lean_obj_tag(v___x_1308_) == 0 {
                            crate::leanh::lean_dec_ref(v_h_1295_);
                            crate::leanh::lean_inc(v_a_1299_);
                            v___x_1309_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_a_1299_);
                            if v___x_1309_ == 0 {
                                v___x_1310_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
                                v___x_1311_ = l_String_quote(v_a_1299_);
                                v___x_1312_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
                                v___x_1313_ = l_Std_Format_defWidth;
                                v___x_1314_ = l_Std_Format_pretty(
                                    v___x_1312_,
                                    v___x_1313_,
                                    v___x_1304_,
                                    v___x_1304_,
                                );
                                v___x_1315_ = lean_string_append(v___x_1310_, v___x_1314_);
                                crate::leanh::lean_dec_ref(v___x_1314_);
                                v___x_1316_ = lean_mk_io_user_error(v___x_1315_);
                                if v_isShared_1302_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1301_, 1);
                                    crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1316_);
                                    v___x_1318_ = v___x_1301_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1319_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1319_,
                                        0,
                                        v___x_1316_,
                                    );
                                    v___x_1318_ = v_reuseFailAlloc_1319_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1299_);
                                v___x_1320_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
                                if v_isShared_1302_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1301_, 1);
                                    crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1320_);
                                    v___x_1322_ = v___x_1301_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1323_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1323_,
                                        0,
                                        v___x_1320_,
                                    );
                                    v___x_1322_ = v_reuseFailAlloc_1323_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1301_);
                            crate::leanh::lean_dec(v_a_1299_);
                            v_val_1324_ = crate::leanh::lean_ctor_get(v___x_1308_, 0);
                            crate::leanh::lean_inc(v_val_1324_);
                            crate::leanh::lean_dec_ref_known(v___x_1308_, 1);
                            v___x_1325_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_1295_);
                            if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                                v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                                v_isSharedCheck_1334_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1325_)) as u8;
                                if v_isSharedCheck_1334_ == 0 {
                                    v___x_1328_ = v___x_1325_;
                                    v_isShared_1329_ = v_isSharedCheck_1334_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1326_);
                                    crate::leanh::lean_dec(v___x_1325_);
                                    v___x_1328_ = crate::leanh::lean_box(0);
                                    v_isShared_1329_ = v_isSharedCheck_1334_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1324_);
                                return v___x_1325_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1299_);
                        crate::leanh::lean_dec_ref(v_h_1295_);
                        v___x_1335_ = crate::leanh::lean_box(0);
                        if v_isShared_1302_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1335_);
                            v___x_1337_ = v___x_1301_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1338_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
                            v___x_1337_ = v_reuseFailAlloc_1338_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1299_);
                    crate::leanh::lean_dec_ref(v_h_1295_);
                    v___x_1339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4);
                    if v_isShared_1302_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1301_, 1);
                        crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1339_);
                        v___x_1341_ = v___x_1301_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
                        v___x_1341_ = v_reuseFailAlloc_1342_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1318_;
            }
            3 => {
                return v___x_1322_;
            }
            4 => {
                v___x_1330_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1330_, 0, v_val_1324_);
                crate::leanh::lean_ctor_set(v___x_1330_, 1, v_a_1326_);
                if v_isShared_1329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1328_, 0, v___x_1330_);
                    v___x_1332_ = v___x_1328_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
                    v___x_1332_ = v_reuseFailAlloc_1333_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1332_;
            }
            6 => {
                return v___x_1337_;
            }
            7 => {
                return v___x_1341_;
            }
            8 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(
    mut v_h_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_1352_);
    return v_res_1354_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_x_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1359_) == 0 {
                    return v_x_1358_;
                } else {
                    v_head_1360_ = crate::leanh::lean_ctor_get(v_x_1359_, 0);
                    v_tail_1361_ = crate::leanh::lean_ctor_get(v_x_1359_, 1);
                    v_fst_1362_ = crate::leanh::lean_ctor_get(v_head_1360_, 0);
                    v_snd_1363_ = crate::leanh::lean_ctor_get(v_head_1360_, 1);
                    v___x_1364_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
                    v___x_1365_ = lean_string_append(v_x_1358_, v___x_1364_);
                    v___x_1366_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
                    v___x_1367_ = lean_string_append(v___x_1366_, v_fst_1362_);
                    v___x_1368_ = lean_string_append(v___x_1367_, v___x_1364_);
                    v___x_1369_ = lean_string_append(v___x_1368_, v_snd_1363_);
                    v___x_1370_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
                    v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
                    v___x_1372_ = lean_string_append(v___x_1365_, v___x_1371_);
                    crate::leanh::lean_dec_ref(v___x_1371_);
                    v_x_1358_ = v___x_1372_;
                    v_x_1359_ = v_tail_1361_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(
    mut v_x_1374_: *mut crate::leanh::LeanObject,
    mut v_x_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_1374_, v_x_1375_);
    crate::leanh::lean_dec(v_x_1375_);
    return v_res_1376_;
}
pub unsafe fn l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(
    mut v_x_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1380_) == 0 {
        let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1381_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
        return v___x_1381_;
    } else {
        let mut v_tail_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1382_ = crate::leanh::lean_ctor_get(v_x_1380_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1382_) == 0 {
            let mut v_head_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_1383_ = crate::leanh::lean_ctor_get(v_x_1380_, 0);
            v_fst_1384_ = crate::leanh::lean_ctor_get(v_head_1383_, 0);
            v_snd_1385_ = crate::leanh::lean_ctor_get(v_head_1383_, 1);
            v___x_1386_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
            v___x_1387_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
            v___x_1388_ = lean_string_append(v___x_1387_, v_fst_1384_);
            v___x_1389_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
            v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
            v___x_1391_ = lean_string_append(v___x_1390_, v_snd_1385_);
            v___x_1392_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
            v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
            v___x_1394_ = lean_string_append(v___x_1386_, v___x_1393_);
            crate::leanh::lean_dec_ref(v___x_1393_);
            v___x_1395_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
            v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
            return v___x_1396_;
        } else {
            let mut v_head_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1410_: u32 = 0;
            let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_1397_ = crate::leanh::lean_ctor_get(v_x_1380_, 0);
            v_fst_1398_ = crate::leanh::lean_ctor_get(v_head_1397_, 0);
            v_snd_1399_ = crate::leanh::lean_ctor_get(v_head_1397_, 1);
            v___x_1400_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
            v___x_1401_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
            v___x_1402_ = lean_string_append(v___x_1401_, v_fst_1398_);
            v___x_1403_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
            v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
            v___x_1405_ = lean_string_append(v___x_1404_, v_snd_1399_);
            v___x_1406_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
            v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
            v___x_1408_ = lean_string_append(v___x_1400_, v___x_1407_);
            crate::leanh::lean_dec_ref(v___x_1407_);
            v___x_1409_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_1408_, v_tail_1382_);
            v___x_1410_ = 93;
            v___x_1411_ = lean_string_push(v___x_1409_, v___x_1410_);
            return v___x_1411_;
        }
    }
}
pub unsafe fn l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(
    mut v_x_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_x_1412_);
    crate::leanh::lean_dec(v_x_1412_);
    return v_res_1413_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(
    mut v_x_1414_: *mut crate::leanh::LeanObject,
    mut v_x_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1415_) == 0 {
                    v___x_1416_ = crate::leanh::lean_box(0);
                    return v___x_1416_;
                } else {
                    v_head_1417_ = crate::leanh::lean_ctor_get(v_x_1415_, 0);
                    v_tail_1418_ = crate::leanh::lean_ctor_get(v_x_1415_, 1);
                    v_fst_1419_ = crate::leanh::lean_ctor_get(v_head_1417_, 0);
                    v_snd_1420_ = crate::leanh::lean_ctor_get(v_head_1417_, 1);
                    v___x_1421_ = lean_string_dec_eq(v_x_1414_, v_fst_1419_);
                    if v___x_1421_ == 0 {
                        v_x_1415_ = v_tail_1418_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1420_);
                        v___x_1423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1423_, 0, v_snd_1420_);
                        return v___x_1423_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(
    mut v_x_1424_: *mut crate::leanh::LeanObject,
    mut v_x_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_1424_, v_x_1425_);
    crate::leanh::lean_dec(v_x_1425_);
    crate::leanh::lean_dec_ref(v_x_1424_);
    return v_res_1426_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
    mut v_h_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_a_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1433_ =
                    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(
                        v_h_1431_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1433_) == 0 {
                    v_a_1434_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                    v_isSharedCheck_1464_ = (!crate::leanh::lean_is_exclusive(v___x_1433_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1436_ = v___x_1433_;
                        v_isShared_1437_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1434_);
                        crate::leanh::lean_dec(v___x_1433_);
                        v___x_1436_ = crate::leanh::lean_box(0);
                        v_isShared_1437_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1465_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                    v_isSharedCheck_1472_ = (!crate::leanh::lean_is_exclusive(v___x_1433_)) as u8;
                    if v_isSharedCheck_1472_ == 0 {
                        v___x_1467_ = v___x_1433_;
                        v_isShared_1468_ = v_isSharedCheck_1472_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1465_);
                        crate::leanh::lean_dec(v___x_1433_);
                        v___x_1467_ = crate::leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1472_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1438_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
                v___x_1439_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_1438_, v_a_1434_);
                if crate::leanh::lean_obj_tag(v___x_1439_) == 0 {
                    v___x_1440_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
                    v___x_1441_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_a_1434_);
                    crate::leanh::lean_dec(v_a_1434_);
                    v___x_1442_ = lean_string_append(v___x_1440_, v___x_1441_);
                    crate::leanh::lean_dec_ref(v___x_1441_);
                    v___x_1443_ = lean_mk_io_user_error(v___x_1442_);
                    if v_isShared_1437_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1436_, 1);
                        crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1443_);
                        v___x_1445_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
                        v___x_1445_ = v_reuseFailAlloc_1446_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1434_);
                    v_val_1447_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    crate::leanh::lean_inc_n(v_val_1447_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1439_, 1);
                    v___x_1448_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1449_ = lean_string_utf8_byte_size(v_val_1447_);
                    v___x_1450_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1450_, 0, v_val_1447_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 1, v___x_1448_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 2, v___x_1449_);
                    v___x_1451_ = l_String_Slice_toNat_x3f(v___x_1450_);
                    crate::leanh::lean_dec_ref_known(v___x_1450_, 3);
                    if crate::leanh::lean_obj_tag(v___x_1451_) == 0 {
                        v___x_1452_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
                        v___x_1453_ = lean_string_append(v___x_1452_, v_val_1447_);
                        crate::leanh::lean_dec(v_val_1447_);
                        v___x_1454_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
                        v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
                        v___x_1456_ = lean_mk_io_user_error(v___x_1455_);
                        if v_isShared_1437_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1436_, 1);
                            crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1456_);
                            v___x_1458_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1459_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
                            v___x_1458_ = v_reuseFailAlloc_1459_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1447_);
                        v_val_1460_ = crate::leanh::lean_ctor_get(v___x_1451_, 0);
                        crate::leanh::lean_inc(v_val_1460_);
                        crate::leanh::lean_dec_ref_known(v___x_1451_, 1);
                        if v_isShared_1437_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1436_, 0, v_val_1460_);
                            v___x_1462_ = v___x_1436_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1463_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_val_1460_);
                            v___x_1462_ = v_reuseFailAlloc_1463_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1445_;
            }
            3 => {
                return v___x_1458_;
            }
            4 => {
                return v___x_1462_;
            }
            5 => {
                if v_isShared_1468_ == 0 {
                    v___x_1470_ = v___x_1467_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
                    v___x_1470_ = v_reuseFailAlloc_1471_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(
    mut v_h_1473_: *mut crate::leanh::LeanObject,
    mut v_a_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_1473_);
    return v_res_1475_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(
    mut v_00_u03b2_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
    mut v_x_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_1477_, v_x_1478_);
    return v___x_1479_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(
    mut v_00_u03b2_1480_: *mut crate::leanh::LeanObject,
    mut v_x_1481_: *mut crate::leanh::LeanObject,
    mut v_x_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_1480_, v_x_1481_, v_x_1482_);
    crate::leanh::lean_dec(v_x_1482_);
    crate::leanh::lean_dec_ref(v_x_1481_);
    return v_res_1483_;
}
pub unsafe fn l_IO_FS_Stream_readLspMessage(
    mut v_h_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_1485_);
                v___x_1494_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1485_,
                );
                if crate::leanh::lean_obj_tag(v___x_1494_) == 0 {
                    v_a_1495_ = crate::leanh::lean_ctor_get(v___x_1494_, 0);
                    crate::leanh::lean_inc(v_a_1495_);
                    crate::leanh::lean_dec_ref_known(v___x_1494_, 1);
                    v___x_1496_ = l_IO_FS_Stream_readMessage(v_h_1485_, v_a_1495_);
                    crate::leanh::lean_dec(v_a_1495_);
                    if crate::leanh::lean_obj_tag(v___x_1496_) == 0 {
                        return v___x_1496_;
                    } else {
                        v_a_1497_ = crate::leanh::lean_ctor_get(v___x_1496_, 0);
                        crate::leanh::lean_inc(v_a_1497_);
                        crate::leanh::lean_dec_ref_known(v___x_1496_, 1);
                        v_a_1488_ = v_a_1497_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_1485_);
                    v_a_1498_ = crate::leanh::lean_ctor_get(v___x_1494_, 0);
                    crate::leanh::lean_inc(v_a_1498_);
                    crate::leanh::lean_dec_ref_known(v___x_1494_, 1);
                    v_a_1488_ = v_a_1498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1489_ = l_IO_FS_Stream_readLspMessage___closed__0;
                v___x_1490_ = lean_io_error_to_string(v_a_1488_);
                v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
                crate::leanh::lean_dec_ref(v___x_1490_);
                v___x_1492_ = lean_mk_io_user_error(v___x_1491_);
                v___x_1493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1493_, 0, v___x_1492_);
                return v___x_1493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspMessage___boxed(
    mut v_h_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_IO_FS_Stream_readLspMessage(v_h_1499_);
    return v_res_1501_;
}
pub unsafe fn l_IO_FS_Stream_readLspMessageAsString(
    mut v_h_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_1502_);
                v___x_1511_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1502_,
                );
                if crate::leanh::lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = crate::leanh::lean_ctor_get(v___x_1511_, 0);
                    crate::leanh::lean_inc(v_a_1512_);
                    crate::leanh::lean_dec_ref_known(v___x_1511_, 1);
                    v___x_1513_ = l_IO_FS_Stream_readUTF8(v_h_1502_, v_a_1512_);
                    crate::leanh::lean_dec(v_a_1512_);
                    if crate::leanh::lean_obj_tag(v___x_1513_) == 0 {
                        return v___x_1513_;
                    } else {
                        v_a_1514_ = crate::leanh::lean_ctor_get(v___x_1513_, 0);
                        crate::leanh::lean_inc(v_a_1514_);
                        crate::leanh::lean_dec_ref_known(v___x_1513_, 1);
                        v_a_1505_ = v_a_1514_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_1502_);
                    v_a_1515_ = crate::leanh::lean_ctor_get(v___x_1511_, 0);
                    crate::leanh::lean_inc(v_a_1515_);
                    crate::leanh::lean_dec_ref_known(v___x_1511_, 1);
                    v_a_1505_ = v_a_1515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1506_ = l_IO_FS_Stream_readLspMessage___closed__0;
                v___x_1507_ = lean_io_error_to_string(v_a_1505_);
                v___x_1508_ = lean_string_append(v___x_1506_, v___x_1507_);
                crate::leanh::lean_dec_ref(v___x_1507_);
                v___x_1509_ = lean_mk_io_user_error(v___x_1508_);
                v___x_1510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
                return v___x_1510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspMessageAsString___boxed(
    mut v_h_1516_: *mut crate::leanh::LeanObject,
    mut v_a_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_IO_FS_Stream_readLspMessageAsString(v_h_1516_);
    return v_res_1518_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___redArg(
    mut v_h_1520_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1521_: *mut crate::leanh::LeanObject,
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_1520_);
                v___x_1531_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1520_,
                );
                if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    crate::leanh::lean_inc(v_a_1532_);
                    crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                    v___x_1533_ = l_IO_FS_Stream_readRequestAs___redArg(
                        v_h_1520_,
                        v_a_1532_,
                        v_expectedMethod_1521_,
                        v_inst_1522_,
                    );
                    crate::leanh::lean_dec(v_a_1532_);
                    if crate::leanh::lean_obj_tag(v___x_1533_) == 0 {
                        return v___x_1533_;
                    } else {
                        v_a_1534_ = crate::leanh::lean_ctor_get(v___x_1533_, 0);
                        crate::leanh::lean_inc(v_a_1534_);
                        crate::leanh::lean_dec_ref_known(v___x_1533_, 1);
                        v_a_1525_ = v_a_1534_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1522_);
                    crate::leanh::lean_dec_ref(v_expectedMethod_1521_);
                    crate::leanh::lean_dec_ref(v_h_1520_);
                    v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    crate::leanh::lean_inc(v_a_1535_);
                    crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                    v_a_1525_ = v_a_1535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1526_ = l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
                v___x_1527_ = lean_io_error_to_string(v_a_1525_);
                v___x_1528_ = lean_string_append(v___x_1526_, v___x_1527_);
                crate::leanh::lean_dec_ref(v___x_1527_);
                v___x_1529_ = lean_mk_io_user_error(v___x_1528_);
                v___x_1530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___redArg___boxed(
    mut v_h_1536_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1537_: *mut crate::leanh::LeanObject,
    mut v_inst_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ =
        l_IO_FS_Stream_readLspRequestAs___redArg(v_h_1536_, v_expectedMethod_1537_, v_inst_1538_);
    return v_res_1540_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs(
    mut v_h_1541_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ =
        l_IO_FS_Stream_readLspRequestAs___redArg(v_h_1541_, v_expectedMethod_1542_, v_inst_1544_);
    return v___x_1546_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___boxed(
    mut v_h_1547_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1549_: *mut crate::leanh::LeanObject,
    mut v_inst_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_IO_FS_Stream_readLspRequestAs(
        v_h_1547_,
        v_expectedMethod_1548_,
        v_00_u03b1_1549_,
        v_inst_1550_,
    );
    return v_res_1552_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___redArg(
    mut v_h_1554_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1555_: *mut crate::leanh::LeanObject,
    mut v_inst_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_1554_);
                v___x_1565_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1554_,
                );
                if crate::leanh::lean_obj_tag(v___x_1565_) == 0 {
                    v_a_1566_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                    crate::leanh::lean_inc(v_a_1566_);
                    crate::leanh::lean_dec_ref_known(v___x_1565_, 1);
                    v___x_1567_ = l_IO_FS_Stream_readNotificationAs___redArg(
                        v_h_1554_,
                        v_a_1566_,
                        v_expectedMethod_1555_,
                        v_inst_1556_,
                    );
                    crate::leanh::lean_dec(v_a_1566_);
                    if crate::leanh::lean_obj_tag(v___x_1567_) == 0 {
                        return v___x_1567_;
                    } else {
                        v_a_1568_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                        crate::leanh::lean_inc(v_a_1568_);
                        crate::leanh::lean_dec_ref_known(v___x_1567_, 1);
                        v_a_1559_ = v_a_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1556_);
                    crate::leanh::lean_dec_ref(v_expectedMethod_1555_);
                    crate::leanh::lean_dec_ref(v_h_1554_);
                    v_a_1569_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                    crate::leanh::lean_inc(v_a_1569_);
                    crate::leanh::lean_dec_ref_known(v___x_1565_, 1);
                    v_a_1559_ = v_a_1569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1560_ = l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
                v___x_1561_ = lean_io_error_to_string(v_a_1559_);
                v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
                crate::leanh::lean_dec_ref(v___x_1561_);
                v___x_1563_ = lean_mk_io_user_error(v___x_1562_);
                v___x_1564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1564_, 0, v___x_1563_);
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(
    mut v_h_1570_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1571_: *mut crate::leanh::LeanObject,
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_IO_FS_Stream_readLspNotificationAs___redArg(
        v_h_1570_,
        v_expectedMethod_1571_,
        v_inst_1572_,
    );
    return v_res_1574_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs(
    mut v_h_1575_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1576_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1577_: *mut crate::leanh::LeanObject,
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_IO_FS_Stream_readLspNotificationAs___redArg(
        v_h_1575_,
        v_expectedMethod_1576_,
        v_inst_1578_,
    );
    return v___x_1580_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___boxed(
    mut v_h_1581_: *mut crate::leanh::LeanObject,
    mut v_expectedMethod_1582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1583_: *mut crate::leanh::LeanObject,
    mut v_inst_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_IO_FS_Stream_readLspNotificationAs(
        v_h_1581_,
        v_expectedMethod_1582_,
        v_00_u03b1_1583_,
        v_inst_1584_,
    );
    return v_res_1586_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___redArg(
    mut v_h_1588_: *mut crate::leanh::LeanObject,
    mut v_expectedID_1589_: *mut crate::leanh::LeanObject,
    mut v_inst_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_1588_);
                v___x_1599_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1588_,
                );
                if crate::leanh::lean_obj_tag(v___x_1599_) == 0 {
                    v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                    crate::leanh::lean_inc(v_a_1600_);
                    crate::leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v___x_1601_ = l_IO_FS_Stream_readResponseAs___redArg(
                        v_h_1588_,
                        v_a_1600_,
                        v_expectedID_1589_,
                        v_inst_1590_,
                    );
                    crate::leanh::lean_dec(v_a_1600_);
                    if crate::leanh::lean_obj_tag(v___x_1601_) == 0 {
                        return v___x_1601_;
                    } else {
                        v_a_1602_ = crate::leanh::lean_ctor_get(v___x_1601_, 0);
                        crate::leanh::lean_inc(v_a_1602_);
                        crate::leanh::lean_dec_ref_known(v___x_1601_, 1);
                        v_a_1593_ = v_a_1602_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1590_);
                    crate::leanh::lean_dec(v_expectedID_1589_);
                    crate::leanh::lean_dec_ref(v_h_1588_);
                    v_a_1603_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                    crate::leanh::lean_inc(v_a_1603_);
                    crate::leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v_a_1593_ = v_a_1603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1594_ = l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
                v___x_1595_ = lean_io_error_to_string(v_a_1593_);
                v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
                crate::leanh::lean_dec_ref(v___x_1595_);
                v___x_1597_ = lean_mk_io_user_error(v___x_1596_);
                v___x_1598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1597_);
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___redArg___boxed(
    mut v_h_1604_: *mut crate::leanh::LeanObject,
    mut v_expectedID_1605_: *mut crate::leanh::LeanObject,
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1608_ =
        l_IO_FS_Stream_readLspResponseAs___redArg(v_h_1604_, v_expectedID_1605_, v_inst_1606_);
    return v_res_1608_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs(
    mut v_h_1609_: *mut crate::leanh::LeanObject,
    mut v_expectedID_1610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1611_: *mut crate::leanh::LeanObject,
    mut v_inst_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ =
        l_IO_FS_Stream_readLspResponseAs___redArg(v_h_1609_, v_expectedID_1610_, v_inst_1612_);
    return v___x_1614_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___boxed(
    mut v_h_1615_: *mut crate::leanh::LeanObject,
    mut v_expectedID_1616_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1617_: *mut crate::leanh::LeanObject,
    mut v_inst_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_IO_FS_Stream_readLspResponseAs(
        v_h_1615_,
        v_expectedID_1616_,
        v_00_u03b1_1617_,
        v_inst_1618_,
    );
    return v_res_1620_;
}
pub unsafe fn l_IO_FS_Stream_writeSerializedLspMessage(
    mut v_h_1623_: *mut crate::leanh::LeanObject,
    mut v_msg_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flush_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_header_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flush_1626_ = crate::leanh::lean_ctor_get(v_h_1623_, 0);
    crate::leanh::lean_inc_ref(v_flush_1626_);
    v_putStr_1627_ = crate::leanh::lean_ctor_get(v_h_1623_, 4);
    crate::leanh::lean_inc_ref(v_putStr_1627_);
    crate::leanh::lean_dec_ref(v_h_1623_);
    v___x_1628_ = l_IO_FS_Stream_writeSerializedLspMessage___closed__0;
    v___x_1629_ = lean_string_utf8_byte_size(v_msg_1624_);
    v___x_1630_ = l_Nat_reprFast(v___x_1629_);
    v___x_1631_ = lean_string_append(v___x_1628_, v___x_1630_);
    crate::leanh::lean_dec_ref(v___x_1630_);
    v___x_1632_ = l_IO_FS_Stream_writeSerializedLspMessage___closed__1;
    v_header_1633_ = lean_string_append(v___x_1631_, v___x_1632_);
    v___x_1634_ = lean_string_append(v_header_1633_, v_msg_1624_);
    v___x_1635_ =
        crate::leanh::lean_apply_2(v_putStr_1627_, v___x_1634_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_1635_) == 0 {
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1635_, 1);
        v___x_1636_ = crate::leanh::lean_apply_1(v_flush_1626_, crate::leanh::lean_box(0));
        return v___x_1636_;
    } else {
        crate::leanh::lean_dec_ref(v_flush_1626_);
        return v___x_1635_;
    }
}
pub unsafe fn l_IO_FS_Stream_writeSerializedLspMessage___boxed(
    mut v_h_1637_: *mut crate::leanh::LeanObject,
    mut v_msg_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_1637_, v_msg_1638_);
    crate::leanh::lean_dec_ref(v_msg_1638_);
    return v_res_1640_;
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(
    mut v_k_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1642_) == 0 {
        let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_1641_);
        v___x_1643_ = crate::leanh::lean_box(0);
        return v___x_1643_;
    } else {
        let mut v_val_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1644_ = crate::leanh::lean_ctor_get(v_x_1642_, 0);
        crate::leanh::lean_inc(v_val_1644_);
        crate::leanh::lean_dec_ref_known(v_x_1642_, 1);
        v___x_1645_ = l_Lean_Json_Structured_toJson(v_val_1644_);
        v___x_1646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1646_, 0, v_k_1641_);
        crate::leanh::lean_ctor_set(v___x_1646_, 1, v___x_1645_);
        v___x_1647_ = crate::leanh::lean_box(0);
        v___x_1648_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1646_);
        crate::leanh::lean_ctor_set(v___x_1648_, 1, v___x_1647_);
        return v___x_1648_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(
    mut v_k_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1650_) == 0 {
        let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_1649_);
        v___x_1651_ = crate::leanh::lean_box(0);
        return v___x_1651_;
    } else {
        let mut v_val_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1652_ = crate::leanh::lean_ctor_get(v_x_1650_, 0);
        crate::leanh::lean_inc(v_val_1652_);
        v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1653_, 0, v_k_1649_);
        crate::leanh::lean_ctor_set(v___x_1653_, 1, v_val_1652_);
        v___x_1654_ = crate::leanh::lean_box(0);
        v___x_1655_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1653_);
        crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
        return v___x_1655_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(
    mut v_k_1656_: *mut crate::leanh::LeanObject,
    mut v_x_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ =
        l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(v_k_1656_, v_x_1657_);
    crate::leanh::lean_dec(v_x_1657_);
    return v_res_1658_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = crate::leanh::lean_unsigned_to_nat(32700);
    v___x_1675_ = lean_nat_to_int(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__12),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__12_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__12,
    );
    v___x_1677_ = lean_int_neg(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__13),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__13_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__13,
    );
    v___x_1679_ = l_Lean_JsonNumber_fromInt(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__14),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__14_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__14,
    );
    v___x_1681_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = crate::leanh::lean_unsigned_to_nat(32600);
    v___x_1683_ = lean_nat_to_int(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__16),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__16_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__16,
    );
    v___x_1685_ = lean_int_neg(v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__17),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__17_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__17,
    );
    v___x_1687_ = l_Lean_JsonNumber_fromInt(v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__18),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__18_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__18,
    );
    v___x_1689_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = crate::leanh::lean_unsigned_to_nat(32601);
    v___x_1691_ = lean_nat_to_int(v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__20),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__20_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__20,
    );
    v___x_1693_ = lean_int_neg(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__21),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__21_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__21,
    );
    v___x_1695_ = l_Lean_JsonNumber_fromInt(v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__22),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__22_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__22,
    );
    v___x_1697_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = crate::leanh::lean_unsigned_to_nat(32602);
    v___x_1699_ = lean_nat_to_int(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__24),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__24_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__24,
    );
    v___x_1701_ = lean_int_neg(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__25),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__25_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__25,
    );
    v___x_1703_ = l_Lean_JsonNumber_fromInt(v___x_1702_);
    return v___x_1703_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__26),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__26_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__26,
    );
    v___x_1705_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1705_, 0, v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = crate::leanh::lean_unsigned_to_nat(32603);
    v___x_1707_ = lean_nat_to_int(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__28),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__28_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__28,
    );
    v___x_1709_ = lean_int_neg(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__29),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__29_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__29,
    );
    v___x_1711_ = l_Lean_JsonNumber_fromInt(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__30),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__30_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__30,
    );
    v___x_1713_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1713_, 0, v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = crate::leanh::lean_unsigned_to_nat(32002);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__32),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__32_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__32,
    );
    v___x_1717_ = lean_int_neg(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__33),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__33_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__33,
    );
    v___x_1719_ = l_Lean_JsonNumber_fromInt(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__35() -> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__34),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__34_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__34,
    );
    v___x_1721_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__36() -> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = crate::leanh::lean_unsigned_to_nat(32001);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__37() -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__36),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__36_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__36,
    );
    v___x_1725_ = lean_int_neg(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__37),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__37_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__37,
    );
    v___x_1727_ = l_Lean_JsonNumber_fromInt(v___x_1726_);
    return v___x_1727_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__39() -> *mut crate::leanh::LeanObject {
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__38),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__38_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__38,
    );
    v___x_1729_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
    return v___x_1729_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = crate::leanh::lean_unsigned_to_nat(32801);
    v___x_1731_ = lean_nat_to_int(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__41() -> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__40),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__40_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__40,
    );
    v___x_1733_ = lean_int_neg(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__42() -> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__41),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__41_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__41,
    );
    v___x_1735_ = l_Lean_JsonNumber_fromInt(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__43() -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__42),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__42_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__42,
    );
    v___x_1737_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = crate::leanh::lean_unsigned_to_nat(32800);
    v___x_1739_ = lean_nat_to_int(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__44),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__44_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__44,
    );
    v___x_1741_ = lean_int_neg(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__45),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__45_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__45,
    );
    v___x_1743_ = l_Lean_JsonNumber_fromInt(v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__47() -> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__46),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__46_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__46,
    );
    v___x_1745_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__48() -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_unsigned_to_nat(32900);
    v___x_1747_ = lean_nat_to_int(v___x_1746_);
    return v___x_1747_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__49() -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__48),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__48_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__48,
    );
    v___x_1749_ = lean_int_neg(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__50() -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__49),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__49_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__49,
    );
    v___x_1751_ = l_Lean_JsonNumber_fromInt(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__51() -> *mut crate::leanh::LeanObject {
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__50),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__50_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__50,
    );
    v___x_1753_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__52() -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = crate::leanh::lean_unsigned_to_nat(32901);
    v___x_1755_ = lean_nat_to_int(v___x_1754_);
    return v___x_1755_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__53() -> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__52),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__52_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__52,
    );
    v___x_1757_ = lean_int_neg(v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__54() -> *mut crate::leanh::LeanObject {
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__53),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__53_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__53,
    );
    v___x_1759_ = l_Lean_JsonNumber_fromInt(v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__55() -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__54),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__54_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__54,
    );
    v___x_1761_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__56() -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = crate::leanh::lean_unsigned_to_nat(32902);
    v___x_1763_ = lean_nat_to_int(v___x_1762_);
    return v___x_1763_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__57() -> *mut crate::leanh::LeanObject {
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__56),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__56_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__56,
    );
    v___x_1765_ = lean_int_neg(v___x_1764_);
    return v___x_1765_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__58() -> *mut crate::leanh::LeanObject {
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__57),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__57_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__57,
    );
    v___x_1767_ = l_Lean_JsonNumber_fromInt(v___x_1766_);
    return v___x_1767_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__59() -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__58),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__58_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__58,
    );
    v___x_1769_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn l_IO_FS_Stream_writeLspMessage(
    mut v_h_1770_: *mut crate::leanh::LeanObject,
    mut v_msg_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_n_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_id_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v_n_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_id_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1862_: u8 = 0;
    let mut v_message_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_n_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1773_ = l_IO_FS_Stream_writeLspMessage___closed__3;
                match crate::leanh::lean_obj_tag(v_msg_1771_) {
                    0 => {
                        v_id_1780_ = crate::leanh::lean_ctor_get(v_msg_1771_, 0);
                        crate::leanh::lean_inc(v_id_1780_);
                        v_method_1781_ = crate::leanh::lean_ctor_get(v_msg_1771_, 1);
                        crate::leanh::lean_inc_ref(v_method_1781_);
                        v_params_x3f_1782_ = crate::leanh::lean_ctor_get(v_msg_1771_, 2);
                        crate::leanh::lean_inc(v_params_x3f_1782_);
                        crate::leanh::lean_dec_ref_known(v_msg_1771_, 3);
                        v___x_1783_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                        match crate::leanh::lean_obj_tag(v_id_1780_) {
                            0 => {
                                v_s_1796_ = crate::leanh::lean_ctor_get(v_id_1780_, 0);
                                v_isSharedCheck_1803_ =
                                    (!crate::leanh::lean_is_exclusive(v_id_1780_)) as u8;
                                if v_isSharedCheck_1803_ == 0 {
                                    v___x_1798_ = v_id_1780_;
                                    v_isShared_1799_ = v_isSharedCheck_1803_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_s_1796_);
                                    crate::leanh::lean_dec(v_id_1780_);
                                    v___x_1798_ = crate::leanh::lean_box(0);
                                    v_isShared_1799_ = v_isSharedCheck_1803_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_1804_ = crate::leanh::lean_ctor_get(v_id_1780_, 0);
                                v_isSharedCheck_1811_ =
                                    (!crate::leanh::lean_is_exclusive(v_id_1780_)) as u8;
                                if v_isSharedCheck_1811_ == 0 {
                                    v___x_1806_ = v_id_1780_;
                                    v_isShared_1807_ = v_isSharedCheck_1811_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_n_1804_);
                                    crate::leanh::lean_dec(v_id_1780_);
                                    v___x_1806_ = crate::leanh::lean_box(0);
                                    v_isShared_1807_ = v_isSharedCheck_1811_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_1812_ = crate::leanh::lean_box(0);
                                v___y_1785_ = v___x_1812_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_1813_ = crate::leanh::lean_ctor_get(v_msg_1771_, 0);
                        v_params_x3f_1814_ = crate::leanh::lean_ctor_get(v_msg_1771_, 1);
                        v_isSharedCheck_1826_ =
                            (!crate::leanh::lean_is_exclusive(v_msg_1771_)) as u8;
                        if v_isSharedCheck_1826_ == 0 {
                            v___x_1816_ = v_msg_1771_;
                            v_isShared_1817_ = v_isSharedCheck_1826_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_params_x3f_1814_);
                            crate::leanh::lean_inc(v_method_1813_);
                            crate::leanh::lean_dec(v_msg_1771_);
                            v___x_1816_ = crate::leanh::lean_box(0);
                            v_isShared_1817_ = v_isSharedCheck_1826_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_id_1827_ = crate::leanh::lean_ctor_get(v_msg_1771_, 0);
                        v_result_1828_ = crate::leanh::lean_ctor_get(v_msg_1771_, 1);
                        v_isSharedCheck_1860_ =
                            (!crate::leanh::lean_is_exclusive(v_msg_1771_)) as u8;
                        if v_isSharedCheck_1860_ == 0 {
                            v___x_1830_ = v_msg_1771_;
                            v_isShared_1831_ = v_isSharedCheck_1860_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_result_1828_);
                            crate::leanh::lean_inc(v_id_1827_);
                            crate::leanh::lean_dec(v_msg_1771_);
                            v___x_1830_ = crate::leanh::lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1860_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_id_1861_ = crate::leanh::lean_ctor_get(v_msg_1771_, 0);
                        crate::leanh::lean_inc(v_id_1861_);
                        v_code_1862_ = crate::leanh::lean_ctor_get_uint8(
                            v_msg_1771_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_message_1863_ = crate::leanh::lean_ctor_get(v_msg_1771_, 1);
                        crate::leanh::lean_inc_ref(v_message_1863_);
                        v_data_x3f_1864_ = crate::leanh::lean_ctor_get(v_msg_1771_, 2);
                        crate::leanh::lean_inc(v_data_x3f_1864_);
                        crate::leanh::lean_dec_ref_known(v_msg_1771_, 3);
                        v___x_1884_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                        match crate::leanh::lean_obj_tag(v_id_1861_) {
                            0 => {
                                v_s_1902_ = crate::leanh::lean_ctor_get(v_id_1861_, 0);
                                v_isSharedCheck_1909_ =
                                    (!crate::leanh::lean_is_exclusive(v_id_1861_)) as u8;
                                if v_isSharedCheck_1909_ == 0 {
                                    v___x_1904_ = v_id_1861_;
                                    v_isShared_1905_ = v_isSharedCheck_1909_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_s_1902_);
                                    crate::leanh::lean_dec(v_id_1861_);
                                    v___x_1904_ = crate::leanh::lean_box(0);
                                    v_isShared_1905_ = v_isSharedCheck_1909_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_1910_ = crate::leanh::lean_ctor_get(v_id_1861_, 0);
                                v_isSharedCheck_1917_ =
                                    (!crate::leanh::lean_is_exclusive(v_id_1861_)) as u8;
                                if v_isSharedCheck_1917_ == 0 {
                                    v___x_1912_ = v_id_1861_;
                                    v_isShared_1913_ = v_isSharedCheck_1917_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_n_1910_);
                                    crate::leanh::lean_dec(v_id_1861_);
                                    v___x_1912_ = crate::leanh::lean_box(0);
                                    v_isShared_1913_ = v_isSharedCheck_1917_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_1918_ = crate::leanh::lean_box(0);
                                v___y_1886_ = v___x_1918_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1776_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1773_);
                crate::leanh::lean_ctor_set(v___x_1776_, 1, v___y_1775_);
                v___x_1777_ = l_Lean_Json_mkObj(v___x_1776_);
                crate::leanh::lean_dec_ref_known(v___x_1776_, 2);
                v___x_1778_ = l_Lean_Json_compress(v___x_1777_);
                v___x_1779_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_1770_, v___x_1778_);
                crate::leanh::lean_dec_ref(v___x_1778_);
                return v___x_1779_;
            }
            2 => {
                v___x_1786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1786_, 0, v___x_1783_);
                crate::leanh::lean_ctor_set(v___x_1786_, 1, v___y_1785_);
                v___x_1787_ = l_IO_FS_Stream_writeLspMessage___closed__5;
                v___x_1788_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1788_, 0, v_method_1781_);
                v___x_1789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1789_, 0, v___x_1787_);
                crate::leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = crate::leanh::lean_box(0);
                v___x_1791_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1789_);
                crate::leanh::lean_ctor_set(v___x_1791_, 1, v___x_1790_);
                v___x_1792_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1786_);
                crate::leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
                v___x_1793_ = l_IO_FS_Stream_writeLspMessage___closed__6;
                v___x_1794_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(
                    v___x_1793_,
                    v_params_x3f_1782_,
                );
                v___x_1795_ = l_List_appendTR___redArg(v___x_1792_, v___x_1794_);
                v___y_1775_ = v___x_1795_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_1799_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1798_, 3);
                    v___x_1801_ = v___x_1798_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_s_1796_);
                    v___x_1801_ = v_reuseFailAlloc_1802_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1785_ = v___x_1801_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_1807_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1806_, 2);
                    v___x_1809_ = v___x_1806_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_n_1804_);
                    v___x_1809_ = v_reuseFailAlloc_1810_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1785_ = v___x_1809_;
                state = 2;
                continue;
            }
            7 => {
                v___x_1818_ = l_IO_FS_Stream_writeLspMessage___closed__5;
                v___x_1819_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1819_, 0, v_method_1813_);
                if v_isShared_1817_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1816_, 0);
                    crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1819_);
                    crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1818_);
                    v___x_1821_ = v___x_1816_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1819_);
                    v___x_1821_ = v_reuseFailAlloc_1825_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1822_ = l_IO_FS_Stream_writeLspMessage___closed__6;
                v___x_1823_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(
                    v___x_1822_,
                    v_params_x3f_1814_,
                );
                v___x_1824_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1821_);
                crate::leanh::lean_ctor_set(v___x_1824_, 1, v___x_1823_);
                v___y_1775_ = v___x_1824_;
                state = 1;
                continue;
            }
            9 => {
                v___x_1832_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                match crate::leanh::lean_obj_tag(v_id_1827_) {
                    0 => {
                        v_s_1843_ = crate::leanh::lean_ctor_get(v_id_1827_, 0);
                        v_isSharedCheck_1850_ =
                            (!crate::leanh::lean_is_exclusive(v_id_1827_)) as u8;
                        if v_isSharedCheck_1850_ == 0 {
                            v___x_1845_ = v_id_1827_;
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_1843_);
                            crate::leanh::lean_dec(v_id_1827_);
                            v___x_1845_ = crate::leanh::lean_box(0);
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_1851_ = crate::leanh::lean_ctor_get(v_id_1827_, 0);
                        v_isSharedCheck_1858_ =
                            (!crate::leanh::lean_is_exclusive(v_id_1827_)) as u8;
                        if v_isSharedCheck_1858_ == 0 {
                            v___x_1853_ = v_id_1827_;
                            v_isShared_1854_ = v_isSharedCheck_1858_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_n_1851_);
                            crate::leanh::lean_dec(v_id_1827_);
                            v___x_1853_ = crate::leanh::lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1858_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1859_ = crate::leanh::lean_box(0);
                        v___y_1834_ = v___x_1859_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1830_, 0);
                    crate::leanh::lean_ctor_set(v___x_1830_, 1, v___y_1834_);
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1836_ = v___x_1830_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___y_1834_);
                    v___x_1836_ = v_reuseFailAlloc_1842_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1837_ = l_IO_FS_Stream_writeLspMessage___closed__7;
                v___x_1838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1838_, 0, v___x_1837_);
                crate::leanh::lean_ctor_set(v___x_1838_, 1, v_result_1828_);
                v___x_1839_ = crate::leanh::lean_box(0);
                v___x_1840_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1838_);
                crate::leanh::lean_ctor_set(v___x_1840_, 1, v___x_1839_);
                v___x_1841_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1841_, 0, v___x_1836_);
                crate::leanh::lean_ctor_set(v___x_1841_, 1, v___x_1840_);
                v___y_1775_ = v___x_1841_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_1846_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1845_, 3);
                    v___x_1848_ = v___x_1845_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1849_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_s_1843_);
                    v___x_1848_ = v_reuseFailAlloc_1849_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_1834_ = v___x_1848_;
                state = 10;
                continue;
            }
            14 => {
                if v_isShared_1854_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1853_, 2);
                    v___x_1856_ = v___x_1853_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_n_1851_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_1834_ = v___x_1856_;
                state = 10;
                continue;
            }
            16 => {
                crate::leanh::lean_inc(v___y_1869_);
                crate::leanh::lean_inc_ref(v___y_1866_);
                v___x_1870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1870_, 0, v___y_1866_);
                crate::leanh::lean_ctor_set(v___x_1870_, 1, v___y_1869_);
                v___x_1871_ = l_IO_FS_Stream_writeLspMessage___closed__8;
                v___x_1872_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1872_, 0, v_message_1863_);
                v___x_1873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1871_);
                crate::leanh::lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                v___x_1874_ = crate::leanh::lean_box(0);
                v___x_1875_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                crate::leanh::lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                v___x_1876_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1870_);
                crate::leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_IO_FS_Stream_writeLspMessage___closed__9;
                v___x_1878_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(
                    v___x_1877_,
                    v_data_x3f_1864_,
                );
                crate::leanh::lean_dec(v_data_x3f_1864_);
                v___x_1879_ = l_List_appendTR___redArg(v___x_1876_, v___x_1878_);
                v___x_1880_ = l_Lean_Json_mkObj(v___x_1879_);
                crate::leanh::lean_dec(v___x_1879_);
                crate::leanh::lean_inc_ref(v___y_1868_);
                v___x_1881_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1881_, 0, v___y_1868_);
                crate::leanh::lean_ctor_set(v___x_1881_, 1, v___x_1880_);
                v___x_1882_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                crate::leanh::lean_ctor_set(v___x_1882_, 1, v___x_1874_);
                v___x_1883_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1883_, 0, v___y_1867_);
                crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                v___y_1775_ = v___x_1883_;
                state = 1;
                continue;
            }
            17 => {
                v___x_1887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1887_, 0, v___x_1884_);
                crate::leanh::lean_ctor_set(v___x_1887_, 1, v___y_1886_);
                v___x_1888_ = l_IO_FS_Stream_writeLspMessage___closed__10;
                v___x_1889_ = l_IO_FS_Stream_writeLspMessage___closed__11;
                match v_code_1862_ {
                    0 => {
                        v___x_1890_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__15),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__15_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__15,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1890_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_1891_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__19),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__19_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__19,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1891_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_1892_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__23),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__23_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__23,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1892_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_1893_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__27),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__27_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__27,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1893_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_1894_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__31),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__31_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__31,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1894_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_1895_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__35),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__35_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__35,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1895_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_1896_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__39),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__39_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__39,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1896_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_1897_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__43),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__43_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__43,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1897_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_1898_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__47),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__47_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__47,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1898_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_1899_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__51),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__51_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__51,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1899_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_1900_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__55),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__55_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__55,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1900_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_1901_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__59),
                            core::ptr::addr_of_mut!(
                                l_IO_FS_Stream_writeLspMessage___closed__59_once
                            ),
                            _init_l_IO_FS_Stream_writeLspMessage___closed__59,
                        );
                        v___y_1866_ = v___x_1889_;
                        v___y_1867_ = v___x_1887_;
                        v___y_1868_ = v___x_1888_;
                        v___y_1869_ = v___x_1901_;
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_1905_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1904_, 3);
                    v___x_1907_ = v___x_1904_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_s_1902_);
                    v___x_1907_ = v_reuseFailAlloc_1908_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_1886_ = v___x_1907_;
                state = 17;
                continue;
            }
            20 => {
                if v_isShared_1913_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1912_, 2);
                    v___x_1915_ = v___x_1912_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_n_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_1886_ = v___x_1915_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspMessage___boxed(
    mut v_h_1919_: *mut crate::leanh::LeanObject,
    mut v_msg_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_IO_FS_Stream_writeLspMessage(v_h_1919_, v_msg_1920_);
    return v_res_1922_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest___redArg(
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_h_1924_: *mut crate::leanh::LeanObject,
    mut v_r_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___y_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1927_ = crate::leanh::lean_ctor_get(v_r_1925_, 0);
                v_method_1928_ = crate::leanh::lean_ctor_get(v_r_1925_, 1);
                v_param_1929_ = crate::leanh::lean_ctor_get(v_r_1925_, 2);
                v_isSharedCheck_1949_ = (!crate::leanh::lean_is_exclusive(v_r_1925_)) as u8;
                if v_isSharedCheck_1949_ == 0 {
                    v___x_1931_ = v_r_1925_;
                    v_isShared_1932_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_param_1929_);
                    crate::leanh::lean_inc(v_method_1928_);
                    crate::leanh::lean_inc(v_id_1927_);
                    crate::leanh::lean_dec(v_r_1925_);
                    v___x_1931_ = crate::leanh::lean_box(0);
                    v_isShared_1932_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1939_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1923_, v_param_1929_);
                if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1939_, 1);
                    v___x_1940_ = crate::leanh::lean_box(0);
                    v___y_1934_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_a_1941_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v___x_1943_ = v___x_1939_;
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1941_);
                        crate::leanh::lean_dec(v___x_1939_);
                        v___x_1943_ = crate::leanh::lean_box(0);
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1931_, 2, v___y_1934_);
                    v___x_1936_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1938_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_id_1927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_method_1928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 2, v___y_1934_);
                    v___x_1936_ = v_reuseFailAlloc_1938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1937_ = l_IO_FS_Stream_writeLspMessage(v_h_1924_, v___x_1936_);
                return v___x_1937_;
            }
            4 => {
                if v_isShared_1944_ == 0 {
                    v___x_1946_ = v___x_1943_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
                    v___x_1946_ = v_reuseFailAlloc_1947_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1934_ = v___x_1946_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest___redArg___boxed(
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
    mut v_h_1951_: *mut crate::leanh::LeanObject,
    mut v_r_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_1950_, v_h_1951_, v_r_1952_);
    return v_res_1954_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest(
    mut v_00_u03b1_1955_: *mut crate::leanh::LeanObject,
    mut v_inst_1956_: *mut crate::leanh::LeanObject,
    mut v_h_1957_: *mut crate::leanh::LeanObject,
    mut v_r_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_1956_, v_h_1957_, v_r_1958_);
    return v___x_1960_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest___boxed(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
    mut v_inst_1962_: *mut crate::leanh::LeanObject,
    mut v_h_1963_: *mut crate::leanh::LeanObject,
    mut v_r_1964_: *mut crate::leanh::LeanObject,
    mut v_a_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ =
        l_IO_FS_Stream_writeLspRequest(v_00_u03b1_1961_, v_inst_1962_, v_h_1963_, v_r_1964_);
    return v_res_1966_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification___redArg(
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
    mut v_h_1968_: *mut crate::leanh::LeanObject,
    mut v_n_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_method_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___y_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_isSharedCheck_1992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_1971_ = crate::leanh::lean_ctor_get(v_n_1969_, 0);
                v_param_1972_ = crate::leanh::lean_ctor_get(v_n_1969_, 1);
                v_isSharedCheck_1992_ = (!crate::leanh::lean_is_exclusive(v_n_1969_)) as u8;
                if v_isSharedCheck_1992_ == 0 {
                    v___x_1974_ = v_n_1969_;
                    v_isShared_1975_ = v_isSharedCheck_1992_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_param_1972_);
                    crate::leanh::lean_inc(v_method_1971_);
                    crate::leanh::lean_dec(v_n_1969_);
                    v___x_1974_ = crate::leanh::lean_box(0);
                    v_isShared_1975_ = v_isSharedCheck_1992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1967_, v_param_1972_);
                if crate::leanh::lean_obj_tag(v___x_1982_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1982_, 1);
                    v___x_1983_ = crate::leanh::lean_box(0);
                    v___y_1977_ = v___x_1983_;
                    state = 2;
                    continue;
                } else {
                    v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1982_, 0);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1986_ = v___x_1982_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1984_);
                        crate::leanh::lean_dec(v___x_1982_);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1975_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1974_, 1);
                    crate::leanh::lean_ctor_set(v___x_1974_, 1, v___y_1977_);
                    v___x_1979_ = v___x_1974_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_method_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___y_1977_);
                    v___x_1979_ = v_reuseFailAlloc_1981_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1980_ = l_IO_FS_Stream_writeLspMessage(v_h_1968_, v___x_1979_);
                return v___x_1980_;
            }
            4 => {
                if v_isShared_1987_ == 0 {
                    v___x_1989_ = v___x_1986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1977_ = v___x_1989_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification___redArg___boxed(
    mut v_inst_1993_: *mut crate::leanh::LeanObject,
    mut v_h_1994_: *mut crate::leanh::LeanObject,
    mut v_n_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_1993_, v_h_1994_, v_n_1995_);
    return v_res_1997_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification(
    mut v_00_u03b1_1998_: *mut crate::leanh::LeanObject,
    mut v_inst_1999_: *mut crate::leanh::LeanObject,
    mut v_h_2000_: *mut crate::leanh::LeanObject,
    mut v_n_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_1999_, v_h_2000_, v_n_2001_);
    return v___x_2003_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification___boxed(
    mut v_00_u03b1_2004_: *mut crate::leanh::LeanObject,
    mut v_inst_2005_: *mut crate::leanh::LeanObject,
    mut v_h_2006_: *mut crate::leanh::LeanObject,
    mut v_n_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ =
        l_IO_FS_Stream_writeLspNotification(v_00_u03b1_2004_, v_inst_2005_, v_h_2006_, v_n_2007_);
    return v_res_2009_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse___redArg(
    mut v_inst_2010_: *mut crate::leanh::LeanObject,
    mut v_h_2011_: *mut crate::leanh::LeanObject,
    mut v_r_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2014_ = crate::leanh::lean_ctor_get(v_r_2012_, 0);
                v_result_2015_ = crate::leanh::lean_ctor_get(v_r_2012_, 1);
                v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v_r_2012_)) as u8;
                if v_isSharedCheck_2024_ == 0 {
                    v___x_2017_ = v_r_2012_;
                    v_isShared_2018_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_result_2015_);
                    crate::leanh::lean_inc(v_id_2014_);
                    crate::leanh::lean_dec(v_r_2012_);
                    v___x_2017_ = crate::leanh::lean_box(0);
                    v_isShared_2018_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2019_ = crate::leanh::lean_apply_1(v_inst_2010_, v_result_2015_);
                if v_isShared_2018_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2017_, 2);
                    crate::leanh::lean_ctor_set(v___x_2017_, 1, v___x_2019_);
                    v___x_2021_ = v___x_2017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_id_2014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2019_);
                    v___x_2021_ = v_reuseFailAlloc_2023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2022_ = l_IO_FS_Stream_writeLspMessage(v_h_2011_, v___x_2021_);
                return v___x_2022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse___redArg___boxed(
    mut v_inst_2025_: *mut crate::leanh::LeanObject,
    mut v_h_2026_: *mut crate::leanh::LeanObject,
    mut v_r_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_2025_, v_h_2026_, v_r_2027_);
    return v_res_2029_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse(
    mut v_00_u03b1_2030_: *mut crate::leanh::LeanObject,
    mut v_inst_2031_: *mut crate::leanh::LeanObject,
    mut v_h_2032_: *mut crate::leanh::LeanObject,
    mut v_r_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_2031_, v_h_2032_, v_r_2033_);
    return v___x_2035_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse___boxed(
    mut v_00_u03b1_2036_: *mut crate::leanh::LeanObject,
    mut v_inst_2037_: *mut crate::leanh::LeanObject,
    mut v_h_2038_: *mut crate::leanh::LeanObject,
    mut v_r_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2041_ =
        l_IO_FS_Stream_writeLspResponse(v_00_u03b1_2036_, v_inst_2037_, v_h_2038_, v_r_2039_);
    return v_res_2041_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseError(
    mut v_h_2042_: *mut crate::leanh::LeanObject,
    mut v_e_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2046_: u8 = 0;
    let mut v_message_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2045_ = crate::leanh::lean_ctor_get(v_e_2043_, 0);
                v_code_2046_ = crate::leanh::lean_ctor_get_uint8(
                    v_e_2043_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_message_2047_ = crate::leanh::lean_ctor_get(v_e_2043_, 1);
                v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v_e_2043_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = crate::leanh::lean_ctor_get(v_e_2043_, 2);
                    crate::leanh::lean_dec(v_unused_2057_);
                    v___x_2049_ = v_e_2043_;
                    v_isShared_2050_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_message_2047_);
                    crate::leanh::lean_inc(v_id_2045_);
                    crate::leanh::lean_dec(v_e_2043_);
                    v___x_2049_ = crate::leanh::lean_box(0);
                    v_isShared_2050_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2051_ = crate::leanh::lean_box(0);
                if v_isShared_2050_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2049_, 3);
                    crate::leanh::lean_ctor_set(v___x_2049_, 2, v___x_2051_);
                    v___x_2053_ = v___x_2049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = crate::leanh::lean_alloc_ctor(3, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_id_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_message_2047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 2, v___x_2051_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2055_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_code_2046_,
                    );
                    v___x_2053_ = v_reuseFailAlloc_2055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2054_ = l_IO_FS_Stream_writeLspMessage(v_h_2042_, v___x_2053_);
                return v___x_2054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseError___boxed(
    mut v_h_2058_: *mut crate::leanh::LeanObject,
    mut v_e_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2061_ = l_IO_FS_Stream_writeLspResponseError(v_h_2058_, v_e_2059_);
    return v_res_2061_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
    mut v_h_2063_: *mut crate::leanh::LeanObject,
    mut v_e_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2067_: u8 = 0;
    let mut v_message_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___y_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2066_ = crate::leanh::lean_ctor_get(v_e_2064_, 0);
                v_code_2067_ = crate::leanh::lean_ctor_get_uint8(
                    v_e_2064_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_message_2068_ = crate::leanh::lean_ctor_get(v_e_2064_, 1);
                v_data_x3f_2069_ = crate::leanh::lean_ctor_get(v_e_2064_, 2);
                v_isSharedCheck_2089_ = (!crate::leanh::lean_is_exclusive(v_e_2064_)) as u8;
                if v_isSharedCheck_2089_ == 0 {
                    v___x_2071_ = v_e_2064_;
                    v_isShared_2072_ = v_isSharedCheck_2089_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_data_x3f_2069_);
                    crate::leanh::lean_inc(v_message_2068_);
                    crate::leanh::lean_inc(v_id_2066_);
                    crate::leanh::lean_dec(v_e_2064_);
                    v___x_2071_ = crate::leanh::lean_box(0);
                    v_isShared_2072_ = v_isSharedCheck_2089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_data_x3f_2069_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2062_);
                    v___x_2079_ = crate::leanh::lean_box(0);
                    v___y_2074_ = v___x_2079_;
                    state = 2;
                    continue;
                } else {
                    v_val_2080_ = crate::leanh::lean_ctor_get(v_data_x3f_2069_, 0);
                    v_isSharedCheck_2088_ =
                        (!crate::leanh::lean_is_exclusive(v_data_x3f_2069_)) as u8;
                    if v_isSharedCheck_2088_ == 0 {
                        v___x_2082_ = v_data_x3f_2069_;
                        v_isShared_2083_ = v_isSharedCheck_2088_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2080_);
                        crate::leanh::lean_dec(v_data_x3f_2069_);
                        v___x_2082_ = crate::leanh::lean_box(0);
                        v_isShared_2083_ = v_isSharedCheck_2088_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2072_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2071_, 3);
                    crate::leanh::lean_ctor_set(v___x_2071_, 2, v___y_2074_);
                    v___x_2076_ = v___x_2071_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(3, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_id_2066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_message_2068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 2, v___y_2074_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2078_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_code_2067_,
                    );
                    v___x_2076_ = v_reuseFailAlloc_2078_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2077_ = l_IO_FS_Stream_writeLspMessage(v_h_2063_, v___x_2076_);
                return v___x_2077_;
            }
            4 => {
                v___x_2084_ = crate::leanh::lean_apply_1(v_inst_2062_, v_val_2080_);
                if v_isShared_2083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2084_);
                    v___x_2086_ = v___x_2082_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2074_ = v___x_2086_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(
    mut v_inst_2090_: *mut crate::leanh::LeanObject,
    mut v_h_2091_: *mut crate::leanh::LeanObject,
    mut v_e_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ =
        l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_2090_, v_h_2091_, v_e_2092_);
    return v_res_2094_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData(
    mut v_00_u03b1_2095_: *mut crate::leanh::LeanObject,
    mut v_inst_2096_: *mut crate::leanh::LeanObject,
    mut v_h_2097_: *mut crate::leanh::LeanObject,
    mut v_e_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ =
        l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_2096_, v_h_2097_, v_e_2098_);
    return v___x_2100_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(
    mut v_00_u03b1_2101_: *mut crate::leanh::LeanObject,
    mut v_inst_2102_: *mut crate::leanh::LeanObject,
    mut v_h_2103_: *mut crate::leanh::LeanObject,
    mut v_e_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_IO_FS_Stream_writeLspResponseErrorWithData(
        v_00_u03b1_2101_,
        v_inst_2102_,
        v_h_2103_,
        v_e_2104_,
    );
    return v_res_2106_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Communication(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Communication(
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
pub unsafe fn initialize_Lean_Data_Lsp_Communication(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_JsonRpc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Communication(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Communication(builtin);
}
