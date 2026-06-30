// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: Lean.Data.JsonRpc Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.Iterators.Consumers.Collect
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_array_to_list, lean_int_neg, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_string_append, lean_string_dec_eq, lean_string_get_byte_fast, lean_string_push,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_next_fast,
    lean_uint8_dec_eq,
};
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
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2: u8 = 0;
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [13, 10, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 101, 113, 95, 110, 117, 109, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 104, 101, 97, 100, 101, 114, 32, 102, 105, 101, 108, 100, 58, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value: leanh::LeanStringObject<176> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 176, m_capacity: 176, m_length: 175, m_data: [65, 32, 76, 101, 97, 110, 32, 51, 32, 114, 101, 113, 117, 101, 115, 116, 32, 119, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 46, 32, 80, 108, 101, 97, 115, 101, 32, 101, 110, 115, 117, 114, 101, 32, 116, 104, 97, 116, 32, 121, 111, 117, 114, 32, 101, 100, 105, 116, 111, 114, 32, 104, 97, 115, 32, 97, 32, 76, 101, 97, 110, 32, 52, 32, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 105, 110, 115, 116, 97, 108, 108, 101, 100, 46, 32, 70, 111, 114, 32, 86, 83, 67, 111, 100, 101, 44, 32, 116, 104, 105, 115, 32, 105, 115, 10, 10, 32, 32, 32, 32, 104, 116, 116, 112, 115, 58, 47, 47, 103, 105, 116, 104, 117, 98, 46, 99, 111, 109, 47, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 118, 115, 99, 111, 100, 101, 45, 108, 101, 97, 110, 52, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 116, 114, 101, 97, 109, 32, 119, 97, 115, 32, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [78, 111, 32, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 32, 102, 105, 101, 108, 100, 32, 105, 110, 32, 104, 101, 97, 100, 101, 114, 58, 32, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 32, 104, 101, 97, 100, 101, 114, 32, 102, 105, 101, 108, 100, 32, 118, 97, 108, 117, 101, 32, 39, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [39, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 78, 97, 116, 0]};
static mut l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value
) as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_readLspMessage___closed__0_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_readLspMessage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspMessage___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_readLspRequestAs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_readLspResponseAs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeSerializedLspMessage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeSerializedLspMessage___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__5_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__6_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__7_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__8_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__9_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_IO_FS_Stream_writeLspMessage___closed__11_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_IO_FS_Stream_writeLspMessage___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_writeLspMessage___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_IO_FS_Stream_writeLspMessage___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__43_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__43: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__46_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__46: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__48_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__48: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__49_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__49: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__50_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__50: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__51_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__51: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__52_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__52: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__53_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__53: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__54_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__54: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__55_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__55: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__56_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__56: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__57_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__57: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__58_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__58: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_Stream_writeLspMessage___closed__59_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_Stream_writeLspMessage___closed__59: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
    v___x_1056_ = lean_string_utf8_byte_size(v___x_1055_);
    return v___x_1056_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2()
-> u8 {
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
    v___x_1057_ = leanh::lean_unsigned_to_nat(0);
    v___x_1058_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
    v___x_1059_ = lean_nat_dec_eq(v___x_1058_, v___x_1057_);
    return v___x_1059_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
    v___x_1061_ = leanh::lean_unsigned_to_nat(0);
    v___x_1062_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
    v___x_1063_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1063_, 0, v___x_1062_);
    leanh::lean_ctor_set(v___x_1063_, 1, v___x_1061_);
    leanh::lean_ctor_set(v___x_1063_, 2, v___x_1060_);
    return v___x_1063_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
    v___x_1065_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = leanh::lean_unsigned_to_nat(0);
    v___x_1067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4);
    v___x_1068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
    v___x_1069_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    leanh::lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    leanh::lean_ctor_set(v___x_1069_, 2, v___x_1066_);
    leanh::lean_ctor_set(v___x_1069_, 3, v___x_1066_);
    return v___x_1069_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5);
    v___x_1071_ = leanh::lean_unsigned_to_nat(0);
    v___x_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
    leanh::lean_ctor_set(v___x_1072_, 1, v___x_1070_);
    return v___x_1072_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(
    mut v_s_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1079_: u8 = 0;
    v___x_1079_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2);
    if v___x_1079_ == 0 {
        let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1080_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6);
        return v___x_1080_;
    } else {
        let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1081_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8;
        return v___x_1081_;
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(
    mut v_s_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v_s_1082_);
    leanh::lean_dec_ref(v_s_1082_);
    return v_res_1083_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(
    mut v_s_1084_: *mut leanh::LeanObject,
    mut v___x_1085_: *mut leanh::LeanObject,
    mut v___x_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_b_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v_it_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v_nextIt_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1126_: u8 = 0;
    let mut v_startInclusive_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v_pos_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1144_: u8 = 0;
    let mut v_needle_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v_str_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1161_: u8 = 0;
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1087_) == 0 {
                    v_currPos_1096_ = leanh::lean_ctor_get(v_a_1087_, 0);
                    v_searcher_1097_ = leanh::lean_ctor_get(v_a_1087_, 1);
                    v_isSharedCheck_1201_ = (!leanh::lean_is_exclusive(v_a_1087_)) as u8;
                    if v_isSharedCheck_1201_ == 0 {
                        v___x_1099_ = v_a_1087_;
                        v_isShared_1100_ = v_isSharedCheck_1201_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1097_);
                        leanh::lean_inc(v_currPos_1096_);
                        leanh::lean_dec(v_a_1087_);
                        v___x_1099_ = leanh::lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1201_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1086_);
                    leanh::lean_dec_ref(v_s_1084_);
                    return v_b_1088_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_s_1084_);
                v___x_1093_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1093_, 0, v_s_1084_);
                leanh::lean_ctor_set(v___x_1093_, 1, v_startInclusive_1091_);
                leanh::lean_ctor_set(v___x_1093_, 2, v_endExclusive_1092_);
                v___x_1094_ = lean_array_push(v_b_1088_, v___x_1093_);
                v_a_1087_ = v_it_1090_;
                v_b_1088_ = v___x_1094_;
                state = 0;
                continue;
            }
            2 => match leanh::lean_obj_tag(v_searcher_1097_) {
                0 => {
                    leanh::lean_del_object(v___x_1099_);
                    v_pos_1123_ = leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_isSharedCheck_1135_ =
                        (!leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1135_ == 0 {
                        v___x_1125_ = v_searcher_1097_;
                        v_isShared_1126_ = v_isSharedCheck_1135_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1123_);
                        leanh::lean_dec(v_searcher_1097_);
                        v___x_1125_ = leanh::lean_box(0);
                        v_isShared_1126_ = v_isSharedCheck_1135_;
                        state = 9;
                        continue;
                    }
                }
                1 => {
                    v_pos_1136_ = leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_isSharedCheck_1144_ =
                        (!leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1144_ == 0 {
                        v___x_1138_ = v_searcher_1097_;
                        v_isShared_1139_ = v_isSharedCheck_1144_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1136_);
                        leanh::lean_dec(v_searcher_1097_);
                        v___x_1138_ = leanh::lean_box(0);
                        v_isShared_1139_ = v_isSharedCheck_1144_;
                        state = 11;
                        continue;
                    }
                }
                2 => {
                    v_needle_1145_ = leanh::lean_ctor_get(v_searcher_1097_, 0);
                    v_table_1146_ = leanh::lean_ctor_get(v_searcher_1097_, 1);
                    v_stackPos_1147_ = leanh::lean_ctor_get(v_searcher_1097_, 2);
                    v_needlePos_1148_ = leanh::lean_ctor_get(v_searcher_1097_, 3);
                    v_isSharedCheck_1200_ =
                        (!leanh::lean_is_exclusive(v_searcher_1097_)) as u8;
                    if v_isSharedCheck_1200_ == 0 {
                        v___x_1150_ = v_searcher_1097_;
                        v_isShared_1151_ = v_isSharedCheck_1200_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_needlePos_1148_);
                        leanh::lean_inc(v_stackPos_1147_);
                        leanh::lean_inc(v_table_1146_);
                        leanh::lean_inc(v_needle_1145_);
                        leanh::lean_dec(v_searcher_1097_);
                        v___x_1150_ = leanh::lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1200_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_1099_);
                    state = 8;
                    continue;
                }
            },
            3 => {
                if v_isShared_1100_ == 0 {
                    leanh::lean_ctor_set(v___x_1099_, 1, v_it_1102_);
                    v___x_1104_ = v___x_1099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_currPos_1096_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_it_1102_);
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
                v_startInclusive_1112_ = leanh::lean_ctor_get(v_slice_1111_, 0);
                v_endExclusive_1113_ = leanh::lean_ctor_get(v_slice_1111_, 1);
                v_isSharedCheck_1120_ = (!leanh::lean_is_exclusive(v_slice_1111_)) as u8;
                if v_isSharedCheck_1120_ == 0 {
                    v___x_1115_ = v_slice_1111_;
                    v_isShared_1116_ = v_isSharedCheck_1120_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1113_);
                    leanh::lean_inc(v_startInclusive_1112_);
                    leanh::lean_dec(v_slice_1111_);
                    v___x_1115_ = leanh::lean_box(0);
                    v_isShared_1116_ = v_isSharedCheck_1120_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1116_ == 0 {
                    leanh::lean_ctor_set(v___x_1115_, 1, v_it_1108_);
                    leanh::lean_ctor_set(v___x_1115_, 0, v_endPos_1110_);
                    v_nextIt_1118_ = v___x_1115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_endPos_1110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_it_1108_);
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
                v___x_1122_ = leanh::lean_box(1);
                leanh::lean_inc(v___x_1086_);
                v_it_1090_ = v___x_1122_;
                v_startInclusive_1091_ = v_currPos_1096_;
                v_endExclusive_1092_ = v___x_1086_;
                state = 1;
                continue;
            }
            9 => {
                v_startInclusive_1127_ = leanh::lean_ctor_get(v___x_1085_, 1);
                v_endExclusive_1128_ = leanh::lean_ctor_get(v___x_1085_, 2);
                v___x_1129_ = lean_nat_sub(v_endExclusive_1128_, v_startInclusive_1127_);
                v___x_1130_ = lean_nat_dec_eq(v_pos_1123_, v___x_1129_);
                leanh::lean_dec(v___x_1129_);
                if v___x_1130_ == 0 {
                    leanh::lean_inc(v_pos_1123_);
                    if v_isShared_1126_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1125_, 1);
                        v___x_1132_ = v___x_1125_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_pos_1123_);
                        v___x_1132_ = v_reuseFailAlloc_1133_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1125_);
                    v___x_1134_ = leanh::lean_box(3);
                    leanh::lean_inc(v_pos_1123_);
                    v_it_1108_ = v___x_1134_;
                    v_startPos_1109_ = v_pos_1123_;
                    v_endPos_1110_ = v_pos_1123_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc(v_pos_1123_);
                v_it_1108_ = v___x_1132_;
                v_startPos_1109_ = v_pos_1123_;
                v_endPos_1110_ = v_pos_1123_;
                state = 5;
                continue;
            }
            11 => {
                v___x_1140_ = lean_string_utf8_next_fast(v_s_1084_, v_pos_1136_);
                leanh::lean_dec(v_pos_1136_);
                if v_isShared_1139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1138_, 0);
                    leanh::lean_ctor_set(v___x_1138_, 0, v___x_1140_);
                    v___x_1142_ = v___x_1138_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
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
                v_str_1152_ = leanh::lean_ctor_get(v_needle_1145_, 0);
                v_startInclusive_1153_ = leanh::lean_ctor_get(v_needle_1145_, 1);
                v_endExclusive_1154_ = leanh::lean_ctor_get(v_needle_1145_, 2);
                v_basePos_1155_ = lean_nat_sub(v_stackPos_1147_, v_needlePos_1148_);
                v___x_1156_ = lean_nat_sub(v_endExclusive_1154_, v_startInclusive_1153_);
                v___x_1157_ = lean_nat_add(v_basePos_1155_, v___x_1156_);
                v___x_1158_ = lean_nat_dec_le(v___x_1157_, v___x_1086_);
                leanh::lean_dec(v___x_1157_);
                if v___x_1158_ == 0 {
                    leanh::lean_dec(v___x_1156_);
                    leanh::lean_del_object(v___x_1150_);
                    leanh::lean_dec(v_needlePos_1148_);
                    leanh::lean_dec(v_stackPos_1147_);
                    leanh::lean_dec_ref(v_table_1146_);
                    leanh::lean_dec_ref(v_needle_1145_);
                    v___x_1159_ = lean_nat_dec_lt(v_basePos_1155_, v___x_1086_);
                    leanh::lean_dec(v_basePos_1155_);
                    if v___x_1159_ == 0 {
                        leanh::lean_del_object(v___x_1099_);
                        state = 8;
                        continue;
                    } else {
                        v___x_1160_ = leanh::lean_box(3);
                        v_it_1102_ = v___x_1160_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_basePos_1155_);
                    leanh::lean_inc(v_stackPos_1147_);
                    v_stackByte_1161_ = lean_string_get_byte_fast(v_s_1084_, v_stackPos_1147_);
                    v___x_1162_ = lean_nat_add(v_startInclusive_1153_, v_needlePos_1148_);
                    v_patByte_1163_ = lean_string_get_byte_fast(v_str_1152_, v___x_1162_);
                    v___x_1164_ = lean_uint8_dec_eq(v_stackByte_1161_, v_patByte_1163_);
                    if v___x_1164_ == 0 {
                        leanh::lean_dec(v___x_1156_);
                        v___x_1165_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1166_ = lean_nat_dec_eq(v_needlePos_1148_, v___x_1165_);
                        if v___x_1166_ == 0 {
                            v___x_1167_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1168_ = lean_nat_sub(v_needlePos_1148_, v___x_1167_);
                            leanh::lean_dec(v_needlePos_1148_);
                            v_newNeedlePos_1169_ =
                                lean_array_fget_borrowed(v_table_1146_, v___x_1168_);
                            leanh::lean_dec(v___x_1168_);
                            v___x_1170_ = lean_nat_dec_eq(v_newNeedlePos_1169_, v___x_1165_);
                            if v___x_1170_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_1169_);
                                if v_isShared_1151_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_1150_,
                                        3,
                                        v_newNeedlePos_1169_,
                                    );
                                    v___x_1172_ = v___x_1150_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1173_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        0,
                                        v_needle_1145_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        1,
                                        v_table_1146_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1173_,
                                        2,
                                        v_stackPos_1147_,
                                    );
                                    leanh::lean_ctor_set(
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
                                    leanh::lean_ctor_set(v___x_1150_, 3, v___x_1165_);
                                    leanh::lean_ctor_set(
                                        v___x_1150_,
                                        2,
                                        v_nextStackPos_1174_,
                                    );
                                    v___x_1176_ = v___x_1150_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1177_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        0,
                                        v_needle_1145_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        1,
                                        v_table_1146_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1177_,
                                        2,
                                        v_nextStackPos_1174_,
                                    );
                                    leanh::lean_ctor_set(
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
                            leanh::lean_dec(v_needlePos_1148_);
                            v___x_1178_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1179_ = lean_nat_add(v_stackPos_1147_, v___x_1178_);
                            leanh::lean_dec(v_stackPos_1147_);
                            v_nextStackPos_1180_ =
                                l_String_Slice_posGE___redArg(v___x_1085_, v___x_1179_);
                            if v_isShared_1151_ == 0 {
                                leanh::lean_ctor_set(v___x_1150_, 3, v___x_1165_);
                                leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1180_);
                                v___x_1182_ = v___x_1150_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1183_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    0,
                                    v_needle_1145_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    1,
                                    v_table_1146_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1183_,
                                    2,
                                    v_nextStackPos_1180_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___x_1165_);
                                v___x_1182_ = v_reuseFailAlloc_1183_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1099_);
                        v___x_1184_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1185_ = lean_nat_add(v_stackPos_1147_, v___x_1184_);
                        leanh::lean_dec(v_stackPos_1147_);
                        v_nextNeedlePos_1186_ = lean_nat_add(v_needlePos_1148_, v___x_1184_);
                        leanh::lean_dec(v_needlePos_1148_);
                        v___x_1187_ = lean_nat_dec_eq(v_nextNeedlePos_1186_, v___x_1156_);
                        leanh::lean_dec(v___x_1156_);
                        if v___x_1187_ == 0 {
                            if v_isShared_1151_ == 0 {
                                leanh::lean_ctor_set(v___x_1150_, 3, v_nextNeedlePos_1186_);
                                leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1185_);
                                v___x_1189_ = v___x_1150_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_1192_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    0,
                                    v_needle_1145_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    1,
                                    v_table_1146_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1192_,
                                    2,
                                    v_nextStackPos_1185_,
                                );
                                leanh::lean_ctor_set(
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
                            leanh::lean_dec(v_nextNeedlePos_1186_);
                            v___x_1194_ = l_String_Slice_pos_x21(v___x_1085_, v___x_1193_);
                            leanh::lean_dec(v___x_1193_);
                            v___x_1195_ = l_String_Slice_pos_x21(v___x_1085_, v_nextStackPos_1185_);
                            v___x_1196_ = leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1151_ == 0 {
                                leanh::lean_ctor_set(v___x_1150_, 3, v___x_1196_);
                                leanh::lean_ctor_set(v___x_1150_, 2, v_nextStackPos_1185_);
                                v___x_1198_ = v___x_1150_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_1199_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    0,
                                    v_needle_1145_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    1,
                                    v_table_1146_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1199_,
                                    2,
                                    v_nextStackPos_1185_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 3, v___x_1196_);
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
                v___x_1190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1190_, 0, v_currPos_1096_);
                leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
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
    mut v_s_1202_: *mut leanh::LeanObject,
    mut v___x_1203_: *mut leanh::LeanObject,
    mut v___x_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_b_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1202_, v___x_1203_, v___x_1204_, v_a_1205_, v_b_1206_);
    leanh::lean_dec_ref(v___x_1203_);
    return v_res_1207_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
    v___x_1211_ = lean_string_utf8_byte_size(v___x_1210_);
    return v___x_1211_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
    v___x_1213_ = leanh::lean_unsigned_to_nat(0);
    v___x_1214_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
    v___x_1215_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
    leanh::lean_ctor_set(v___x_1215_, 1, v___x_1213_);
    leanh::lean_ctor_set(v___x_1215_, 2, v___x_1212_);
    return v___x_1215_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(
    mut v_s_1218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_unused_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1219_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
                v___x_1220_ = lean_string_dec_eq(v_s_1218_, v___x_1219_);
                if v___x_1220_ == 0 {
                    v___x_1221_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1222_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1223_ = lean_string_utf8_byte_size(v_s_1218_);
                    leanh::lean_inc_ref_n(v_s_1218_, 2);
                    v___x_1224_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1224_, 0, v_s_1218_);
                    leanh::lean_ctor_set(v___x_1224_, 1, v___x_1222_);
                    leanh::lean_ctor_set(v___x_1224_, 2, v___x_1223_);
                    v___x_1225_ = l_String_Slice_Pos_prevn(v___x_1224_, v___x_1223_, v___x_1221_);
                    leanh::lean_dec_ref_known(v___x_1224_, 3);
                    leanh::lean_inc(v___x_1225_);
                    v___x_1226_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1226_, 0, v_s_1218_);
                    leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
                    leanh::lean_ctor_set(v___x_1226_, 2, v___x_1223_);
                    v___x_1227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
                    v___x_1228_ = l_String_Slice_beq(v___x_1226_, v___x_1227_);
                    leanh::lean_dec_ref_known(v___x_1226_, 3);
                    if v___x_1228_ == 0 {
                        leanh::lean_dec(v___x_1225_);
                        leanh::lean_dec_ref(v_s_1218_);
                        v___x_1229_ = leanh::lean_box(0);
                        return v___x_1229_;
                    } else {
                        leanh::lean_inc(v___x_1225_);
                        leanh::lean_inc_ref(v_s_1218_);
                        v___x_1230_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1230_, 0, v_s_1218_);
                        leanh::lean_ctor_set(v___x_1230_, 1, v___x_1222_);
                        leanh::lean_ctor_set(v___x_1230_, 2, v___x_1225_);
                        v___x_1231_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v___x_1230_);
                        v___x_1232_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
                        v___x_1233_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1218_, v___x_1230_, v___x_1225_, v___x_1231_, v___x_1232_);
                        leanh::lean_dec_ref_known(v___x_1230_, 3);
                        v___x_1234_ = lean_array_to_list(v___x_1233_);
                        if leanh::lean_obj_tag(v___x_1234_) == 0 {
                            v___x_1235_ = leanh::lean_box(0);
                            return v___x_1235_;
                        } else {
                            v_tail_1236_ = leanh::lean_ctor_get(v___x_1234_, 1);
                            leanh::lean_inc(v_tail_1236_);
                            if leanh::lean_obj_tag(v_tail_1236_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1234_, 2);
                                v___x_1237_ = leanh::lean_box(0);
                                return v___x_1237_;
                            } else {
                                v_head_1238_ = leanh::lean_ctor_get(v___x_1234_, 0);
                                leanh::lean_inc(v_head_1238_);
                                leanh::lean_dec_ref_known(v___x_1234_, 2);
                                v_str_1239_ = leanh::lean_ctor_get(v_head_1238_, 0);
                                leanh::lean_inc_ref(v_str_1239_);
                                v_startInclusive_1240_ =
                                    leanh::lean_ctor_get(v_head_1238_, 1);
                                leanh::lean_inc(v_startInclusive_1240_);
                                v_endExclusive_1241_ = leanh::lean_ctor_get(v_head_1238_, 2);
                                leanh::lean_inc(v_endExclusive_1241_);
                                leanh::lean_dec(v_head_1238_);
                                v___x_1242_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
                                v___x_1243_ = l_String_Slice_intercalate(v___x_1242_, v_tail_1236_);
                                v_isSharedCheck_1252_ =
                                    (!leanh::lean_is_exclusive(v_tail_1236_)) as u8;
                                if v_isSharedCheck_1252_ == 0 {
                                    v_unused_1253_ = leanh::lean_ctor_get(v_tail_1236_, 1);
                                    leanh::lean_dec(v_unused_1253_);
                                    v_unused_1254_ = leanh::lean_ctor_get(v_tail_1236_, 0);
                                    leanh::lean_dec(v_unused_1254_);
                                    v___x_1245_ = v_tail_1236_;
                                    v_isShared_1246_ = v_isSharedCheck_1252_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_tail_1236_);
                                    v___x_1245_ = leanh::lean_box(0);
                                    v_isShared_1246_ = v_isSharedCheck_1252_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_s_1218_);
                    v___x_1255_ = leanh::lean_box(0);
                    return v___x_1255_;
                }
            }
            1 => {
                v___x_1247_ = lean_string_utf8_extract(
                    v_str_1239_,
                    v_startInclusive_1240_,
                    v_endExclusive_1241_,
                );
                leanh::lean_dec(v_endExclusive_1241_);
                leanh::lean_dec(v_startInclusive_1240_);
                leanh::lean_dec_ref(v_str_1239_);
                if v_isShared_1246_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1245_, 0);
                    leanh::lean_ctor_set(v___x_1245_, 1, v___x_1243_);
                    leanh::lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1243_);
                    v___x_1249_ = v_reuseFailAlloc_1251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(
    mut v_s_1256_: *mut leanh::LeanObject,
    mut v___x_1257_: *mut leanh::LeanObject,
    mut v___x_1258_: *mut leanh::LeanObject,
    mut v_inst_1259_: *mut leanh::LeanObject,
    mut v_R_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
    mut v_b_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_1256_, v___x_1257_, v___x_1258_, v_a_1261_, v_b_1262_);
    return v___x_1263_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(
    mut v_s_1264_: *mut leanh::LeanObject,
    mut v___x_1265_: *mut leanh::LeanObject,
    mut v___x_1266_: *mut leanh::LeanObject,
    mut v_inst_1267_: *mut leanh::LeanObject,
    mut v_R_1268_: *mut leanh::LeanObject,
    mut v_a_1269_: *mut leanh::LeanObject,
    mut v_b_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(v_s_1264_, v___x_1265_, v___x_1266_, v_inst_1267_, v_R_1268_, v_a_1269_, v_b_1270_);
    leanh::lean_dec_ref(v___x_1265_);
    return v_res_1271_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(
    mut v_s_1274_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Json_parse(v_s_1274_);
    if leanh::lean_obj_tag(v___x_1275_) == 0 {
        let mut v___x_1276_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_1275_, 1);
        v___x_1276_ = 0;
        return v___x_1276_;
    } else {
        let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1277_ = leanh::lean_ctor_get(v___x_1275_, 0);
        leanh::lean_inc_n(v_a_1277_, 2);
        leanh::lean_dec_ref_known(v___x_1275_, 1);
        v___x_1278_ =
            l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
        v___x_1279_ = l_Lean_Json_getObjVal_x3f(v_a_1277_, v___x_1278_);
        if leanh::lean_obj_tag(v___x_1279_) == 0 {
            let mut v___x_1280_: u8 = 0;
            leanh::lean_dec_ref_known(v___x_1279_, 1);
            leanh::lean_dec(v_a_1277_);
            v___x_1280_ = 0;
            return v___x_1280_;
        } else {
            let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1279_, 1);
            v___x_1281_ =
                l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
            v___x_1282_ = l_Lean_Json_getObjVal_x3f(v_a_1277_, v___x_1281_);
            if leanh::lean_obj_tag(v___x_1282_) == 0 {
                let mut v___x_1283_: u8 = 0;
                leanh::lean_dec_ref_known(v___x_1282_, 1);
                v___x_1283_ = 0;
                return v___x_1283_;
            } else {
                let mut v___x_1284_: u8 = 0;
                leanh::lean_dec_ref_known(v___x_1282_, 1);
                v___x_1284_ = 1;
                return v___x_1284_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(
    mut v_s_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1286_: u8 = 0;
    let mut v_r_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_s_1285_);
    v_r_1287_ = leanh::lean_box((v_res_1286_) as usize);
    return v_r_1287_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
    v___x_1291_ = lean_mk_io_user_error(v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3;
    v___x_1294_ = lean_mk_io_user_error(v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(
    mut v_h_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getLine_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getLine_1297_ = leanh::lean_ctor_get(v_h_1295_, 3);
                leanh::lean_inc_ref(v_getLine_1297_);
                v___x_1298_ =
                    leanh::lean_apply_1(v_getLine_1297_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1298_) == 0 {
                    v_a_1299_ = leanh::lean_ctor_get(v___x_1298_, 0);
                    v_isSharedCheck_1343_ = (!leanh::lean_is_exclusive(v___x_1298_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1301_ = v___x_1298_;
                        v_isShared_1302_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1299_);
                        leanh::lean_dec(v___x_1298_);
                        v___x_1301_ = leanh::lean_box(0);
                        v_isShared_1302_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_h_1295_);
                    v_a_1344_ = leanh::lean_ctor_get(v___x_1298_, 0);
                    v_isSharedCheck_1351_ = (!leanh::lean_is_exclusive(v___x_1298_)) as u8;
                    if v_isSharedCheck_1351_ == 0 {
                        v___x_1346_ = v___x_1298_;
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1344_);
                        leanh::lean_dec(v___x_1298_);
                        v___x_1346_ = leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1303_ = lean_string_utf8_byte_size(v_a_1299_);
                v___x_1304_ = leanh::lean_unsigned_to_nat(0);
                v___x_1305_ = lean_nat_dec_eq(v___x_1303_, v___x_1304_);
                if v___x_1305_ == 0 {
                    v___x_1306_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
                    v___x_1307_ = lean_string_dec_eq(v_a_1299_, v___x_1306_);
                    if v___x_1307_ == 0 {
                        leanh::lean_inc(v_a_1299_);
                        v___x_1308_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(v_a_1299_);
                        if leanh::lean_obj_tag(v___x_1308_) == 0 {
                            leanh::lean_dec_ref(v_h_1295_);
                            leanh::lean_inc(v_a_1299_);
                            v___x_1309_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_a_1299_);
                            if v___x_1309_ == 0 {
                                v___x_1310_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
                                v___x_1311_ = l_String_quote(v_a_1299_);
                                v___x_1312_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
                                v___x_1313_ = l_Std_Format_defWidth;
                                v___x_1314_ = l_Std_Format_pretty(
                                    v___x_1312_,
                                    v___x_1313_,
                                    v___x_1304_,
                                    v___x_1304_,
                                );
                                v___x_1315_ = lean_string_append(v___x_1310_, v___x_1314_);
                                leanh::lean_dec_ref(v___x_1314_);
                                v___x_1316_ = lean_mk_io_user_error(v___x_1315_);
                                if v_isShared_1302_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_1301_, 1);
                                    leanh::lean_ctor_set(v___x_1301_, 0, v___x_1316_);
                                    v___x_1318_ = v___x_1301_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1319_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1319_,
                                        0,
                                        v___x_1316_,
                                    );
                                    v___x_1318_ = v_reuseFailAlloc_1319_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1299_);
                                v___x_1320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
                                if v_isShared_1302_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_1301_, 1);
                                    leanh::lean_ctor_set(v___x_1301_, 0, v___x_1320_);
                                    v___x_1322_ = v___x_1301_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1323_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
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
                            leanh::lean_del_object(v___x_1301_);
                            leanh::lean_dec(v_a_1299_);
                            v_val_1324_ = leanh::lean_ctor_get(v___x_1308_, 0);
                            leanh::lean_inc(v_val_1324_);
                            leanh::lean_dec_ref_known(v___x_1308_, 1);
                            v___x_1325_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_1295_);
                            if leanh::lean_obj_tag(v___x_1325_) == 0 {
                                v_a_1326_ = leanh::lean_ctor_get(v___x_1325_, 0);
                                v_isSharedCheck_1334_ =
                                    (!leanh::lean_is_exclusive(v___x_1325_)) as u8;
                                if v_isSharedCheck_1334_ == 0 {
                                    v___x_1328_ = v___x_1325_;
                                    v_isShared_1329_ = v_isSharedCheck_1334_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1326_);
                                    leanh::lean_dec(v___x_1325_);
                                    v___x_1328_ = leanh::lean_box(0);
                                    v_isShared_1329_ = v_isSharedCheck_1334_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_1324_);
                                return v___x_1325_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1299_);
                        leanh::lean_dec_ref(v_h_1295_);
                        v___x_1335_ = leanh::lean_box(0);
                        if v_isShared_1302_ == 0 {
                            leanh::lean_ctor_set(v___x_1301_, 0, v___x_1335_);
                            v___x_1337_ = v___x_1301_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1338_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
                            v___x_1337_ = v_reuseFailAlloc_1338_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1299_);
                    leanh::lean_dec_ref(v_h_1295_);
                    v___x_1339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once), _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4);
                    if v_isShared_1302_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1301_, 1);
                        leanh::lean_ctor_set(v___x_1301_, 0, v___x_1339_);
                        v___x_1341_ = v___x_1301_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
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
                v___x_1330_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1330_, 0, v_val_1324_);
                leanh::lean_ctor_set(v___x_1330_, 1, v_a_1326_);
                if v_isShared_1329_ == 0 {
                    leanh::lean_ctor_set(v___x_1328_, 0, v___x_1330_);
                    v___x_1332_ = v___x_1328_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
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
                    v_reuseFailAlloc_1350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
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
    mut v_h_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_1352_);
    return v_res_1354_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(
    mut v_x_1358_: *mut leanh::LeanObject,
    mut v_x_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1359_) == 0 {
                    return v_x_1358_;
                } else {
                    v_head_1360_ = leanh::lean_ctor_get(v_x_1359_, 0);
                    v_tail_1361_ = leanh::lean_ctor_get(v_x_1359_, 1);
                    v_fst_1362_ = leanh::lean_ctor_get(v_head_1360_, 0);
                    v_snd_1363_ = leanh::lean_ctor_get(v_head_1360_, 1);
                    v___x_1364_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
                    v___x_1365_ = lean_string_append(v_x_1358_, v___x_1364_);
                    v___x_1366_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
                    v___x_1367_ = lean_string_append(v___x_1366_, v_fst_1362_);
                    v___x_1368_ = lean_string_append(v___x_1367_, v___x_1364_);
                    v___x_1369_ = lean_string_append(v___x_1368_, v_snd_1363_);
                    v___x_1370_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
                    v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
                    v___x_1372_ = lean_string_append(v___x_1365_, v___x_1371_);
                    leanh::lean_dec_ref(v___x_1371_);
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
    mut v_x_1374_: *mut leanh::LeanObject,
    mut v_x_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_1374_, v_x_1375_);
    leanh::lean_dec(v_x_1375_);
    return v_res_1376_;
}
pub unsafe fn l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(
    mut v_x_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1380_) == 0 {
        let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1381_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
        return v___x_1381_;
    } else {
        let mut v_tail_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1382_ = leanh::lean_ctor_get(v_x_1380_, 1);
        if leanh::lean_obj_tag(v_tail_1382_) == 0 {
            let mut v_head_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1383_ = leanh::lean_ctor_get(v_x_1380_, 0);
            v_fst_1384_ = leanh::lean_ctor_get(v_head_1383_, 0);
            v_snd_1385_ = leanh::lean_ctor_get(v_head_1383_, 1);
            v___x_1386_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
            v___x_1387_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
            v___x_1388_ = lean_string_append(v___x_1387_, v_fst_1384_);
            v___x_1389_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
            v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
            v___x_1391_ = lean_string_append(v___x_1390_, v_snd_1385_);
            v___x_1392_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
            v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
            v___x_1394_ = lean_string_append(v___x_1386_, v___x_1393_);
            leanh::lean_dec_ref(v___x_1393_);
            v___x_1395_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
            v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
            return v___x_1396_;
        } else {
            let mut v_head_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1410_: u32 = 0;
            let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1397_ = leanh::lean_ctor_get(v_x_1380_, 0);
            v_fst_1398_ = leanh::lean_ctor_get(v_head_1397_, 0);
            v_snd_1399_ = leanh::lean_ctor_get(v_head_1397_, 1);
            v___x_1400_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
            v___x_1401_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
            v___x_1402_ = lean_string_append(v___x_1401_, v_fst_1398_);
            v___x_1403_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
            v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
            v___x_1405_ = lean_string_append(v___x_1404_, v_snd_1399_);
            v___x_1406_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
            v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
            v___x_1408_ = lean_string_append(v___x_1400_, v___x_1407_);
            leanh::lean_dec_ref(v___x_1407_);
            v___x_1409_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_1408_, v_tail_1382_);
            v___x_1410_ = 93;
            v___x_1411_ = lean_string_push(v___x_1409_, v___x_1410_);
            return v___x_1411_;
        }
    }
}
pub unsafe fn l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(
    mut v_x_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_x_1412_);
    leanh::lean_dec(v_x_1412_);
    return v_res_1413_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(
    mut v_x_1414_: *mut leanh::LeanObject,
    mut v_x_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1415_) == 0 {
                    v___x_1416_ = leanh::lean_box(0);
                    return v___x_1416_;
                } else {
                    v_head_1417_ = leanh::lean_ctor_get(v_x_1415_, 0);
                    v_tail_1418_ = leanh::lean_ctor_get(v_x_1415_, 1);
                    v_fst_1419_ = leanh::lean_ctor_get(v_head_1417_, 0);
                    v_snd_1420_ = leanh::lean_ctor_get(v_head_1417_, 1);
                    v___x_1421_ = lean_string_dec_eq(v_x_1414_, v_fst_1419_);
                    if v___x_1421_ == 0 {
                        v_x_1415_ = v_tail_1418_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1420_);
                        v___x_1423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1423_, 0, v_snd_1420_);
                        return v___x_1423_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(
    mut v_x_1424_: *mut leanh::LeanObject,
    mut v_x_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_1424_, v_x_1425_);
    leanh::lean_dec(v_x_1425_);
    leanh::lean_dec_ref(v_x_1424_);
    return v_res_1426_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
    mut v_h_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_a_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1433_ =
                    l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(
                        v_h_1431_,
                    );
                if leanh::lean_obj_tag(v___x_1433_) == 0 {
                    v_a_1434_ = leanh::lean_ctor_get(v___x_1433_, 0);
                    v_isSharedCheck_1464_ = (!leanh::lean_is_exclusive(v___x_1433_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1436_ = v___x_1433_;
                        v_isShared_1437_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1434_);
                        leanh::lean_dec(v___x_1433_);
                        v___x_1436_ = leanh::lean_box(0);
                        v_isShared_1437_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1465_ = leanh::lean_ctor_get(v___x_1433_, 0);
                    v_isSharedCheck_1472_ = (!leanh::lean_is_exclusive(v___x_1433_)) as u8;
                    if v_isSharedCheck_1472_ == 0 {
                        v___x_1467_ = v___x_1433_;
                        v_isShared_1468_ = v_isSharedCheck_1472_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1465_);
                        leanh::lean_dec(v___x_1433_);
                        v___x_1467_ = leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1472_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1438_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
                v___x_1439_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_1438_, v_a_1434_);
                if leanh::lean_obj_tag(v___x_1439_) == 0 {
                    v___x_1440_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
                    v___x_1441_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_a_1434_);
                    leanh::lean_dec(v_a_1434_);
                    v___x_1442_ = lean_string_append(v___x_1440_, v___x_1441_);
                    leanh::lean_dec_ref(v___x_1441_);
                    v___x_1443_ = lean_mk_io_user_error(v___x_1442_);
                    if v_isShared_1437_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1436_, 1);
                        leanh::lean_ctor_set(v___x_1436_, 0, v___x_1443_);
                        v___x_1445_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
                        v___x_1445_ = v_reuseFailAlloc_1446_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1434_);
                    v_val_1447_ = leanh::lean_ctor_get(v___x_1439_, 0);
                    leanh::lean_inc_n(v_val_1447_, 2);
                    leanh::lean_dec_ref_known(v___x_1439_, 1);
                    v___x_1448_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1449_ = lean_string_utf8_byte_size(v_val_1447_);
                    v___x_1450_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1450_, 0, v_val_1447_);
                    leanh::lean_ctor_set(v___x_1450_, 1, v___x_1448_);
                    leanh::lean_ctor_set(v___x_1450_, 2, v___x_1449_);
                    v___x_1451_ = l_String_Slice_toNat_x3f(v___x_1450_);
                    leanh::lean_dec_ref_known(v___x_1450_, 3);
                    if leanh::lean_obj_tag(v___x_1451_) == 0 {
                        v___x_1452_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
                        v___x_1453_ = lean_string_append(v___x_1452_, v_val_1447_);
                        leanh::lean_dec(v_val_1447_);
                        v___x_1454_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
                        v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
                        v___x_1456_ = lean_mk_io_user_error(v___x_1455_);
                        if v_isShared_1437_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1436_, 1);
                            leanh::lean_ctor_set(v___x_1436_, 0, v___x_1456_);
                            v___x_1458_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1459_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
                            v___x_1458_ = v_reuseFailAlloc_1459_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_1447_);
                        v_val_1460_ = leanh::lean_ctor_get(v___x_1451_, 0);
                        leanh::lean_inc(v_val_1460_);
                        leanh::lean_dec_ref_known(v___x_1451_, 1);
                        if v_isShared_1437_ == 0 {
                            leanh::lean_ctor_set(v___x_1436_, 0, v_val_1460_);
                            v___x_1462_ = v___x_1436_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1463_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_val_1460_);
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
                    v_reuseFailAlloc_1471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
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
    mut v_h_1473_: *mut leanh::LeanObject,
    mut v_a_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_1473_);
    return v_res_1475_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(
    mut v_00_u03b2_1476_: *mut leanh::LeanObject,
    mut v_x_1477_: *mut leanh::LeanObject,
    mut v_x_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_1477_, v_x_1478_);
    return v___x_1479_;
}
pub unsafe fn l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(
    mut v_00_u03b2_1480_: *mut leanh::LeanObject,
    mut v_x_1481_: *mut leanh::LeanObject,
    mut v_x_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_1480_, v_x_1481_, v_x_1482_);
    leanh::lean_dec(v_x_1482_);
    leanh::lean_dec_ref(v_x_1481_);
    return v_res_1483_;
}
pub unsafe fn l_IO_FS_Stream_readLspMessage(
    mut v_h_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_1485_);
                v___x_1494_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1485_,
                );
                if leanh::lean_obj_tag(v___x_1494_) == 0 {
                    v_a_1495_ = leanh::lean_ctor_get(v___x_1494_, 0);
                    leanh::lean_inc(v_a_1495_);
                    leanh::lean_dec_ref_known(v___x_1494_, 1);
                    v___x_1496_ = l_IO_FS_Stream_readMessage(v_h_1485_, v_a_1495_);
                    leanh::lean_dec(v_a_1495_);
                    if leanh::lean_obj_tag(v___x_1496_) == 0 {
                        return v___x_1496_;
                    } else {
                        v_a_1497_ = leanh::lean_ctor_get(v___x_1496_, 0);
                        leanh::lean_inc(v_a_1497_);
                        leanh::lean_dec_ref_known(v___x_1496_, 1);
                        v_a_1488_ = v_a_1497_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_h_1485_);
                    v_a_1498_ = leanh::lean_ctor_get(v___x_1494_, 0);
                    leanh::lean_inc(v_a_1498_);
                    leanh::lean_dec_ref_known(v___x_1494_, 1);
                    v_a_1488_ = v_a_1498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1489_ = l_IO_FS_Stream_readLspMessage___closed__0;
                v___x_1490_ = lean_io_error_to_string(v_a_1488_);
                v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
                leanh::lean_dec_ref(v___x_1490_);
                v___x_1492_ = lean_mk_io_user_error(v___x_1491_);
                v___x_1493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1493_, 0, v___x_1492_);
                return v___x_1493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspMessage___boxed(
    mut v_h_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_IO_FS_Stream_readLspMessage(v_h_1499_);
    return v_res_1501_;
}
pub unsafe fn l_IO_FS_Stream_readLspMessageAsString(
    mut v_h_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_1502_);
                v___x_1511_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1502_,
                );
                if leanh::lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    leanh::lean_inc(v_a_1512_);
                    leanh::lean_dec_ref_known(v___x_1511_, 1);
                    v___x_1513_ = l_IO_FS_Stream_readUTF8(v_h_1502_, v_a_1512_);
                    leanh::lean_dec(v_a_1512_);
                    if leanh::lean_obj_tag(v___x_1513_) == 0 {
                        return v___x_1513_;
                    } else {
                        v_a_1514_ = leanh::lean_ctor_get(v___x_1513_, 0);
                        leanh::lean_inc(v_a_1514_);
                        leanh::lean_dec_ref_known(v___x_1513_, 1);
                        v_a_1505_ = v_a_1514_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_h_1502_);
                    v_a_1515_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    leanh::lean_inc(v_a_1515_);
                    leanh::lean_dec_ref_known(v___x_1511_, 1);
                    v_a_1505_ = v_a_1515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1506_ = l_IO_FS_Stream_readLspMessage___closed__0;
                v___x_1507_ = lean_io_error_to_string(v_a_1505_);
                v___x_1508_ = lean_string_append(v___x_1506_, v___x_1507_);
                leanh::lean_dec_ref(v___x_1507_);
                v___x_1509_ = lean_mk_io_user_error(v___x_1508_);
                v___x_1510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
                return v___x_1510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspMessageAsString___boxed(
    mut v_h_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_IO_FS_Stream_readLspMessageAsString(v_h_1516_);
    return v_res_1518_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___redArg(
    mut v_h_1520_: *mut leanh::LeanObject,
    mut v_expectedMethod_1521_: *mut leanh::LeanObject,
    mut v_inst_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_1520_);
                v___x_1531_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1520_,
                );
                if leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    leanh::lean_inc(v_a_1532_);
                    leanh::lean_dec_ref_known(v___x_1531_, 1);
                    v___x_1533_ = l_IO_FS_Stream_readRequestAs___redArg(
                        v_h_1520_,
                        v_a_1532_,
                        v_expectedMethod_1521_,
                        v_inst_1522_,
                    );
                    leanh::lean_dec(v_a_1532_);
                    if leanh::lean_obj_tag(v___x_1533_) == 0 {
                        return v___x_1533_;
                    } else {
                        v_a_1534_ = leanh::lean_ctor_get(v___x_1533_, 0);
                        leanh::lean_inc(v_a_1534_);
                        leanh::lean_dec_ref_known(v___x_1533_, 1);
                        v_a_1525_ = v_a_1534_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1522_);
                    leanh::lean_dec_ref(v_expectedMethod_1521_);
                    leanh::lean_dec_ref(v_h_1520_);
                    v_a_1535_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    leanh::lean_inc(v_a_1535_);
                    leanh::lean_dec_ref_known(v___x_1531_, 1);
                    v_a_1525_ = v_a_1535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1526_ = l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
                v___x_1527_ = lean_io_error_to_string(v_a_1525_);
                v___x_1528_ = lean_string_append(v___x_1526_, v___x_1527_);
                leanh::lean_dec_ref(v___x_1527_);
                v___x_1529_ = lean_mk_io_user_error(v___x_1528_);
                v___x_1530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___redArg___boxed(
    mut v_h_1536_: *mut leanh::LeanObject,
    mut v_expectedMethod_1537_: *mut leanh::LeanObject,
    mut v_inst_1538_: *mut leanh::LeanObject,
    mut v_a_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ =
        l_IO_FS_Stream_readLspRequestAs___redArg(v_h_1536_, v_expectedMethod_1537_, v_inst_1538_);
    return v_res_1540_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs(
    mut v_h_1541_: *mut leanh::LeanObject,
    mut v_expectedMethod_1542_: *mut leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ =
        l_IO_FS_Stream_readLspRequestAs___redArg(v_h_1541_, v_expectedMethod_1542_, v_inst_1544_);
    return v___x_1546_;
}
pub unsafe fn l_IO_FS_Stream_readLspRequestAs___boxed(
    mut v_h_1547_: *mut leanh::LeanObject,
    mut v_expectedMethod_1548_: *mut leanh::LeanObject,
    mut v_00_u03b1_1549_: *mut leanh::LeanObject,
    mut v_inst_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_IO_FS_Stream_readLspRequestAs(
        v_h_1547_,
        v_expectedMethod_1548_,
        v_00_u03b1_1549_,
        v_inst_1550_,
    );
    return v_res_1552_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___redArg(
    mut v_h_1554_: *mut leanh::LeanObject,
    mut v_expectedMethod_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_1554_);
                v___x_1565_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1554_,
                );
                if leanh::lean_obj_tag(v___x_1565_) == 0 {
                    v_a_1566_ = leanh::lean_ctor_get(v___x_1565_, 0);
                    leanh::lean_inc(v_a_1566_);
                    leanh::lean_dec_ref_known(v___x_1565_, 1);
                    v___x_1567_ = l_IO_FS_Stream_readNotificationAs___redArg(
                        v_h_1554_,
                        v_a_1566_,
                        v_expectedMethod_1555_,
                        v_inst_1556_,
                    );
                    leanh::lean_dec(v_a_1566_);
                    if leanh::lean_obj_tag(v___x_1567_) == 0 {
                        return v___x_1567_;
                    } else {
                        v_a_1568_ = leanh::lean_ctor_get(v___x_1567_, 0);
                        leanh::lean_inc(v_a_1568_);
                        leanh::lean_dec_ref_known(v___x_1567_, 1);
                        v_a_1559_ = v_a_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1556_);
                    leanh::lean_dec_ref(v_expectedMethod_1555_);
                    leanh::lean_dec_ref(v_h_1554_);
                    v_a_1569_ = leanh::lean_ctor_get(v___x_1565_, 0);
                    leanh::lean_inc(v_a_1569_);
                    leanh::lean_dec_ref_known(v___x_1565_, 1);
                    v_a_1559_ = v_a_1569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1560_ = l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
                v___x_1561_ = lean_io_error_to_string(v_a_1559_);
                v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
                leanh::lean_dec_ref(v___x_1561_);
                v___x_1563_ = lean_mk_io_user_error(v___x_1562_);
                v___x_1564_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1564_, 0, v___x_1563_);
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(
    mut v_h_1570_: *mut leanh::LeanObject,
    mut v_expectedMethod_1571_: *mut leanh::LeanObject,
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_IO_FS_Stream_readLspNotificationAs___redArg(
        v_h_1570_,
        v_expectedMethod_1571_,
        v_inst_1572_,
    );
    return v_res_1574_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs(
    mut v_h_1575_: *mut leanh::LeanObject,
    mut v_expectedMethod_1576_: *mut leanh::LeanObject,
    mut v_00_u03b1_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_IO_FS_Stream_readLspNotificationAs___redArg(
        v_h_1575_,
        v_expectedMethod_1576_,
        v_inst_1578_,
    );
    return v___x_1580_;
}
pub unsafe fn l_IO_FS_Stream_readLspNotificationAs___boxed(
    mut v_h_1581_: *mut leanh::LeanObject,
    mut v_expectedMethod_1582_: *mut leanh::LeanObject,
    mut v_00_u03b1_1583_: *mut leanh::LeanObject,
    mut v_inst_1584_: *mut leanh::LeanObject,
    mut v_a_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_IO_FS_Stream_readLspNotificationAs(
        v_h_1581_,
        v_expectedMethod_1582_,
        v_00_u03b1_1583_,
        v_inst_1584_,
    );
    return v_res_1586_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___redArg(
    mut v_h_1588_: *mut leanh::LeanObject,
    mut v_expectedID_1589_: *mut leanh::LeanObject,
    mut v_inst_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_1588_);
                v___x_1599_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(
                    v_h_1588_,
                );
                if leanh::lean_obj_tag(v___x_1599_) == 0 {
                    v_a_1600_ = leanh::lean_ctor_get(v___x_1599_, 0);
                    leanh::lean_inc(v_a_1600_);
                    leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v___x_1601_ = l_IO_FS_Stream_readResponseAs___redArg(
                        v_h_1588_,
                        v_a_1600_,
                        v_expectedID_1589_,
                        v_inst_1590_,
                    );
                    leanh::lean_dec(v_a_1600_);
                    if leanh::lean_obj_tag(v___x_1601_) == 0 {
                        return v___x_1601_;
                    } else {
                        v_a_1602_ = leanh::lean_ctor_get(v___x_1601_, 0);
                        leanh::lean_inc(v_a_1602_);
                        leanh::lean_dec_ref_known(v___x_1601_, 1);
                        v_a_1593_ = v_a_1602_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1590_);
                    leanh::lean_dec(v_expectedID_1589_);
                    leanh::lean_dec_ref(v_h_1588_);
                    v_a_1603_ = leanh::lean_ctor_get(v___x_1599_, 0);
                    leanh::lean_inc(v_a_1603_);
                    leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v_a_1593_ = v_a_1603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1594_ = l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
                v___x_1595_ = lean_io_error_to_string(v_a_1593_);
                v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
                leanh::lean_dec_ref(v___x_1595_);
                v___x_1597_ = lean_mk_io_user_error(v___x_1596_);
                v___x_1598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1598_, 0, v___x_1597_);
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___redArg___boxed(
    mut v_h_1604_: *mut leanh::LeanObject,
    mut v_expectedID_1605_: *mut leanh::LeanObject,
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1608_ =
        l_IO_FS_Stream_readLspResponseAs___redArg(v_h_1604_, v_expectedID_1605_, v_inst_1606_);
    return v_res_1608_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs(
    mut v_h_1609_: *mut leanh::LeanObject,
    mut v_expectedID_1610_: *mut leanh::LeanObject,
    mut v_00_u03b1_1611_: *mut leanh::LeanObject,
    mut v_inst_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ =
        l_IO_FS_Stream_readLspResponseAs___redArg(v_h_1609_, v_expectedID_1610_, v_inst_1612_);
    return v___x_1614_;
}
pub unsafe fn l_IO_FS_Stream_readLspResponseAs___boxed(
    mut v_h_1615_: *mut leanh::LeanObject,
    mut v_expectedID_1616_: *mut leanh::LeanObject,
    mut v_00_u03b1_1617_: *mut leanh::LeanObject,
    mut v_inst_1618_: *mut leanh::LeanObject,
    mut v_a_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_IO_FS_Stream_readLspResponseAs(
        v_h_1615_,
        v_expectedID_1616_,
        v_00_u03b1_1617_,
        v_inst_1618_,
    );
    return v_res_1620_;
}
pub unsafe fn l_IO_FS_Stream_writeSerializedLspMessage(
    mut v_h_1623_: *mut leanh::LeanObject,
    mut v_msg_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flush_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_header_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flush_1626_ = leanh::lean_ctor_get(v_h_1623_, 0);
    leanh::lean_inc_ref(v_flush_1626_);
    v_putStr_1627_ = leanh::lean_ctor_get(v_h_1623_, 4);
    leanh::lean_inc_ref(v_putStr_1627_);
    leanh::lean_dec_ref(v_h_1623_);
    v___x_1628_ = l_IO_FS_Stream_writeSerializedLspMessage___closed__0;
    v___x_1629_ = lean_string_utf8_byte_size(v_msg_1624_);
    v___x_1630_ = l_Nat_reprFast(v___x_1629_);
    v___x_1631_ = lean_string_append(v___x_1628_, v___x_1630_);
    leanh::lean_dec_ref(v___x_1630_);
    v___x_1632_ = l_IO_FS_Stream_writeSerializedLspMessage___closed__1;
    v_header_1633_ = lean_string_append(v___x_1631_, v___x_1632_);
    v___x_1634_ = lean_string_append(v_header_1633_, v_msg_1624_);
    v___x_1635_ =
        leanh::lean_apply_2(v_putStr_1627_, v___x_1634_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1635_) == 0 {
        let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1635_, 1);
        v___x_1636_ = leanh::lean_apply_1(v_flush_1626_, leanh::lean_box(0));
        return v___x_1636_;
    } else {
        leanh::lean_dec_ref(v_flush_1626_);
        return v___x_1635_;
    }
}
pub unsafe fn l_IO_FS_Stream_writeSerializedLspMessage___boxed(
    mut v_h_1637_: *mut leanh::LeanObject,
    mut v_msg_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_1637_, v_msg_1638_);
    leanh::lean_dec_ref(v_msg_1638_);
    return v_res_1640_;
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(
    mut v_k_1641_: *mut leanh::LeanObject,
    mut v_x_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1642_) == 0 {
        let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_1641_);
        v___x_1643_ = leanh::lean_box(0);
        return v___x_1643_;
    } else {
        let mut v_val_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1644_ = leanh::lean_ctor_get(v_x_1642_, 0);
        leanh::lean_inc(v_val_1644_);
        leanh::lean_dec_ref_known(v_x_1642_, 1);
        v___x_1645_ = l_Lean_Json_Structured_toJson(v_val_1644_);
        v___x_1646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1646_, 0, v_k_1641_);
        leanh::lean_ctor_set(v___x_1646_, 1, v___x_1645_);
        v___x_1647_ = leanh::lean_box(0);
        v___x_1648_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1648_, 0, v___x_1646_);
        leanh::lean_ctor_set(v___x_1648_, 1, v___x_1647_);
        return v___x_1648_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(
    mut v_k_1649_: *mut leanh::LeanObject,
    mut v_x_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1650_) == 0 {
        let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_1649_);
        v___x_1651_ = leanh::lean_box(0);
        return v___x_1651_;
    } else {
        let mut v_val_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1652_ = leanh::lean_ctor_get(v_x_1650_, 0);
        leanh::lean_inc(v_val_1652_);
        v___x_1653_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1653_, 0, v_k_1649_);
        leanh::lean_ctor_set(v___x_1653_, 1, v_val_1652_);
        v___x_1654_ = leanh::lean_box(0);
        v___x_1655_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1655_, 0, v___x_1653_);
        leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
        return v___x_1655_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(
    mut v_k_1656_: *mut leanh::LeanObject,
    mut v_x_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ =
        l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(v_k_1656_, v_x_1657_);
    leanh::lean_dec(v_x_1657_);
    return v_res_1658_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = leanh::lean_unsigned_to_nat(32700);
    v___x_1675_ = lean_nat_to_int(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__12),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__12_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__12,
    );
    v___x_1677_ = lean_int_neg(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__13),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__13_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__13,
    );
    v___x_1679_ = l_Lean_JsonNumber_fromInt(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__14),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__14_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__14,
    );
    v___x_1681_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = leanh::lean_unsigned_to_nat(32600);
    v___x_1683_ = lean_nat_to_int(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__16),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__16_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__16,
    );
    v___x_1685_ = lean_int_neg(v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__17),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__17_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__17,
    );
    v___x_1687_ = l_Lean_JsonNumber_fromInt(v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__18),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__18_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__18,
    );
    v___x_1689_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = leanh::lean_unsigned_to_nat(32601);
    v___x_1691_ = lean_nat_to_int(v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__20),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__20_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__20,
    );
    v___x_1693_ = lean_int_neg(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__21),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__21_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__21,
    );
    v___x_1695_ = l_Lean_JsonNumber_fromInt(v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__22),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__22_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__22,
    );
    v___x_1697_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = leanh::lean_unsigned_to_nat(32602);
    v___x_1699_ = lean_nat_to_int(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__24),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__24_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__24,
    );
    v___x_1701_ = lean_int_neg(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__25),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__25_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__25,
    );
    v___x_1703_ = l_Lean_JsonNumber_fromInt(v___x_1702_);
    return v___x_1703_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__26),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__26_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__26,
    );
    v___x_1705_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1705_, 0, v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = leanh::lean_unsigned_to_nat(32603);
    v___x_1707_ = lean_nat_to_int(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__28),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__28_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__28,
    );
    v___x_1709_ = lean_int_neg(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__29),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__29_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__29,
    );
    v___x_1711_ = l_Lean_JsonNumber_fromInt(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__31() -> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__30),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__30_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__30,
    );
    v___x_1713_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1713_, 0, v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = leanh::lean_unsigned_to_nat(32002);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__33() -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__32),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__32_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__32,
    );
    v___x_1717_ = lean_int_neg(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__33),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__33_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__33,
    );
    v___x_1719_ = l_Lean_JsonNumber_fromInt(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__35() -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__34),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__34_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__34,
    );
    v___x_1721_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__36() -> *mut leanh::LeanObject {
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = leanh::lean_unsigned_to_nat(32001);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__37() -> *mut leanh::LeanObject {
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__36),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__36_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__36,
    );
    v___x_1725_ = lean_int_neg(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__38() -> *mut leanh::LeanObject {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__37),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__37_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__37,
    );
    v___x_1727_ = l_Lean_JsonNumber_fromInt(v___x_1726_);
    return v___x_1727_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__39() -> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__38),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__38_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__38,
    );
    v___x_1729_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
    return v___x_1729_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__40() -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = leanh::lean_unsigned_to_nat(32801);
    v___x_1731_ = lean_nat_to_int(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__41() -> *mut leanh::LeanObject {
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__40),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__40_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__40,
    );
    v___x_1733_ = lean_int_neg(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__41),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__41_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__41,
    );
    v___x_1735_ = l_Lean_JsonNumber_fromInt(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__43() -> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__42),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__42_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__42,
    );
    v___x_1737_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1737_, 0, v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__44() -> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = leanh::lean_unsigned_to_nat(32800);
    v___x_1739_ = lean_nat_to_int(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__44),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__44_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__44,
    );
    v___x_1741_ = lean_int_neg(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__46() -> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__45),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__45_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__45,
    );
    v___x_1743_ = l_Lean_JsonNumber_fromInt(v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__47() -> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__46),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__46_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__46,
    );
    v___x_1745_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__48() -> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_unsigned_to_nat(32900);
    v___x_1747_ = lean_nat_to_int(v___x_1746_);
    return v___x_1747_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__49() -> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__48),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__48_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__48,
    );
    v___x_1749_ = lean_int_neg(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__50() -> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__49),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__49_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__49,
    );
    v___x_1751_ = l_Lean_JsonNumber_fromInt(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__51() -> *mut leanh::LeanObject {
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__50),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__50_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__50,
    );
    v___x_1753_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1753_, 0, v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__52() -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = leanh::lean_unsigned_to_nat(32901);
    v___x_1755_ = lean_nat_to_int(v___x_1754_);
    return v___x_1755_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__53() -> *mut leanh::LeanObject {
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__52),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__52_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__52,
    );
    v___x_1757_ = lean_int_neg(v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__54() -> *mut leanh::LeanObject {
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__53),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__53_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__53,
    );
    v___x_1759_ = l_Lean_JsonNumber_fromInt(v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__55() -> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__54),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__54_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__54,
    );
    v___x_1761_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__56() -> *mut leanh::LeanObject {
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = leanh::lean_unsigned_to_nat(32902);
    v___x_1763_ = lean_nat_to_int(v___x_1762_);
    return v___x_1763_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__57() -> *mut leanh::LeanObject {
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__56),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__56_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__56,
    );
    v___x_1765_ = lean_int_neg(v___x_1764_);
    return v___x_1765_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__58() -> *mut leanh::LeanObject {
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__57),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__57_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__57,
    );
    v___x_1767_ = l_Lean_JsonNumber_fromInt(v___x_1766_);
    return v___x_1767_;
}
pub unsafe fn _init_l_IO_FS_Stream_writeLspMessage___closed__59() -> *mut leanh::LeanObject {
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__58),
        core::ptr::addr_of_mut!(l_IO_FS_Stream_writeLspMessage___closed__58_once),
        _init_l_IO_FS_Stream_writeLspMessage___closed__58,
    );
    v___x_1769_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn l_IO_FS_Stream_writeLspMessage(
    mut v_h_1770_: *mut leanh::LeanObject,
    mut v_msg_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_n_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_id_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v_n_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_id_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1862_: u8 = 0;
    let mut v_message_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_n_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1773_ = l_IO_FS_Stream_writeLspMessage___closed__3;
                match leanh::lean_obj_tag(v_msg_1771_) {
                    0 => {
                        v_id_1780_ = leanh::lean_ctor_get(v_msg_1771_, 0);
                        leanh::lean_inc(v_id_1780_);
                        v_method_1781_ = leanh::lean_ctor_get(v_msg_1771_, 1);
                        leanh::lean_inc_ref(v_method_1781_);
                        v_params_x3f_1782_ = leanh::lean_ctor_get(v_msg_1771_, 2);
                        leanh::lean_inc(v_params_x3f_1782_);
                        leanh::lean_dec_ref_known(v_msg_1771_, 3);
                        v___x_1783_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                        match leanh::lean_obj_tag(v_id_1780_) {
                            0 => {
                                v_s_1796_ = leanh::lean_ctor_get(v_id_1780_, 0);
                                v_isSharedCheck_1803_ =
                                    (!leanh::lean_is_exclusive(v_id_1780_)) as u8;
                                if v_isSharedCheck_1803_ == 0 {
                                    v___x_1798_ = v_id_1780_;
                                    v_isShared_1799_ = v_isSharedCheck_1803_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_s_1796_);
                                    leanh::lean_dec(v_id_1780_);
                                    v___x_1798_ = leanh::lean_box(0);
                                    v_isShared_1799_ = v_isSharedCheck_1803_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_1804_ = leanh::lean_ctor_get(v_id_1780_, 0);
                                v_isSharedCheck_1811_ =
                                    (!leanh::lean_is_exclusive(v_id_1780_)) as u8;
                                if v_isSharedCheck_1811_ == 0 {
                                    v___x_1806_ = v_id_1780_;
                                    v_isShared_1807_ = v_isSharedCheck_1811_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_n_1804_);
                                    leanh::lean_dec(v_id_1780_);
                                    v___x_1806_ = leanh::lean_box(0);
                                    v_isShared_1807_ = v_isSharedCheck_1811_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_1812_ = leanh::lean_box(0);
                                v___y_1785_ = v___x_1812_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_1813_ = leanh::lean_ctor_get(v_msg_1771_, 0);
                        v_params_x3f_1814_ = leanh::lean_ctor_get(v_msg_1771_, 1);
                        v_isSharedCheck_1826_ =
                            (!leanh::lean_is_exclusive(v_msg_1771_)) as u8;
                        if v_isSharedCheck_1826_ == 0 {
                            v___x_1816_ = v_msg_1771_;
                            v_isShared_1817_ = v_isSharedCheck_1826_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_params_x3f_1814_);
                            leanh::lean_inc(v_method_1813_);
                            leanh::lean_dec(v_msg_1771_);
                            v___x_1816_ = leanh::lean_box(0);
                            v_isShared_1817_ = v_isSharedCheck_1826_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_id_1827_ = leanh::lean_ctor_get(v_msg_1771_, 0);
                        v_result_1828_ = leanh::lean_ctor_get(v_msg_1771_, 1);
                        v_isSharedCheck_1860_ =
                            (!leanh::lean_is_exclusive(v_msg_1771_)) as u8;
                        if v_isSharedCheck_1860_ == 0 {
                            v___x_1830_ = v_msg_1771_;
                            v_isShared_1831_ = v_isSharedCheck_1860_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_result_1828_);
                            leanh::lean_inc(v_id_1827_);
                            leanh::lean_dec(v_msg_1771_);
                            v___x_1830_ = leanh::lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1860_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_id_1861_ = leanh::lean_ctor_get(v_msg_1771_, 0);
                        leanh::lean_inc(v_id_1861_);
                        v_code_1862_ = leanh::lean_ctor_get_uint8(
                            v_msg_1771_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_message_1863_ = leanh::lean_ctor_get(v_msg_1771_, 1);
                        leanh::lean_inc_ref(v_message_1863_);
                        v_data_x3f_1864_ = leanh::lean_ctor_get(v_msg_1771_, 2);
                        leanh::lean_inc(v_data_x3f_1864_);
                        leanh::lean_dec_ref_known(v_msg_1771_, 3);
                        v___x_1884_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                        match leanh::lean_obj_tag(v_id_1861_) {
                            0 => {
                                v_s_1902_ = leanh::lean_ctor_get(v_id_1861_, 0);
                                v_isSharedCheck_1909_ =
                                    (!leanh::lean_is_exclusive(v_id_1861_)) as u8;
                                if v_isSharedCheck_1909_ == 0 {
                                    v___x_1904_ = v_id_1861_;
                                    v_isShared_1905_ = v_isSharedCheck_1909_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_s_1902_);
                                    leanh::lean_dec(v_id_1861_);
                                    v___x_1904_ = leanh::lean_box(0);
                                    v_isShared_1905_ = v_isSharedCheck_1909_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_1910_ = leanh::lean_ctor_get(v_id_1861_, 0);
                                v_isSharedCheck_1917_ =
                                    (!leanh::lean_is_exclusive(v_id_1861_)) as u8;
                                if v_isSharedCheck_1917_ == 0 {
                                    v___x_1912_ = v_id_1861_;
                                    v_isShared_1913_ = v_isSharedCheck_1917_;
                                    state = 20;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_n_1910_);
                                    leanh::lean_dec(v_id_1861_);
                                    v___x_1912_ = leanh::lean_box(0);
                                    v_isShared_1913_ = v_isSharedCheck_1917_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_1918_ = leanh::lean_box(0);
                                v___y_1886_ = v___x_1918_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1776_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1776_, 0, v___x_1773_);
                leanh::lean_ctor_set(v___x_1776_, 1, v___y_1775_);
                v___x_1777_ = l_Lean_Json_mkObj(v___x_1776_);
                leanh::lean_dec_ref_known(v___x_1776_, 2);
                v___x_1778_ = l_Lean_Json_compress(v___x_1777_);
                v___x_1779_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_1770_, v___x_1778_);
                leanh::lean_dec_ref(v___x_1778_);
                return v___x_1779_;
            }
            2 => {
                v___x_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1786_, 0, v___x_1783_);
                leanh::lean_ctor_set(v___x_1786_, 1, v___y_1785_);
                v___x_1787_ = l_IO_FS_Stream_writeLspMessage___closed__5;
                v___x_1788_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1788_, 0, v_method_1781_);
                v___x_1789_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1789_, 0, v___x_1787_);
                leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = leanh::lean_box(0);
                v___x_1791_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1791_, 0, v___x_1789_);
                leanh::lean_ctor_set(v___x_1791_, 1, v___x_1790_);
                v___x_1792_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1792_, 0, v___x_1786_);
                leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
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
                    leanh::lean_ctor_set_tag(v___x_1798_, 3);
                    v___x_1801_ = v___x_1798_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_s_1796_);
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
                    leanh::lean_ctor_set_tag(v___x_1806_, 2);
                    v___x_1809_ = v___x_1806_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_n_1804_);
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
                v___x_1819_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1819_, 0, v_method_1813_);
                if v_isShared_1817_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1816_, 0);
                    leanh::lean_ctor_set(v___x_1816_, 1, v___x_1819_);
                    leanh::lean_ctor_set(v___x_1816_, 0, v___x_1818_);
                    v___x_1821_ = v___x_1816_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1819_);
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
                v___x_1824_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1824_, 0, v___x_1821_);
                leanh::lean_ctor_set(v___x_1824_, 1, v___x_1823_);
                v___y_1775_ = v___x_1824_;
                state = 1;
                continue;
            }
            9 => {
                v___x_1832_ = l_IO_FS_Stream_writeLspMessage___closed__4;
                match leanh::lean_obj_tag(v_id_1827_) {
                    0 => {
                        v_s_1843_ = leanh::lean_ctor_get(v_id_1827_, 0);
                        v_isSharedCheck_1850_ =
                            (!leanh::lean_is_exclusive(v_id_1827_)) as u8;
                        if v_isSharedCheck_1850_ == 0 {
                            v___x_1845_ = v_id_1827_;
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_1843_);
                            leanh::lean_dec(v_id_1827_);
                            v___x_1845_ = leanh::lean_box(0);
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_1851_ = leanh::lean_ctor_get(v_id_1827_, 0);
                        v_isSharedCheck_1858_ =
                            (!leanh::lean_is_exclusive(v_id_1827_)) as u8;
                        if v_isSharedCheck_1858_ == 0 {
                            v___x_1853_ = v_id_1827_;
                            v_isShared_1854_ = v_isSharedCheck_1858_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_1851_);
                            leanh::lean_dec(v_id_1827_);
                            v___x_1853_ = leanh::lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1858_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1859_ = leanh::lean_box(0);
                        v___y_1834_ = v___x_1859_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1831_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1830_, 0);
                    leanh::lean_ctor_set(v___x_1830_, 1, v___y_1834_);
                    leanh::lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1836_ = v___x_1830_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___y_1834_);
                    v___x_1836_ = v_reuseFailAlloc_1842_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1837_ = l_IO_FS_Stream_writeLspMessage___closed__7;
                v___x_1838_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1838_, 0, v___x_1837_);
                leanh::lean_ctor_set(v___x_1838_, 1, v_result_1828_);
                v___x_1839_ = leanh::lean_box(0);
                v___x_1840_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1840_, 0, v___x_1838_);
                leanh::lean_ctor_set(v___x_1840_, 1, v___x_1839_);
                v___x_1841_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1841_, 0, v___x_1836_);
                leanh::lean_ctor_set(v___x_1841_, 1, v___x_1840_);
                v___y_1775_ = v___x_1841_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_1846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1845_, 3);
                    v___x_1848_ = v___x_1845_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1849_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_s_1843_);
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
                    leanh::lean_ctor_set_tag(v___x_1853_, 2);
                    v___x_1856_ = v___x_1853_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_n_1851_);
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
                leanh::lean_inc(v___y_1869_);
                leanh::lean_inc_ref(v___y_1866_);
                v___x_1870_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1870_, 0, v___y_1866_);
                leanh::lean_ctor_set(v___x_1870_, 1, v___y_1869_);
                v___x_1871_ = l_IO_FS_Stream_writeLspMessage___closed__8;
                v___x_1872_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1872_, 0, v_message_1863_);
                v___x_1873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1873_, 0, v___x_1871_);
                leanh::lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                v___x_1874_ = leanh::lean_box(0);
                v___x_1875_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                leanh::lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                v___x_1876_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1876_, 0, v___x_1870_);
                leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_IO_FS_Stream_writeLspMessage___closed__9;
                v___x_1878_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(
                    v___x_1877_,
                    v_data_x3f_1864_,
                );
                leanh::lean_dec(v_data_x3f_1864_);
                v___x_1879_ = l_List_appendTR___redArg(v___x_1876_, v___x_1878_);
                v___x_1880_ = l_Lean_Json_mkObj(v___x_1879_);
                leanh::lean_dec(v___x_1879_);
                leanh::lean_inc_ref(v___y_1868_);
                v___x_1881_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1881_, 0, v___y_1868_);
                leanh::lean_ctor_set(v___x_1881_, 1, v___x_1880_);
                v___x_1882_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                leanh::lean_ctor_set(v___x_1882_, 1, v___x_1874_);
                v___x_1883_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1883_, 0, v___y_1867_);
                leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                v___y_1775_ = v___x_1883_;
                state = 1;
                continue;
            }
            17 => {
                v___x_1887_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1887_, 0, v___x_1884_);
                leanh::lean_ctor_set(v___x_1887_, 1, v___y_1886_);
                v___x_1888_ = l_IO_FS_Stream_writeLspMessage___closed__10;
                v___x_1889_ = l_IO_FS_Stream_writeLspMessage___closed__11;
                match v_code_1862_ {
                    0 => {
                        v___x_1890_ = leanh::lean_obj_once(
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
                        v___x_1891_ = leanh::lean_obj_once(
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
                        v___x_1892_ = leanh::lean_obj_once(
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
                        v___x_1893_ = leanh::lean_obj_once(
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
                        v___x_1894_ = leanh::lean_obj_once(
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
                        v___x_1895_ = leanh::lean_obj_once(
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
                        v___x_1896_ = leanh::lean_obj_once(
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
                        v___x_1897_ = leanh::lean_obj_once(
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
                        v___x_1898_ = leanh::lean_obj_once(
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
                        v___x_1899_ = leanh::lean_obj_once(
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
                        v___x_1900_ = leanh::lean_obj_once(
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
                        v___x_1901_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_1904_, 3);
                    v___x_1907_ = v___x_1904_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_s_1902_);
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
                    leanh::lean_ctor_set_tag(v___x_1912_, 2);
                    v___x_1915_ = v___x_1912_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_n_1910_);
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
    mut v_h_1919_: *mut leanh::LeanObject,
    mut v_msg_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_IO_FS_Stream_writeLspMessage(v_h_1919_, v_msg_1920_);
    return v_res_1922_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest___redArg(
    mut v_inst_1923_: *mut leanh::LeanObject,
    mut v_h_1924_: *mut leanh::LeanObject,
    mut v_r_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___y_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1927_ = leanh::lean_ctor_get(v_r_1925_, 0);
                v_method_1928_ = leanh::lean_ctor_get(v_r_1925_, 1);
                v_param_1929_ = leanh::lean_ctor_get(v_r_1925_, 2);
                v_isSharedCheck_1949_ = (!leanh::lean_is_exclusive(v_r_1925_)) as u8;
                if v_isSharedCheck_1949_ == 0 {
                    v___x_1931_ = v_r_1925_;
                    v_isShared_1932_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_param_1929_);
                    leanh::lean_inc(v_method_1928_);
                    leanh::lean_inc(v_id_1927_);
                    leanh::lean_dec(v_r_1925_);
                    v___x_1931_ = leanh::lean_box(0);
                    v_isShared_1932_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1939_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1923_, v_param_1929_);
                if leanh::lean_obj_tag(v___x_1939_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1939_, 1);
                    v___x_1940_ = leanh::lean_box(0);
                    v___y_1934_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_a_1941_ = leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1948_ = (!leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v___x_1943_ = v___x_1939_;
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1941_);
                        leanh::lean_dec(v___x_1939_);
                        v___x_1943_ = leanh::lean_box(0);
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1932_ == 0 {
                    leanh::lean_ctor_set(v___x_1931_, 2, v___y_1934_);
                    v___x_1936_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1938_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_id_1927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_method_1928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 2, v___y_1934_);
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
                    v_reuseFailAlloc_1947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
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
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_h_1951_: *mut leanh::LeanObject,
    mut v_r_1952_: *mut leanh::LeanObject,
    mut v_a_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_1950_, v_h_1951_, v_r_1952_);
    return v_res_1954_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest(
    mut v_00_u03b1_1955_: *mut leanh::LeanObject,
    mut v_inst_1956_: *mut leanh::LeanObject,
    mut v_h_1957_: *mut leanh::LeanObject,
    mut v_r_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_1956_, v_h_1957_, v_r_1958_);
    return v___x_1960_;
}
pub unsafe fn l_IO_FS_Stream_writeLspRequest___boxed(
    mut v_00_u03b1_1961_: *mut leanh::LeanObject,
    mut v_inst_1962_: *mut leanh::LeanObject,
    mut v_h_1963_: *mut leanh::LeanObject,
    mut v_r_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ =
        l_IO_FS_Stream_writeLspRequest(v_00_u03b1_1961_, v_inst_1962_, v_h_1963_, v_r_1964_);
    return v_res_1966_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification___redArg(
    mut v_inst_1967_: *mut leanh::LeanObject,
    mut v_h_1968_: *mut leanh::LeanObject,
    mut v_n_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___y_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_isSharedCheck_1992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_1971_ = leanh::lean_ctor_get(v_n_1969_, 0);
                v_param_1972_ = leanh::lean_ctor_get(v_n_1969_, 1);
                v_isSharedCheck_1992_ = (!leanh::lean_is_exclusive(v_n_1969_)) as u8;
                if v_isSharedCheck_1992_ == 0 {
                    v___x_1974_ = v_n_1969_;
                    v_isShared_1975_ = v_isSharedCheck_1992_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_param_1972_);
                    leanh::lean_inc(v_method_1971_);
                    leanh::lean_dec(v_n_1969_);
                    v___x_1974_ = leanh::lean_box(0);
                    v_isShared_1975_ = v_isSharedCheck_1992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1967_, v_param_1972_);
                if leanh::lean_obj_tag(v___x_1982_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1982_, 1);
                    v___x_1983_ = leanh::lean_box(0);
                    v___y_1977_ = v___x_1983_;
                    state = 2;
                    continue;
                } else {
                    v_a_1984_ = leanh::lean_ctor_get(v___x_1982_, 0);
                    v_isSharedCheck_1991_ = (!leanh::lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1986_ = v___x_1982_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1984_);
                        leanh::lean_dec(v___x_1982_);
                        v___x_1986_ = leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1975_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1974_, 1);
                    leanh::lean_ctor_set(v___x_1974_, 1, v___y_1977_);
                    v___x_1979_ = v___x_1974_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_method_1971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___y_1977_);
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
                    v_reuseFailAlloc_1990_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
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
    mut v_inst_1993_: *mut leanh::LeanObject,
    mut v_h_1994_: *mut leanh::LeanObject,
    mut v_n_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_1993_, v_h_1994_, v_n_1995_);
    return v_res_1997_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification(
    mut v_00_u03b1_1998_: *mut leanh::LeanObject,
    mut v_inst_1999_: *mut leanh::LeanObject,
    mut v_h_2000_: *mut leanh::LeanObject,
    mut v_n_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_1999_, v_h_2000_, v_n_2001_);
    return v___x_2003_;
}
pub unsafe fn l_IO_FS_Stream_writeLspNotification___boxed(
    mut v_00_u03b1_2004_: *mut leanh::LeanObject,
    mut v_inst_2005_: *mut leanh::LeanObject,
    mut v_h_2006_: *mut leanh::LeanObject,
    mut v_n_2007_: *mut leanh::LeanObject,
    mut v_a_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ =
        l_IO_FS_Stream_writeLspNotification(v_00_u03b1_2004_, v_inst_2005_, v_h_2006_, v_n_2007_);
    return v_res_2009_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse___redArg(
    mut v_inst_2010_: *mut leanh::LeanObject,
    mut v_h_2011_: *mut leanh::LeanObject,
    mut v_r_2012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2018_: u8 = 0;
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2014_ = leanh::lean_ctor_get(v_r_2012_, 0);
                v_result_2015_ = leanh::lean_ctor_get(v_r_2012_, 1);
                v_isSharedCheck_2024_ = (!leanh::lean_is_exclusive(v_r_2012_)) as u8;
                if v_isSharedCheck_2024_ == 0 {
                    v___x_2017_ = v_r_2012_;
                    v_isShared_2018_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_result_2015_);
                    leanh::lean_inc(v_id_2014_);
                    leanh::lean_dec(v_r_2012_);
                    v___x_2017_ = leanh::lean_box(0);
                    v_isShared_2018_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2019_ = leanh::lean_apply_1(v_inst_2010_, v_result_2015_);
                if v_isShared_2018_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2017_, 2);
                    leanh::lean_ctor_set(v___x_2017_, 1, v___x_2019_);
                    v___x_2021_ = v___x_2017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_id_2014_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2019_);
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
    mut v_inst_2025_: *mut leanh::LeanObject,
    mut v_h_2026_: *mut leanh::LeanObject,
    mut v_r_2027_: *mut leanh::LeanObject,
    mut v_a_2028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_2025_, v_h_2026_, v_r_2027_);
    return v_res_2029_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse(
    mut v_00_u03b1_2030_: *mut leanh::LeanObject,
    mut v_inst_2031_: *mut leanh::LeanObject,
    mut v_h_2032_: *mut leanh::LeanObject,
    mut v_r_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_2031_, v_h_2032_, v_r_2033_);
    return v___x_2035_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponse___boxed(
    mut v_00_u03b1_2036_: *mut leanh::LeanObject,
    mut v_inst_2037_: *mut leanh::LeanObject,
    mut v_h_2038_: *mut leanh::LeanObject,
    mut v_r_2039_: *mut leanh::LeanObject,
    mut v_a_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2041_ =
        l_IO_FS_Stream_writeLspResponse(v_00_u03b1_2036_, v_inst_2037_, v_h_2038_, v_r_2039_);
    return v_res_2041_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseError(
    mut v_h_2042_: *mut leanh::LeanObject,
    mut v_e_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2046_: u8 = 0;
    let mut v_message_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2045_ = leanh::lean_ctor_get(v_e_2043_, 0);
                v_code_2046_ = leanh::lean_ctor_get_uint8(
                    v_e_2043_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_message_2047_ = leanh::lean_ctor_get(v_e_2043_, 1);
                v_isSharedCheck_2056_ = (!leanh::lean_is_exclusive(v_e_2043_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = leanh::lean_ctor_get(v_e_2043_, 2);
                    leanh::lean_dec(v_unused_2057_);
                    v___x_2049_ = v_e_2043_;
                    v_isShared_2050_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_message_2047_);
                    leanh::lean_inc(v_id_2045_);
                    leanh::lean_dec(v_e_2043_);
                    v___x_2049_ = leanh::lean_box(0);
                    v_isShared_2050_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2051_ = leanh::lean_box(0);
                if v_isShared_2050_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2049_, 3);
                    leanh::lean_ctor_set(v___x_2049_, 2, v___x_2051_);
                    v___x_2053_ = v___x_2049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = leanh::lean_alloc_ctor(3, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_id_2045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_message_2047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 2, v___x_2051_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2055_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
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
    mut v_h_2058_: *mut leanh::LeanObject,
    mut v_e_2059_: *mut leanh::LeanObject,
    mut v_a_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2061_ = l_IO_FS_Stream_writeLspResponseError(v_h_2058_, v_e_2059_);
    return v_res_2061_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(
    mut v_inst_2062_: *mut leanh::LeanObject,
    mut v_h_2063_: *mut leanh::LeanObject,
    mut v_e_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2067_: u8 = 0;
    let mut v_message_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___y_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2066_ = leanh::lean_ctor_get(v_e_2064_, 0);
                v_code_2067_ = leanh::lean_ctor_get_uint8(
                    v_e_2064_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_message_2068_ = leanh::lean_ctor_get(v_e_2064_, 1);
                v_data_x3f_2069_ = leanh::lean_ctor_get(v_e_2064_, 2);
                v_isSharedCheck_2089_ = (!leanh::lean_is_exclusive(v_e_2064_)) as u8;
                if v_isSharedCheck_2089_ == 0 {
                    v___x_2071_ = v_e_2064_;
                    v_isShared_2072_ = v_isSharedCheck_2089_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_data_x3f_2069_);
                    leanh::lean_inc(v_message_2068_);
                    leanh::lean_inc(v_id_2066_);
                    leanh::lean_dec(v_e_2064_);
                    v___x_2071_ = leanh::lean_box(0);
                    v_isShared_2072_ = v_isSharedCheck_2089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_data_x3f_2069_) == 0 {
                    leanh::lean_dec_ref(v_inst_2062_);
                    v___x_2079_ = leanh::lean_box(0);
                    v___y_2074_ = v___x_2079_;
                    state = 2;
                    continue;
                } else {
                    v_val_2080_ = leanh::lean_ctor_get(v_data_x3f_2069_, 0);
                    v_isSharedCheck_2088_ =
                        (!leanh::lean_is_exclusive(v_data_x3f_2069_)) as u8;
                    if v_isSharedCheck_2088_ == 0 {
                        v___x_2082_ = v_data_x3f_2069_;
                        v_isShared_2083_ = v_isSharedCheck_2088_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2080_);
                        leanh::lean_dec(v_data_x3f_2069_);
                        v___x_2082_ = leanh::lean_box(0);
                        v_isShared_2083_ = v_isSharedCheck_2088_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2072_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2071_, 3);
                    leanh::lean_ctor_set(v___x_2071_, 2, v___y_2074_);
                    v___x_2076_ = v___x_2071_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = leanh::lean_alloc_ctor(3, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_id_2066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_message_2068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 2, v___y_2074_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2078_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
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
                v___x_2084_ = leanh::lean_apply_1(v_inst_2062_, v_val_2080_);
                if v_isShared_2083_ == 0 {
                    leanh::lean_ctor_set(v___x_2082_, 0, v___x_2084_);
                    v___x_2086_ = v___x_2082_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
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
    mut v_inst_2090_: *mut leanh::LeanObject,
    mut v_h_2091_: *mut leanh::LeanObject,
    mut v_e_2092_: *mut leanh::LeanObject,
    mut v_a_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ =
        l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_2090_, v_h_2091_, v_e_2092_);
    return v_res_2094_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData(
    mut v_00_u03b1_2095_: *mut leanh::LeanObject,
    mut v_inst_2096_: *mut leanh::LeanObject,
    mut v_h_2097_: *mut leanh::LeanObject,
    mut v_e_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ =
        l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_2096_, v_h_2097_, v_e_2098_);
    return v___x_2100_;
}
pub unsafe fn l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(
    mut v_00_u03b1_2101_: *mut leanh::LeanObject,
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_h_2103_: *mut leanh::LeanObject,
    mut v_e_2104_: *mut leanh::LeanObject,
    mut v_a_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Communication(
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
pub unsafe fn initialize_Lean_Data_Lsp_Communication(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_JsonRpc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Communication(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Communication(builtin);
}