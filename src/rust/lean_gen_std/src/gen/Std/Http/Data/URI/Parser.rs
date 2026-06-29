// Lean compiler output
// Module: Std.Http.Data.URI.Parser
// Imports: Init.While Init.Data.String.Basic Std.Internal.Parsec Std.Internal.Parsec.ByteArray Std.Http.Data.URI.Basic Std.Http.Data.URI.Config Init.Data.String.Search
use crate::r#gen::Init::Data::List::Basic::l_List_head_x3f___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toNat_x3f, l_String_Slice_toString};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::{l_ByteArray_empty, l_Char_utf8Size};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Std::Data::ByteSlice::{
    l_ByteArray_toByteSlice, l_ByteSlice_size, l_ByteSlice_toByteArray,
};
use crate::r#gen::Std::Http::Data::URI::Basic::{
    initialize_Std_Http_Data_URI_Basic, l_Std_Http_URI_Query_empty,
    l_Std_Http_URI_Query_insertEncoded, l_Std_Http_URI_isValidDomainLabel,
    runtime_initialize_Std_Http_Data_URI_Basic,
};
use crate::r#gen::Std::Http::Data::URI::Config::{
    initialize_Std_Http_Data_URI_Config, runtime_initialize_Std_Http_Data_URI_Config,
};
use crate::r#gen::Std::Http::Data::URI::Encoding::{
    l_Std_Http_URI_EncodedFragment_decode, l_Std_Http_URI_EncodedFragment_ofByteArray_x3f,
    l_Std_Http_URI_EncodedQueryParam_fromString_x3f, l_Std_Http_URI_EncodedSegment_ofByteArray_x3f,
    l_Std_Http_URI_EncodedString_empty, l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f,
};
use crate::r#gen::Std::Http::Internal::LowerCase::l_Std_Http_Internal_instDecidableIsLowerCase;
use crate::r#gen::Std::Internal::Parsec::ByteArray::{
    initialize_Std_Internal_Parsec_ByteArray,
    l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo,
    l_Std_Internal_Parsec_ByteArray_skipBytes, runtime_initialize_Std_Internal_Parsec_ByteArray,
};
use crate::r#gen::Std::Internal::Parsec::{
    initialize_Std_Internal_Parsec, runtime_initialize_Std_Internal_Parsec,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::{
    lean_byte_array_copy_slice, lean_byte_array_fget,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_data, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_string_validate_utf8,
};
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::String::Length::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_of_nat, lean_uint32_add, lean_uint32_to_uint8,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_byte_array_push,
    lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_from_utf8_unchecked,
    lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_nat,
};
use crate::lean_imports_rs::Std::Net::Addr::{lean_uv_pton_v4, lean_uv_pton_v6};
pub static l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8: u8 = 0;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 115, 99, 104, 101, 109, 101, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115, 102, 105, 101, 100, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [115, 99, 104, 101, 109, 101, 32, 108, 101, 110, 103, 116, 104, 32, 108, 105, 109, 105, 116, 32, 105, 115, 32, 48, 32, 40, 110, 111, 32, 115, 99, 104, 101, 109, 101, 32, 97, 108, 108, 111, 119, 101, 100, 41, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [112, 111, 114, 116, 32, 110, 117, 109, 98, 101, 114, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 111, 114, 116, 32, 110, 117, 109, 98, 101, 114, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13: u8 = 0;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 101, 114, 99, 101, 110, 116, 32, 101, 110, 99, 111, 100, 105, 110, 103, 32, 105, 110, 32, 117, 115, 101, 114, 32, 105, 110, 102, 111, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1: u8 = 0;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 73, 80, 118, 54, 32, 97, 100, 100, 114, 101, 115, 115, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1: u8 =
    0;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9: u8 =
    0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101, 32, 99, 104, 97, 114, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 73, 80, 118, 52, 32, 97, 100, 100, 114, 101, 115, 115, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 109, 97, 105, 110, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 104, 111, 115, 116, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 111, 114, 116, 32, 110, 117, 109, 98, 101, 114, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10: u8 = 0;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [116, 111, 111, 32, 109, 97, 110, 121, 32, 112, 97, 116, 104, 32, 115, 101, 103, 109, 101, 110, 116, 115, 32, 40, 108, 105, 109, 105, 116, 58, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [112, 97, 116, 104, 32, 116, 111, 111, 32, 108, 111, 110, 103, 32, 40, 108, 105, 109, 105, 116, 58, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 98, 121, 116, 101, 115, 41, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 101, 114, 99, 101, 110, 116, 32, 101, 110, 99, 111, 100, 105, 110, 103, 32, 105, 110, 32, 112, 97, 116, 104, 32, 115, 101, 103, 109, 101, 110, 116, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            114, 101, 113, 117, 105, 114, 101, 32, 39, 47, 39, 32, 105, 110, 32, 112, 97, 116, 104,
            0,
        ],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [110, 101, 101, 100, 32, 97, 32, 112, 97, 116, 104, 0],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__4_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parsePath___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__4_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Parser_parsePath___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parsePath___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 113, 117, 101, 114, 121, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [116, 111, 111, 32, 109, 97, 110, 121, 32, 113, 117, 101, 114, 121, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 40, 108, 105, 109, 105, 116, 58, 32, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 101, 114, 99, 101, 110, 116, 32, 101, 110, 99, 111, 100, 105, 110, 103, 32, 105, 110, 32, 102, 114, 97, 103, 109, 101, 110, 116, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [47, 47, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_Parser_parseURI___closed__5_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 102, 114, 97, 103, 109, 101, 110, 116, 32, 112,
            97, 114, 115, 101, 32, 101, 110, 99, 111, 100, 105, 110, 103, 0,
        ],
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseURI___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parseURI___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Parser_parseURI___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseURI___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_URI_Parser_parseURI___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_Parser_parseURI___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_Parser_parseURI___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 111, 116, 32, 111, 114, 105, 103, 105, 110, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [110, 111, 116, 32, 104, 116, 116, 112, 32, 97, 98, 115, 111, 108, 117, 116, 101, 32, 117, 114, 105, 32, 119, 105, 116, 104, 32, 112, 97, 116, 104, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [110, 111, 116, 32, 104, 116, 116, 112, 32, 97, 98, 115, 111, 108, 117, 116, 101, 32, 117, 114, 105, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 116, 116, 112, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 116, 116, 112, 115, 0]};
static mut l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parseHostHeader___closed__0_value: crate::leanh::LeanStringObject<
    25,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 104, 111, 115, 116, 32, 104, 101, 97, 100, 101, 114,
        32, 112, 111, 114, 116, 0,
    ],
};
static mut l_Std_Http_URI_Parser_parseHostHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parseHostHeader___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_Parser_parseHostHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parseHostHeader___closed__2_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 104, 111, 115, 116, 32, 104, 101, 97, 100, 101, 114,
        0,
    ],
};
static mut l_Std_Http_URI_Parser_parseHostHeader___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Parser_parseHostHeader___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_Parser_parseHostHeader___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Parser_parseHostHeader___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(
    mut v_p_3584_: *mut crate::leanh::LeanObject,
    mut v_a_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v_err_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v_idx_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3610_: u8 = 0;
    let mut v_unused_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_3585_);
                v___x_3586_ = crate::leanh::lean_apply_1(v_p_3584_, v_a_3585_);
                if crate::leanh::lean_obj_tag(v___x_3586_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3585_);
                    v_pos_3587_ = crate::leanh::lean_ctor_get(v___x_3586_, 0);
                    v_res_3588_ = crate::leanh::lean_ctor_get(v___x_3586_, 1);
                    v_isSharedCheck_3596_ = (!crate::leanh::lean_is_exclusive(v___x_3586_)) as u8;
                    if v_isSharedCheck_3596_ == 0 {
                        v___x_3590_ = v___x_3586_;
                        v_isShared_3591_ = v_isSharedCheck_3596_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3588_);
                        crate::leanh::lean_inc(v_pos_3587_);
                        crate::leanh::lean_dec(v___x_3586_);
                        v___x_3590_ = crate::leanh::lean_box(0);
                        v_isShared_3591_ = v_isSharedCheck_3596_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_err_3597_ = crate::leanh::lean_ctor_get(v___x_3586_, 1);
                    v_isSharedCheck_3610_ = (!crate::leanh::lean_is_exclusive(v___x_3586_)) as u8;
                    if v_isSharedCheck_3610_ == 0 {
                        v_unused_3611_ = crate::leanh::lean_ctor_get(v___x_3586_, 0);
                        crate::leanh::lean_dec(v_unused_3611_);
                        v___x_3599_ = v___x_3586_;
                        v_isShared_3600_ = v_isSharedCheck_3610_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3597_);
                        crate::leanh::lean_dec(v___x_3586_);
                        v___x_3599_ = crate::leanh::lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3610_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3592_, 0, v_res_3588_);
                if v_isShared_3591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3590_, 1, v___x_3592_);
                    v___x_3594_ = v___x_3590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_pos_3587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3592_);
                    v___x_3594_ = v_reuseFailAlloc_3595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3594_;
            }
            3 => {
                v_idx_3601_ = crate::leanh::lean_ctor_get(v_a_3585_, 1);
                v___x_3602_ = lean_nat_dec_eq(v_idx_3601_, v_idx_3601_);
                if v___x_3602_ == 0 {
                    if v_isShared_3600_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3599_, 0, v_a_3585_);
                        v___x_3604_ = v___x_3599_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3585_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_err_3597_);
                        v___x_3604_ = v_reuseFailAlloc_3605_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_3597_);
                    v___x_3606_ = crate::leanh::lean_box(0);
                    if v_isShared_3600_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3599_, 0);
                        crate::leanh::lean_ctor_set(v___x_3599_, 1, v___x_3606_);
                        crate::leanh::lean_ctor_set(v___x_3599_, 0, v_a_3585_);
                        v___x_3608_ = v___x_3599_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3585_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 1, v___x_3606_);
                        v___x_3608_ = v_reuseFailAlloc_3609_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3604_;
            }
            5 => {
                return v___x_3608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(
    mut v_00_u03b1_3612_: *mut crate::leanh::LeanObject,
    mut v_p_3613_: *mut crate::leanh::LeanObject,
    mut v_a_3614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v_err_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v_idx_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_unused_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_3614_);
                v___x_3615_ = crate::leanh::lean_apply_1(v_p_3613_, v_a_3614_);
                if crate::leanh::lean_obj_tag(v___x_3615_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3614_);
                    v_pos_3616_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                    v_res_3617_ = crate::leanh::lean_ctor_get(v___x_3615_, 1);
                    v_isSharedCheck_3625_ = (!crate::leanh::lean_is_exclusive(v___x_3615_)) as u8;
                    if v_isSharedCheck_3625_ == 0 {
                        v___x_3619_ = v___x_3615_;
                        v_isShared_3620_ = v_isSharedCheck_3625_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3617_);
                        crate::leanh::lean_inc(v_pos_3616_);
                        crate::leanh::lean_dec(v___x_3615_);
                        v___x_3619_ = crate::leanh::lean_box(0);
                        v_isShared_3620_ = v_isSharedCheck_3625_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_err_3626_ = crate::leanh::lean_ctor_get(v___x_3615_, 1);
                    v_isSharedCheck_3639_ = (!crate::leanh::lean_is_exclusive(v___x_3615_)) as u8;
                    if v_isSharedCheck_3639_ == 0 {
                        v_unused_3640_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                        crate::leanh::lean_dec(v_unused_3640_);
                        v___x_3628_ = v___x_3615_;
                        v_isShared_3629_ = v_isSharedCheck_3639_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3626_);
                        crate::leanh::lean_dec(v___x_3615_);
                        v___x_3628_ = crate::leanh::lean_box(0);
                        v_isShared_3629_ = v_isSharedCheck_3639_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3621_, 0, v_res_3617_);
                if v_isShared_3620_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3619_, 1, v___x_3621_);
                    v___x_3623_ = v___x_3619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_pos_3616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3621_);
                    v___x_3623_ = v_reuseFailAlloc_3624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3623_;
            }
            3 => {
                v_idx_3630_ = crate::leanh::lean_ctor_get(v_a_3614_, 1);
                v___x_3631_ = lean_nat_dec_eq(v_idx_3630_, v_idx_3630_);
                if v___x_3631_ == 0 {
                    if v_isShared_3629_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3628_, 0, v_a_3614_);
                        v___x_3633_ = v___x_3628_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3634_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3614_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_err_3626_);
                        v___x_3633_ = v_reuseFailAlloc_3634_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_3626_);
                    v___x_3635_ = crate::leanh::lean_box(0);
                    if v_isShared_3629_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3628_, 0);
                        crate::leanh::lean_ctor_set(v___x_3628_, 1, v___x_3635_);
                        crate::leanh::lean_ctor_set(v___x_3628_, 0, v_a_3614_);
                        v___x_3637_ = v___x_3628_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3614_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 1, v___x_3635_);
                        v___x_3637_ = v_reuseFailAlloc_3638_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3633_;
            }
            5 => {
                return v___x_3637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(
    mut v_p_3641_: *mut crate::leanh::LeanObject,
    mut v_a_3642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: u8 = 0;
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: u8 = 0;
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3648_ = crate::leanh::lean_ctor_get(v_a_3642_, 0);
                v_idx_3649_ = crate::leanh::lean_ctor_get(v_a_3642_, 1);
                v___x_3650_ = lean_byte_array_size(v_array_3648_);
                v___x_3651_ = lean_nat_dec_lt(v_idx_3649_, v___x_3650_);
                if v___x_3651_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_3641_);
                    v_pos_3644_ = v_a_3642_;
                    state = 1;
                    continue;
                } else {
                    v___x_3652_ = lean_byte_array_fget(v_array_3648_, v_idx_3649_);
                    v___x_3653_ = crate::leanh::lean_box((v___x_3652_) as usize);
                    v___x_3654_ = crate::leanh::lean_apply_1(v_p_3641_, v___x_3653_);
                    v___x_3655_ = (crate::leanh::lean_unbox(v___x_3654_) as u8);
                    if v___x_3655_ == 0 {
                        v_pos_3644_ = v_a_3642_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3656_, 0, v_a_3642_);
                        crate::leanh::lean_ctor_set(v___x_3656_, 1, v___x_3654_);
                        return v___x_3656_;
                    }
                }
            }
            1 => {
                v___x_3645_ = 0;
                v___x_3646_ = crate::leanh::lean_box((v___x_3645_) as usize);
                v___x_3647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3647_, 0, v_pos_3644_);
                crate::leanh::lean_ctor_set(v___x_3647_, 1, v___x_3646_);
                return v___x_3647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(
    mut v_msg_3658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0;
    v___x_3660_ = lean_panic_fn_borrowed(v___x_3659_, v_msg_3658_);
    return v___x_3660_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0()
-> u8 {
    let mut v___x_3661_: u32 = 0;
    let mut v___x_3662_: u8 = 0;
    v___x_3661_ = 43;
    v___x_3662_ = lean_uint32_to_uint8(v___x_3661_);
    return v___x_3662_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1()
-> u8 {
    let mut v___x_3663_: u32 = 0;
    let mut v___x_3664_: u8 = 0;
    v___x_3663_ = 45;
    v___x_3664_ = lean_uint32_to_uint8(v___x_3663_);
    return v___x_3664_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2()
-> u8 {
    let mut v___x_3665_: u32 = 0;
    let mut v___x_3666_: u8 = 0;
    v___x_3665_ = 46;
    v___x_3666_ = lean_uint32_to_uint8(v___x_3665_);
    return v___x_3666_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3()
-> u8 {
    let mut v___x_3667_: u32 = 0;
    let mut v___x_3668_: u8 = 0;
    v___x_3667_ = 65;
    v___x_3668_ = lean_uint32_to_uint8(v___x_3667_);
    return v___x_3668_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4()
-> u8 {
    let mut v___x_3669_: u32 = 0;
    let mut v___x_3670_: u8 = 0;
    v___x_3669_ = 90;
    v___x_3670_ = lean_uint32_to_uint8(v___x_3669_);
    return v___x_3670_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5()
-> u8 {
    let mut v___x_3671_: u32 = 0;
    let mut v___x_3672_: u8 = 0;
    v___x_3671_ = 97;
    v___x_3672_ = lean_uint32_to_uint8(v___x_3671_);
    return v___x_3672_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6()
-> u8 {
    let mut v___x_3673_: u32 = 0;
    let mut v___x_3674_: u8 = 0;
    v___x_3673_ = 122;
    v___x_3674_ = lean_uint32_to_uint8(v___x_3673_);
    return v___x_3674_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7()
-> u8 {
    let mut v___x_3675_: u32 = 0;
    let mut v___x_3676_: u8 = 0;
    v___x_3675_ = 48;
    v___x_3676_ = lean_uint32_to_uint8(v___x_3675_);
    return v___x_3676_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8()
-> u8 {
    let mut v___x_3677_: u32 = 0;
    let mut v___x_3678_: u8 = 0;
    v___x_3677_ = 57;
    v___x_3678_ = lean_uint32_to_uint8(v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(
    mut v_c_3679_: u8,
) -> u8 {
    let mut v___y_3681_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: u8 = 0;
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: u8 = 0;
    let mut v___x_3686_: u8 = 0;
    let mut v___x_3687_: u8 = 0;
    let mut v___y_3689_: u8 = 0;
    let mut v___x_3690_: u8 = 0;
    let mut v___x_3691_: u8 = 0;
    let mut v___x_3692_: u8 = 0;
    let mut v___x_3693_: u8 = 0;
    let mut v___y_3695_: u8 = 0;
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: u8 = 0;
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3700_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_3701_ = lean_uint8_dec_le(v___x_3700_, v_c_3679_);
                if v___x_3701_ == 0 {
                    v___y_3695_ = v___x_3701_;
                    state = 3;
                    continue;
                } else {
                    v___x_3702_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_3703_ = lean_uint8_dec_le(v_c_3679_, v___x_3702_);
                    v___y_3695_ = v___x_3703_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_3681_ == 0 {
                    v___x_3682_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                    v___x_3683_ = lean_uint8_dec_eq(v_c_3679_, v___x_3682_);
                    if v___x_3683_ == 0 {
                        v___x_3684_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                        v___x_3685_ = lean_uint8_dec_eq(v_c_3679_, v___x_3684_);
                        if v___x_3685_ == 0 {
                            v___x_3686_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                            v___x_3687_ = lean_uint8_dec_eq(v_c_3679_, v___x_3686_);
                            if v___x_3687_ == 0 {
                                return v___y_3681_;
                            } else {
                                return v___x_3687_;
                            }
                        } else {
                            return v___x_3685_;
                        }
                    } else {
                        return v___x_3683_;
                    }
                } else {
                    return v___y_3681_;
                }
            }
            2 => {
                if v___y_3689_ == 0 {
                    v___x_3690_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_3691_ = lean_uint8_dec_le(v___x_3690_, v_c_3679_);
                    if v___x_3691_ == 0 {
                        v___y_3681_ = v___x_3691_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3692_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_3693_ = lean_uint8_dec_le(v_c_3679_, v___x_3692_);
                        v___y_3681_ = v___x_3693_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_3689_;
                }
            }
            3 => {
                if v___y_3695_ == 0 {
                    v___x_3696_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_3697_ = lean_uint8_dec_le(v___x_3696_, v_c_3679_);
                    if v___x_3697_ == 0 {
                        v___y_3689_ = v___x_3697_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3698_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_3699_ = lean_uint8_dec_le(v_c_3679_, v___x_3698_);
                        v___y_3689_ = v___x_3699_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_3695_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(
    mut v_c_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_3705_: u8 = 0;
    let mut v_res_3706_: u8 = 0;
    let mut v_r_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_3705_ = (crate::leanh::lean_unbox(v_c_3704_) as u8);
    v_res_3706_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(
        v_c_boxed_3705_,
    );
    v_r_3707_ = crate::leanh::lean_box((v_res_3706_) as usize);
    return v_r_3707_;
}
pub unsafe fn l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(
    mut v_x_3708_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3709_: u8 = 0;
    let mut v_head_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: u8 = 0;
    let mut v___x_3714_: u32 = 0;
    let mut v___x_3715_: u32 = 0;
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: u32 = 0;
    let mut v___x_3718_: u32 = 0;
    let mut v___x_3719_: u8 = 0;
    let mut v___x_3720_: u32 = 0;
    let mut v___x_3721_: u32 = 0;
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3728_: u32 = 0;
    let mut v___x_3729_: u32 = 0;
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: u32 = 0;
    let mut v___x_3732_: u32 = 0;
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: u32 = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___y_3739_: u8 = 0;
    let mut v___x_3740_: u32 = 0;
    let mut v___x_3741_: u32 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: u32 = 0;
    let mut v___x_3744_: u32 = 0;
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3747_: u32 = 0;
    let mut v___x_3748_: u32 = 0;
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: u32 = 0;
    let mut v___x_3751_: u32 = 0;
    let mut v___x_3752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3708_) == 0 {
                    v___x_3709_ = 1;
                    return v___x_3709_;
                } else {
                    v_head_3710_ = crate::leanh::lean_ctor_get(v_x_3708_, 0);
                    v_tail_3711_ = crate::leanh::lean_ctor_get(v_x_3708_, 1);
                    v___x_3734_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                    v___x_3735_ = lean_uint32_to_nat(v___x_3734_);
                    v___x_3736_ = crate::leanh::lean_unsigned_to_nat(128);
                    v___x_3737_ = lean_nat_dec_lt(v___x_3735_, v___x_3736_);
                    crate::leanh::lean_dec(v___x_3735_);
                    if v___x_3737_ == 0 {
                        v___y_3713_ = v___x_3737_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3747_ = 48;
                        v___x_3748_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                        v___x_3749_ = lean_uint32_dec_le(v___x_3747_, v___x_3748_);
                        if v___x_3749_ == 0 {
                            v___y_3739_ = v___x_3749_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3750_ = 57;
                            v___x_3751_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                            v___x_3752_ = lean_uint32_dec_le(v___x_3751_, v___x_3750_);
                            v___y_3739_ = v___x_3752_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_3713_ == 0 {
                    v___x_3714_ = 43;
                    v___x_3715_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                    v___x_3716_ = lean_uint32_dec_eq(v___x_3715_, v___x_3714_);
                    if v___x_3716_ == 0 {
                        v___x_3717_ = 45;
                        v___x_3718_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                        v___x_3719_ = lean_uint32_dec_eq(v___x_3718_, v___x_3717_);
                        if v___x_3719_ == 0 {
                            v___x_3720_ = 46;
                            v___x_3721_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                            v___x_3722_ = lean_uint32_dec_eq(v___x_3721_, v___x_3720_);
                            if v___x_3722_ == 0 {
                                return v___y_3713_;
                            } else {
                                v_x_3708_ = v_tail_3711_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_3708_ = v_tail_3711_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_3708_ = v_tail_3711_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_x_3708_ = v_tail_3711_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3728_ = 97;
                v___x_3729_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                v___x_3730_ = lean_uint32_dec_le(v___x_3728_, v___x_3729_);
                if v___x_3730_ == 0 {
                    v___y_3713_ = v___x_3730_;
                    state = 1;
                    continue;
                } else {
                    v___x_3731_ = 122;
                    v___x_3732_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                    v___x_3733_ = lean_uint32_dec_le(v___x_3732_, v___x_3731_);
                    v___y_3713_ = v___x_3733_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_3739_ == 0 {
                    v___x_3740_ = 65;
                    v___x_3741_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                    v___x_3742_ = lean_uint32_dec_le(v___x_3740_, v___x_3741_);
                    if v___x_3742_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_3743_ = 90;
                        v___x_3744_ = crate::leanh::lean_unbox_uint32(v_head_3710_);
                        v___x_3745_ = lean_uint32_dec_le(v___x_3744_, v___x_3743_);
                        if v___x_3745_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_3713_ = v___x_3737_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_x_3708_ = v_tail_3711_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(
    mut v_x_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: u8 = 0;
    let mut v_r_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_3753_);
    crate::leanh::lean_dec(v_x_3753_);
    v_r_3755_ = crate::leanh::lean_box((v_res_3754_) as usize);
    return v_r_3755_;
}
pub unsafe fn l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(
    mut v_s_3756_: *mut crate::leanh::LeanObject,
    mut v_p_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3759_: u32 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: u32 = 0;
    let mut v___x_3767_: u32 = 0;
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3769_: u32 = 0;
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: u32 = 0;
    let mut v___x_3772_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3764_ = lean_string_utf8_byte_size(v_s_3756_);
                v___x_3765_ = lean_nat_dec_eq(v_p_3757_, v___x_3764_);
                if v___x_3765_ == 0 {
                    v___x_3766_ = lean_string_utf8_get_fast(v_s_3756_, v_p_3757_);
                    v___x_3767_ = 65;
                    v___x_3768_ = lean_uint32_dec_le(v___x_3767_, v___x_3766_);
                    if v___x_3768_ == 0 {
                        v___y_3759_ = v___x_3766_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3769_ = 90;
                        v___x_3770_ = lean_uint32_dec_le(v___x_3766_, v___x_3769_);
                        if v___x_3770_ == 0 {
                            v___y_3759_ = v___x_3766_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3771_ = 32;
                            v___x_3772_ = lean_uint32_add(v___x_3766_, v___x_3771_);
                            v___y_3759_ = v___x_3772_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_3757_);
                    return v_s_3756_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_3757_);
                v___x_3760_ = lean_string_utf8_set(v_s_3756_, v_p_3757_, v___y_3759_);
                v___x_3761_ = l_Char_utf8Size(v___y_3759_);
                v___x_3762_ = lean_nat_add(v_p_3757_, v___x_3761_);
                crate::leanh::lean_dec(v___x_3761_);
                crate::leanh::lean_dec(v_p_3757_);
                v_s_3756_ = v___x_3760_;
                v_p_3757_ = v___x_3762_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4;
    v___x_3780_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_3781_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_3782_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3;
    v___x_3783_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2;
    v___x_3784_ = l_mkPanicMessageWithDecl(
        v___x_3783_,
        v___x_3782_,
        v___x_3781_,
        v___x_3780_,
        v___x_3779_,
    );
    return v___x_3784_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(
    mut v_config_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: u32 = 0;
    let mut v___y_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: u32 = 0;
    let mut v___x_3808_: u8 = 0;
    let mut v___x_3809_: u32 = 0;
    let mut v___x_3810_: u8 = 0;
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u32 = 0;
    let mut v___x_3822_: u32 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: u32 = 0;
    let mut v___x_3825_: u32 = 0;
    let mut v___x_3826_: u32 = 0;
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: u32 = 0;
    let mut v_maxSchemeLength_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u8 = 0;
    let mut v___y_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: u8 = 0;
    let mut v___y_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3854_: u8 = 0;
    let mut v___y_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: u8 = 0;
    let mut v_array_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3868_: u8 = 0;
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v_c_3880_: u8 = 0;
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: u8 = 0;
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxSchemeLength_3829_ = crate::leanh::lean_ctor_get(v_config_3792_, 0);
                v___x_3830_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3831_ = lean_nat_dec_eq(v_maxSchemeLength_3829_, v___x_3830_);
                if v___x_3831_ == 0 {
                    v_array_3859_ = crate::leanh::lean_ctor_get(v_a_3793_, 0);
                    v_idx_3860_ = crate::leanh::lean_ctor_get(v_a_3793_, 1);
                    v___x_3861_ = lean_byte_array_size(v_array_3859_);
                    v___x_3862_ = lean_nat_dec_lt(v_idx_3860_, v___x_3861_);
                    if v___x_3862_ == 0 {
                        v___x_3863_ = crate::leanh::lean_box(0);
                        v___x_3864_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3864_, 0, v_a_3793_);
                        crate::leanh::lean_ctor_set(v___x_3864_, 1, v___x_3863_);
                        return v___x_3864_;
                    } else {
                        v___f_3865_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6;
                        v_c_3880_ = lean_byte_array_fget(v_array_3859_, v_idx_3860_);
                        v___x_3881_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3882_ = lean_nat_add(v_idx_3860_, v___x_3881_);
                        crate::leanh::lean_inc_ref(v_array_3859_);
                        v_it_x27_3883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_it_x27_3883_, 0, v_array_3859_);
                        crate::leanh::lean_ctor_set(v_it_x27_3883_, 1, v___x_3882_);
                        v___x_3894_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                        v___x_3895_ = lean_uint8_dec_le(v___x_3894_, v_c_3880_);
                        if v___x_3895_ == 0 {
                            v___y_3889_ = v___x_3895_;
                            state = 9;
                            continue;
                        } else {
                            v___x_3896_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                            v___x_3897_ = lean_uint8_dec_le(v_c_3880_, v___x_3896_);
                            v___y_3889_ = v___x_3897_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v___x_3898_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10;
                    v___x_3899_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3899_, 0, v_a_3793_);
                    crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                    return v___x_3899_;
                }
            }
            1 => {
                v___x_3796_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1;
                v___x_3797_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3797_, 0, v___y_3795_);
                crate::leanh::lean_ctor_set(v___x_3797_, 1, v___x_3796_);
                return v___x_3797_;
            }
            2 => {
                if v_val_3801_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3799_);
                    v___y_3795_ = v___y_3800_;
                    state = 1;
                    continue;
                } else {
                    v___x_3802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3802_, 0, v___y_3800_);
                    crate::leanh::lean_ctor_set(v___x_3802_, 1, v___y_3799_);
                    return v___x_3802_;
                }
            }
            3 => {
                v___x_3807_ = 97;
                v___x_3808_ = lean_uint32_dec_le(v___x_3807_, v___y_3804_);
                if v___x_3808_ == 0 {
                    v___y_3799_ = v___y_3805_;
                    v___y_3800_ = v___y_3806_;
                    v_val_3801_ = v___x_3808_;
                    state = 2;
                    continue;
                } else {
                    v___x_3809_ = 122;
                    v___x_3810_ = lean_uint32_dec_le(v___y_3804_, v___x_3809_);
                    v___y_3799_ = v___y_3805_;
                    v___y_3800_ = v___y_3806_;
                    v_val_3801_ = v___x_3810_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_3815_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_3814_, v___y_3813_);
                crate::leanh::lean_inc_ref(v___x_3815_);
                v___x_3816_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_3815_);
                if v___x_3816_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3815_);
                    v___y_3795_ = v___y_3812_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v___x_3815_);
                    v___x_3817_ = lean_string_data(v___x_3815_);
                    v___x_3818_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_3817_);
                    if v___x_3818_ == 0 {
                        crate::leanh::lean_dec(v___x_3817_);
                        crate::leanh::lean_dec_ref(v___x_3815_);
                        v___y_3795_ = v___y_3812_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3819_ = l_List_head_x3f___redArg(v___x_3817_);
                        crate::leanh::lean_dec(v___x_3817_);
                        if crate::leanh::lean_obj_tag(v___x_3819_) == 0 {
                            crate::leanh::lean_dec_ref(v___x_3815_);
                            v___y_3795_ = v___y_3812_;
                            state = 1;
                            continue;
                        } else {
                            v_val_3820_ = crate::leanh::lean_ctor_get(v___x_3819_, 0);
                            crate::leanh::lean_inc(v_val_3820_);
                            crate::leanh::lean_dec_ref_known(v___x_3819_, 1);
                            v___x_3821_ = 65;
                            v___x_3822_ = crate::leanh::lean_unbox_uint32(v_val_3820_);
                            v___x_3823_ = lean_uint32_dec_le(v___x_3821_, v___x_3822_);
                            if v___x_3823_ == 0 {
                                v___x_3824_ = crate::leanh::lean_unbox_uint32(v_val_3820_);
                                crate::leanh::lean_dec(v_val_3820_);
                                v___y_3804_ = v___x_3824_;
                                v___y_3805_ = v___x_3815_;
                                v___y_3806_ = v___y_3812_;
                                state = 3;
                                continue;
                            } else {
                                v___x_3825_ = 90;
                                v___x_3826_ = crate::leanh::lean_unbox_uint32(v_val_3820_);
                                v___x_3827_ = lean_uint32_dec_le(v___x_3826_, v___x_3825_);
                                if v___x_3827_ == 0 {
                                    v___x_3828_ = crate::leanh::lean_unbox_uint32(v_val_3820_);
                                    crate::leanh::lean_dec(v_val_3820_);
                                    v___y_3804_ = v___x_3828_;
                                    v___y_3805_ = v___x_3815_;
                                    v___y_3806_ = v___y_3812_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_val_3820_);
                                    v___y_3799_ = v___x_3815_;
                                    v___y_3800_ = v___y_3812_;
                                    v_val_3801_ = v___x_3818_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_3839_ = l_ByteArray_toByteSlice(v___y_3833_, v_lower_3837_, v_upper_3838_);
                v___x_3840_ = l_ByteArray_empty;
                v___x_3841_ = lean_byte_array_push(v___x_3840_, v___y_3834_);
                v___x_3842_ = l_ByteSlice_toByteArray(v___x_3839_);
                v___x_3843_ = lean_byte_array_size(v___x_3841_);
                v___x_3844_ = lean_byte_array_size(v___x_3842_);
                crate::leanh::lean_inc(v___y_3836_);
                v___x_3845_ = lean_byte_array_copy_slice(
                    v___x_3842_,
                    v___y_3836_,
                    v___x_3841_,
                    v___x_3843_,
                    v___x_3844_,
                    v___x_3831_,
                );
                crate::leanh::lean_dec_ref(v___x_3842_);
                v___x_3846_ = lean_string_validate_utf8(v___x_3845_);
                if v___x_3846_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3845_);
                    v___x_3847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
                    v___x_3848_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_3847_);
                    v___y_3812_ = v___y_3835_;
                    v___y_3813_ = v___y_3836_;
                    v___y_3814_ = v___x_3848_;
                    state = 4;
                    continue;
                } else {
                    v___x_3849_ = lean_string_from_utf8_unchecked(v___x_3845_);
                    v___y_3812_ = v___y_3835_;
                    v___y_3813_ = v___y_3836_;
                    v___y_3814_ = v___x_3849_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_3858_ = lean_nat_dec_le(v___y_3853_, v___y_3852_);
                if v___x_3858_ == 0 {
                    crate::leanh::lean_dec(v___y_3853_);
                    v___y_3833_ = v___y_3851_;
                    v___y_3834_ = v___y_3854_;
                    v___y_3835_ = v___y_3856_;
                    v___y_3836_ = v___y_3855_;
                    v_lower_3837_ = v___y_3857_;
                    v_upper_3838_ = v___y_3852_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3852_);
                    v___y_3833_ = v___y_3851_;
                    v___y_3834_ = v___y_3854_;
                    v___y_3835_ = v___y_3856_;
                    v___y_3836_ = v___y_3855_;
                    v_lower_3837_ = v___y_3857_;
                    v_upper_3838_ = v___y_3853_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_3869_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3870_ = lean_nat_sub(v_maxSchemeLength_3829_, v___x_3869_);
                crate::leanh::lean_inc_ref(v_pos_3867_);
                v___x_3871_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3865_, v___x_3870_, v___x_3830_, v_pos_3867_);
                crate::leanh::lean_dec(v___x_3870_);
                v_snd_3872_ = crate::leanh::lean_ctor_get(v___x_3871_, 1);
                crate::leanh::lean_inc(v_snd_3872_);
                v_fst_3873_ = crate::leanh::lean_ctor_get(v___x_3871_, 0);
                crate::leanh::lean_inc(v_fst_3873_);
                crate::leanh::lean_dec_ref(v___x_3871_);
                v_fst_3874_ = crate::leanh::lean_ctor_get(v_snd_3872_, 0);
                crate::leanh::lean_inc(v_fst_3874_);
                crate::leanh::lean_dec(v_snd_3872_);
                v_array_3875_ = crate::leanh::lean_ctor_get(v_pos_3867_, 0);
                crate::leanh::lean_inc_ref(v_array_3875_);
                v_idx_3876_ = crate::leanh::lean_ctor_get(v_pos_3867_, 1);
                crate::leanh::lean_inc(v_idx_3876_);
                crate::leanh::lean_dec_ref(v_pos_3867_);
                v___x_3877_ = lean_nat_add(v_idx_3876_, v_fst_3873_);
                crate::leanh::lean_dec(v_fst_3873_);
                v___x_3878_ = lean_byte_array_size(v_array_3875_);
                v___x_3879_ = lean_nat_dec_le(v_idx_3876_, v___x_3830_);
                if v___x_3879_ == 0 {
                    v___y_3851_ = v_array_3875_;
                    v___y_3852_ = v___x_3878_;
                    v___y_3853_ = v___x_3877_;
                    v___y_3854_ = v_res_3868_;
                    v___y_3855_ = v___x_3830_;
                    v___y_3856_ = v_fst_3874_;
                    v___y_3857_ = v_idx_3876_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_3876_);
                    v___y_3851_ = v_array_3875_;
                    v___y_3852_ = v___x_3878_;
                    v___y_3853_ = v___x_3877_;
                    v___y_3854_ = v_res_3868_;
                    v___y_3855_ = v___x_3830_;
                    v___y_3856_ = v_fst_3874_;
                    v___y_3857_ = v___x_3830_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v___y_3885_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_it_x27_3883_, 2);
                    v___x_3886_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8;
                    v___x_3887_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3887_, 0, v_a_3793_);
                    crate::leanh::lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                    return v___x_3887_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_3793_);
                    v_pos_3867_ = v_it_x27_3883_;
                    v_res_3868_ = v_c_3880_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3889_ == 0 {
                    v___x_3890_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_3891_ = lean_uint8_dec_le(v___x_3890_, v_c_3880_);
                    if v___x_3891_ == 0 {
                        v___y_3885_ = v___x_3891_;
                        state = 8;
                        continue;
                    } else {
                        v___x_3892_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_3893_ = lean_uint8_dec_le(v_c_3880_, v___x_3892_);
                        v___y_3885_ = v___x_3893_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_3793_);
                    v_pos_3867_ = v_it_x27_3883_;
                    v_res_3868_ = v_c_3880_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(
    mut v_config_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(
        v_config_3900_,
        v_a_3901_,
    );
    crate::leanh::lean_dec_ref(v_config_3900_);
    return v_res_3902_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(
    mut v___y_3903_: u8,
) -> u8 {
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: u8 = 0;
    v___x_3904_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
    v___x_3905_ = lean_uint8_dec_le(v___x_3904_, v___y_3903_);
    if v___x_3905_ == 0 {
        return v___x_3905_;
    } else {
        let mut v___x_3906_: u8 = 0;
        let mut v___x_3907_: u8 = 0;
        v___x_3906_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
        v___x_3907_ = lean_uint8_dec_le(v___y_3903_, v___x_3906_);
        return v___x_3907_;
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(
    mut v___y_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_582__boxed_3909_: u8 = 0;
    let mut v_res_3910_: u8 = 0;
    let mut v_r_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_582__boxed_3909_ = (crate::leanh::lean_unbox(v___y_3908_) as u8);
    v_res_3910_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(
            v___y_582__boxed_3909_,
        );
    v_r_3911_ = crate::leanh::lean_box((v_res_3910_) as usize);
    return v_r_3911_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(
    mut v_a_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___y_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: u8 = 0;
    let mut v___x_3937_: u16 = 0;
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3951_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    let mut v___x_3974_: u8 = 0;
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v_unused_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3916_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0;
                v___x_3917_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_3918_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_3915_);
                v___x_3919_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3916_, v___x_3917_, v___x_3918_, v_a_3915_);
                v_snd_3920_ = crate::leanh::lean_ctor_get(v___x_3919_, 1);
                crate::leanh::lean_inc(v_snd_3920_);
                v_fst_3921_ = crate::leanh::lean_ctor_get(v___x_3919_, 0);
                crate::leanh::lean_inc(v_fst_3921_);
                crate::leanh::lean_dec_ref(v___x_3919_);
                v_fst_3922_ = crate::leanh::lean_ctor_get(v_snd_3920_, 0);
                v_isSharedCheck_3975_ = (!crate::leanh::lean_is_exclusive(v_snd_3920_)) as u8;
                if v_isSharedCheck_3975_ == 0 {
                    v_unused_3976_ = crate::leanh::lean_ctor_get(v_snd_3920_, 1);
                    crate::leanh::lean_dec(v_unused_3976_);
                    v___x_3924_ = v_snd_3920_;
                    v_isShared_3925_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3922_);
                    crate::leanh::lean_dec(v_snd_3920_);
                    v___x_3924_ = crate::leanh::lean_box(0);
                    v_isShared_3925_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_3958_ = crate::leanh::lean_ctor_get(v_a_3915_, 0);
                crate::leanh::lean_inc_ref(v_array_3958_);
                v_idx_3959_ = crate::leanh::lean_ctor_get(v_a_3915_, 1);
                crate::leanh::lean_inc(v_idx_3959_);
                crate::leanh::lean_dec_ref(v_a_3915_);
                v___x_3969_ = lean_nat_add(v_idx_3959_, v_fst_3921_);
                crate::leanh::lean_dec(v_fst_3921_);
                v___x_3970_ = lean_byte_array_size(v_array_3958_);
                v___x_3974_ = lean_nat_dec_le(v_idx_3959_, v___x_3918_);
                if v___x_3974_ == 0 {
                    v___y_3972_ = v_idx_3959_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_3959_);
                    v___y_3972_ = v___x_3918_;
                    state = 9;
                    continue;
                }
            }
            2 => {
                v___x_3928_ = lean_string_utf8_byte_size(v___y_3927_);
                crate::leanh::lean_inc_ref(v___y_3927_);
                v___x_3929_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3929_, 0, v___y_3927_);
                crate::leanh::lean_ctor_set(v___x_3929_, 1, v___x_3918_);
                crate::leanh::lean_ctor_set(v___x_3929_, 2, v___x_3928_);
                v___x_3930_ = l_String_Slice_toNat_x3f(v___x_3929_);
                crate::leanh::lean_dec_ref_known(v___x_3929_, 3);
                if crate::leanh::lean_obj_tag(v___x_3930_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_3927_);
                    v_val_3931_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                    v_isSharedCheck_3951_ = (!crate::leanh::lean_is_exclusive(v___x_3930_)) as u8;
                    if v_isSharedCheck_3951_ == 0 {
                        v___x_3933_ = v___x_3930_;
                        v_isShared_3934_ = v_isSharedCheck_3951_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3931_);
                        crate::leanh::lean_dec(v___x_3930_);
                        v___x_3933_ = crate::leanh::lean_box(0);
                        v_isShared_3934_ = v_isSharedCheck_3951_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3930_);
                    v___x_3952_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2;
                    v___x_3953_ = lean_string_append(v___x_3952_, v___y_3927_);
                    crate::leanh::lean_dec_ref(v___y_3927_);
                    v___x_3954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3953_);
                    if v_isShared_3925_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3924_, 1);
                        crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3954_);
                        v___x_3956_ = v___x_3924_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_fst_3922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3954_);
                        v___x_3956_ = v_reuseFailAlloc_3957_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3935_ = crate::leanh::lean_unsigned_to_nat(65535);
                v___x_3936_ = lean_nat_dec_lt(v___x_3935_, v_val_3931_);
                if v___x_3936_ == 0 {
                    crate::leanh::lean_del_object(v___x_3933_);
                    v___x_3937_ = lean_uint16_of_nat(v_val_3931_);
                    crate::leanh::lean_dec(v_val_3931_);
                    v___x_3938_ = crate::leanh::lean_box((v___x_3937_) as usize);
                    if v_isShared_3925_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3938_);
                        v___x_3940_ = v___x_3924_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fst_3922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 1, v___x_3938_);
                        v___x_3940_ = v_reuseFailAlloc_3941_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3942_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1;
                    v___x_3943_ = l_Nat_reprFast(v_val_3931_);
                    v___x_3944_ = lean_string_append(v___x_3942_, v___x_3943_);
                    crate::leanh::lean_dec_ref(v___x_3943_);
                    if v_isShared_3934_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3944_);
                        v___x_3946_ = v___x_3933_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3944_);
                        v___x_3946_ = v_reuseFailAlloc_3950_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3940_;
            }
            5 => {
                if v_isShared_3925_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3924_, 1);
                    crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3946_);
                    v___x_3948_ = v___x_3924_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3949_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_fst_3922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3949_, 1, v___x_3946_);
                    v___x_3948_ = v_reuseFailAlloc_3949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3948_;
            }
            7 => {
                return v___x_3956_;
            }
            8 => {
                v___x_3963_ = l_ByteArray_toByteSlice(v_array_3958_, v_lower_3961_, v_upper_3962_);
                v___x_3964_ = l_ByteSlice_toByteArray(v___x_3963_);
                v___x_3965_ = lean_string_validate_utf8(v___x_3964_);
                if v___x_3965_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3964_);
                    v___x_3966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
                    v___x_3967_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_3966_);
                    v___y_3927_ = v___x_3967_;
                    state = 2;
                    continue;
                } else {
                    v___x_3968_ = lean_string_from_utf8_unchecked(v___x_3964_);
                    v___y_3927_ = v___x_3968_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v___x_3973_ = lean_nat_dec_le(v___x_3969_, v___x_3970_);
                if v___x_3973_ == 0 {
                    crate::leanh::lean_dec(v___x_3969_);
                    v_lower_3961_ = v___y_3972_;
                    v_upper_3962_ = v___x_3970_;
                    state = 8;
                    continue;
                } else {
                    v_lower_3961_ = v___y_3972_;
                    v_upper_3962_ = v___x_3969_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0()
-> u8 {
    let mut v___x_3977_: u32 = 0;
    let mut v___x_3978_: u8 = 0;
    v___x_3977_ = 58;
    v___x_3978_ = lean_uint32_to_uint8(v___x_3977_);
    return v___x_3978_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1()
-> u8 {
    let mut v___x_3979_: u32 = 0;
    let mut v___x_3980_: u8 = 0;
    v___x_3979_ = 37;
    v___x_3980_ = lean_uint32_to_uint8(v___x_3979_);
    return v___x_3980_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2()
-> u8 {
    let mut v___x_3981_: u32 = 0;
    let mut v___x_3982_: u8 = 0;
    v___x_3981_ = 38;
    v___x_3982_ = lean_uint32_to_uint8(v___x_3981_);
    return v___x_3982_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3()
-> u8 {
    let mut v___x_3983_: u32 = 0;
    let mut v___x_3984_: u8 = 0;
    v___x_3983_ = 39;
    v___x_3984_ = lean_uint32_to_uint8(v___x_3983_);
    return v___x_3984_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4()
-> u8 {
    let mut v___x_3985_: u32 = 0;
    let mut v___x_3986_: u8 = 0;
    v___x_3985_ = 40;
    v___x_3986_ = lean_uint32_to_uint8(v___x_3985_);
    return v___x_3986_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5()
-> u8 {
    let mut v___x_3987_: u32 = 0;
    let mut v___x_3988_: u8 = 0;
    v___x_3987_ = 41;
    v___x_3988_ = lean_uint32_to_uint8(v___x_3987_);
    return v___x_3988_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6()
-> u8 {
    let mut v___x_3989_: u32 = 0;
    let mut v___x_3990_: u8 = 0;
    v___x_3989_ = 42;
    v___x_3990_ = lean_uint32_to_uint8(v___x_3989_);
    return v___x_3990_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7()
-> u8 {
    let mut v___x_3991_: u32 = 0;
    let mut v___x_3992_: u8 = 0;
    v___x_3991_ = 44;
    v___x_3992_ = lean_uint32_to_uint8(v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8()
-> u8 {
    let mut v___x_3993_: u32 = 0;
    let mut v___x_3994_: u8 = 0;
    v___x_3993_ = 59;
    v___x_3994_ = lean_uint32_to_uint8(v___x_3993_);
    return v___x_3994_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9()
-> u8 {
    let mut v___x_3995_: u32 = 0;
    let mut v___x_3996_: u8 = 0;
    v___x_3995_ = 61;
    v___x_3996_ = lean_uint32_to_uint8(v___x_3995_);
    return v___x_3996_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10()
-> u8 {
    let mut v___x_3997_: u32 = 0;
    let mut v___x_3998_: u8 = 0;
    v___x_3997_ = 33;
    v___x_3998_ = lean_uint32_to_uint8(v___x_3997_);
    return v___x_3998_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11()
-> u8 {
    let mut v___x_3999_: u32 = 0;
    let mut v___x_4000_: u8 = 0;
    v___x_3999_ = 36;
    v___x_4000_ = lean_uint32_to_uint8(v___x_3999_);
    return v___x_4000_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12()
-> u8 {
    let mut v___x_4001_: u32 = 0;
    let mut v___x_4002_: u8 = 0;
    v___x_4001_ = 95;
    v___x_4002_ = lean_uint32_to_uint8(v___x_4001_);
    return v___x_4002_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13()
-> u8 {
    let mut v___x_4003_: u32 = 0;
    let mut v___x_4004_: u8 = 0;
    v___x_4003_ = 126;
    v___x_4004_ = lean_uint32_to_uint8(v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(
    mut v_x_4005_: u8,
) -> u8 {
    let mut v___y_4007_: u8 = 0;
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4011_: u8 = 0;
    let mut v___y_4013_: u8 = 0;
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: u8 = 0;
    let mut v___x_4016_: u8 = 0;
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: u8 = 0;
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4025_: u8 = 0;
    let mut v___x_4026_: u8 = 0;
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: u8 = 0;
    let mut v___y_4033_: u8 = 0;
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: u8 = 0;
    let mut v___y_4039_: u8 = 0;
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: u8 = 0;
    let mut v___y_4045_: u8 = 0;
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: u8 = 0;
    let mut v___y_4051_: u8 = 0;
    let mut v___x_4052_: u8 = 0;
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: u8 = 0;
    let mut v___y_4057_: u8 = 0;
    let mut v___x_4058_: u8 = 0;
    let mut v___x_4059_: u8 = 0;
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: u8 = 0;
    let mut v___x_4064_: u8 = 0;
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: u8 = 0;
    let mut v___x_4067_: u8 = 0;
    let mut v___x_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4062_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                v___x_4063_ = lean_uint8_dec_eq(v_x_4005_, v___x_4062_);
                if v___x_4063_ == 0 {
                    v___x_4064_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                    v___x_4065_ = lean_uint8_dec_le(v___x_4064_, v_x_4005_);
                    if v___x_4065_ == 0 {
                        v___y_4057_ = v___x_4065_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4066_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                        v___x_4067_ = lean_uint8_dec_le(v_x_4005_, v___x_4066_);
                        v___y_4057_ = v___x_4067_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_4068_ = 0;
                    return v___x_4068_;
                }
            }
            1 => {
                if v___y_4007_ == 0 {
                    v___x_4008_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_4009_ = lean_uint8_dec_eq(v_x_4005_, v___x_4008_);
                    if v___x_4009_ == 0 {
                        v___x_4010_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                        v___x_4011_ = lean_uint8_dec_eq(v_x_4005_, v___x_4010_);
                        if v___x_4011_ == 0 {
                            return v___x_4009_;
                        } else {
                            return v___x_4011_;
                        }
                    } else {
                        return v___x_4009_;
                    }
                } else {
                    return v___y_4007_;
                }
            }
            2 => {
                if v___y_4013_ == 0 {
                    v___x_4014_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_4015_ = lean_uint8_dec_eq(v_x_4005_, v___x_4014_);
                    if v___x_4015_ == 0 {
                        v___x_4016_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_4017_ = lean_uint8_dec_eq(v_x_4005_, v___x_4016_);
                        if v___x_4017_ == 0 {
                            v___x_4018_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_4019_ = lean_uint8_dec_eq(v_x_4005_, v___x_4018_);
                            if v___x_4019_ == 0 {
                                v___x_4020_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_4021_ = lean_uint8_dec_eq(v_x_4005_, v___x_4020_);
                                if v___x_4021_ == 0 {
                                    v___x_4022_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_4023_ = lean_uint8_dec_eq(v_x_4005_, v___x_4022_);
                                    if v___x_4023_ == 0 {
                                        v___x_4024_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_4025_ = lean_uint8_dec_eq(v_x_4005_, v___x_4024_);
                                        if v___x_4025_ == 0 {
                                            v___x_4026_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_4027_ = lean_uint8_dec_eq(v_x_4005_, v___x_4026_);
                                            if v___x_4027_ == 0 {
                                                v___x_4028_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_4029_ =
                                                    lean_uint8_dec_eq(v_x_4005_, v___x_4028_);
                                                if v___x_4029_ == 0 {
                                                    v___x_4030_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_4031_ =
                                                        lean_uint8_dec_eq(v_x_4005_, v___x_4030_);
                                                    v___y_4007_ = v___x_4031_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_4007_ = v___x_4029_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_4007_ = v___x_4027_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_4007_ = v___x_4025_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_4007_ = v___x_4023_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_4007_ = v___x_4021_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_4007_ = v___x_4019_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_4007_ = v___x_4017_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4007_ = v___x_4015_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_4013_;
                }
            }
            3 => {
                if v___y_4033_ == 0 {
                    v___x_4034_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_4035_ = lean_uint8_dec_eq(v_x_4005_, v___x_4034_);
                    if v___x_4035_ == 0 {
                        v___x_4036_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_4037_ = lean_uint8_dec_eq(v_x_4005_, v___x_4036_);
                        v___y_4013_ = v___x_4037_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4013_ = v___x_4035_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_4033_;
                }
            }
            4 => {
                if v___y_4039_ == 0 {
                    v___x_4040_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_4041_ = lean_uint8_dec_eq(v_x_4005_, v___x_4040_);
                    if v___x_4041_ == 0 {
                        v___x_4042_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_4043_ = lean_uint8_dec_eq(v_x_4005_, v___x_4042_);
                        v___y_4033_ = v___x_4043_;
                        state = 3;
                        continue;
                    } else {
                        v___y_4033_ = v___x_4041_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_4039_;
                }
            }
            5 => {
                if v___y_4045_ == 0 {
                    v___x_4046_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_4047_ = lean_uint8_dec_eq(v_x_4005_, v___x_4046_);
                    if v___x_4047_ == 0 {
                        v___x_4048_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_4049_ = lean_uint8_dec_eq(v_x_4005_, v___x_4048_);
                        v___y_4039_ = v___x_4049_;
                        state = 4;
                        continue;
                    } else {
                        v___y_4039_ = v___x_4047_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_4045_;
                }
            }
            6 => {
                if v___y_4051_ == 0 {
                    v___x_4052_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_4053_ = lean_uint8_dec_le(v___x_4052_, v_x_4005_);
                    if v___x_4053_ == 0 {
                        v___y_4045_ = v___x_4053_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4054_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_4055_ = lean_uint8_dec_le(v_x_4005_, v___x_4054_);
                        v___y_4045_ = v___x_4055_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_4051_;
                }
            }
            7 => {
                if v___y_4057_ == 0 {
                    v___x_4058_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_4059_ = lean_uint8_dec_le(v___x_4058_, v_x_4005_);
                    if v___x_4059_ == 0 {
                        v___y_4051_ = v___x_4059_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4060_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_4061_ = lean_uint8_dec_le(v_x_4005_, v___x_4060_);
                        v___y_4051_ = v___x_4061_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_4057_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(
    mut v_x_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4070_: u8 = 0;
    let mut v_res_4071_: u8 = 0;
    let mut v_r_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4070_ = (crate::leanh::lean_unbox(v_x_4069_) as u8);
    v_res_4071_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(
            v_x_boxed_4070_,
        );
    v_r_4072_ = crate::leanh::lean_box((v_res_4071_) as usize);
    return v_r_4072_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(
    mut v___x_4073_: u8,
    mut v___x_4074_: u8,
    mut v_x_4075_: u8,
) -> u8 {
    let mut v___y_4077_: u8 = 0;
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___y_4082_: u8 = 0;
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: u8 = 0;
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: u8 = 0;
    let mut v___y_4102_: u8 = 0;
    let mut v___x_4103_: u8 = 0;
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___y_4108_: u8 = 0;
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: u8 = 0;
    let mut v___y_4114_: u8 = 0;
    let mut v___x_4115_: u8 = 0;
    let mut v___x_4116_: u8 = 0;
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: u8 = 0;
    let mut v___y_4120_: u8 = 0;
    let mut v___x_4121_: u8 = 0;
    let mut v___x_4122_: u8 = 0;
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: u8 = 0;
    let mut v___y_4126_: u8 = 0;
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: u8 = 0;
    let mut v___x_4131_: u8 = 0;
    let mut v___x_4132_: u8 = 0;
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4131_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_4132_ = lean_uint8_dec_le(v___x_4131_, v_x_4075_);
                if v___x_4132_ == 0 {
                    v___y_4126_ = v___x_4132_;
                    state = 7;
                    continue;
                } else {
                    v___x_4133_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_4134_ = lean_uint8_dec_le(v_x_4075_, v___x_4133_);
                    v___y_4126_ = v___x_4134_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_4077_ == 0 {
                    v___x_4078_ = lean_uint8_dec_eq(v_x_4075_, v___x_4073_);
                    if v___x_4078_ == 0 {
                        v___x_4079_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                        v___x_4080_ = lean_uint8_dec_eq(v_x_4075_, v___x_4079_);
                        if v___x_4080_ == 0 {
                            return v___x_4078_;
                        } else {
                            return v___x_4074_;
                        }
                    } else {
                        return v___x_4078_;
                    }
                } else {
                    return v___y_4077_;
                }
            }
            2 => {
                if v___y_4082_ == 0 {
                    v___x_4083_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_4084_ = lean_uint8_dec_eq(v_x_4075_, v___x_4083_);
                    if v___x_4084_ == 0 {
                        v___x_4085_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_4086_ = lean_uint8_dec_eq(v_x_4075_, v___x_4085_);
                        if v___x_4086_ == 0 {
                            v___x_4087_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_4088_ = lean_uint8_dec_eq(v_x_4075_, v___x_4087_);
                            if v___x_4088_ == 0 {
                                v___x_4089_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_4090_ = lean_uint8_dec_eq(v_x_4075_, v___x_4089_);
                                if v___x_4090_ == 0 {
                                    v___x_4091_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_4092_ = lean_uint8_dec_eq(v_x_4075_, v___x_4091_);
                                    if v___x_4092_ == 0 {
                                        v___x_4093_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_4094_ = lean_uint8_dec_eq(v_x_4075_, v___x_4093_);
                                        if v___x_4094_ == 0 {
                                            v___x_4095_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_4096_ = lean_uint8_dec_eq(v_x_4075_, v___x_4095_);
                                            if v___x_4096_ == 0 {
                                                v___x_4097_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_4098_ =
                                                    lean_uint8_dec_eq(v_x_4075_, v___x_4097_);
                                                if v___x_4098_ == 0 {
                                                    v___x_4099_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_4100_ =
                                                        lean_uint8_dec_eq(v_x_4075_, v___x_4099_);
                                                    v___y_4077_ = v___x_4100_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_4077_ = v___x_4098_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_4077_ = v___x_4096_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_4077_ = v___x_4094_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_4077_ = v___x_4092_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_4077_ = v___x_4090_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_4077_ = v___x_4088_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_4077_ = v___x_4086_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4077_ = v___x_4084_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_4082_;
                }
            }
            3 => {
                if v___y_4102_ == 0 {
                    v___x_4103_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_4104_ = lean_uint8_dec_eq(v_x_4075_, v___x_4103_);
                    if v___x_4104_ == 0 {
                        v___x_4105_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_4106_ = lean_uint8_dec_eq(v_x_4075_, v___x_4105_);
                        v___y_4082_ = v___x_4106_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4082_ = v___x_4104_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_4102_;
                }
            }
            4 => {
                if v___y_4108_ == 0 {
                    v___x_4109_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_4110_ = lean_uint8_dec_eq(v_x_4075_, v___x_4109_);
                    if v___x_4110_ == 0 {
                        v___x_4111_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_4112_ = lean_uint8_dec_eq(v_x_4075_, v___x_4111_);
                        v___y_4102_ = v___x_4112_;
                        state = 3;
                        continue;
                    } else {
                        v___y_4102_ = v___x_4110_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_4108_;
                }
            }
            5 => {
                if v___y_4114_ == 0 {
                    v___x_4115_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_4116_ = lean_uint8_dec_eq(v_x_4075_, v___x_4115_);
                    if v___x_4116_ == 0 {
                        v___x_4117_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_4118_ = lean_uint8_dec_eq(v_x_4075_, v___x_4117_);
                        v___y_4108_ = v___x_4118_;
                        state = 4;
                        continue;
                    } else {
                        v___y_4108_ = v___x_4116_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_4114_;
                }
            }
            6 => {
                if v___y_4120_ == 0 {
                    v___x_4121_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_4122_ = lean_uint8_dec_le(v___x_4121_, v_x_4075_);
                    if v___x_4122_ == 0 {
                        v___y_4114_ = v___x_4122_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4123_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_4124_ = lean_uint8_dec_le(v_x_4075_, v___x_4123_);
                        v___y_4114_ = v___x_4124_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_4120_;
                }
            }
            7 => {
                if v___y_4126_ == 0 {
                    v___x_4127_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_4128_ = lean_uint8_dec_le(v___x_4127_, v_x_4075_);
                    if v___x_4128_ == 0 {
                        v___y_4120_ = v___x_4128_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4129_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_4130_ = lean_uint8_dec_le(v_x_4075_, v___x_4129_);
                        v___y_4120_ = v___x_4130_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_4126_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(
    mut v___x_4135_: *mut crate::leanh::LeanObject,
    mut v___x_4136_: *mut crate::leanh::LeanObject,
    mut v_x_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665__boxed_4138_: u8 = 0;
    let mut v___x_4666__boxed_4139_: u8 = 0;
    let mut v_x_boxed_4140_: u8 = 0;
    let mut v_res_4141_: u8 = 0;
    let mut v_r_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665__boxed_4138_ = (crate::leanh::lean_unbox(v___x_4135_) as u8);
    v___x_4666__boxed_4139_ = (crate::leanh::lean_unbox(v___x_4136_) as u8);
    v_x_boxed_4140_ = (crate::leanh::lean_unbox(v_x_4137_) as u8);
    v_res_4141_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(
            v___x_4665__boxed_4138_,
            v___x_4666__boxed_4139_,
            v_x_boxed_4140_,
        );
    v_r_4142_ = crate::leanh::lean_box((v_res_4141_) as usize);
    return v_r_4142_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(
    mut v_config_4147_: *mut crate::leanh::LeanObject,
    mut v_a_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userPassEncoded_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___y_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUserInfoLength_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v_lower_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: u8 = 0;
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4202_: u8 = 0;
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4210_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: u8 = 0;
    let mut v_reuseFailAlloc_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_unused_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: u8 = 0;
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxUserInfoLength_4178_ = crate::leanh::lean_ctor_get(v_config_4147_, 2);
                v___f_4179_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2;
                v___x_4180_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_4148_);
                v___x_4181_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4179_, v_maxUserInfoLength_4178_, v___x_4180_, v_a_4148_);
                v_snd_4182_ = crate::leanh::lean_ctor_get(v___x_4181_, 1);
                crate::leanh::lean_inc(v_snd_4182_);
                v_fst_4183_ = crate::leanh::lean_ctor_get(v___x_4181_, 0);
                crate::leanh::lean_inc(v_fst_4183_);
                crate::leanh::lean_dec_ref(v___x_4181_);
                v_fst_4184_ = crate::leanh::lean_ctor_get(v_snd_4182_, 0);
                crate::leanh::lean_inc(v_fst_4184_);
                crate::leanh::lean_dec(v_snd_4182_);
                v_array_4185_ = crate::leanh::lean_ctor_get(v_a_4148_, 0);
                v_idx_4186_ = crate::leanh::lean_ctor_get(v_a_4148_, 1);
                v_isSharedCheck_4238_ = (!crate::leanh::lean_is_exclusive(v_a_4148_)) as u8;
                if v_isSharedCheck_4238_ == 0 {
                    v___x_4188_ = v_a_4148_;
                    v_isShared_4189_ = v_isSharedCheck_4238_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_4186_);
                    crate::leanh::lean_inc(v_array_4185_);
                    crate::leanh::lean_dec(v_a_4148_);
                    v___x_4188_ = crate::leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4238_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_4153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4153_, 0, v___y_4150_);
                crate::leanh::lean_ctor_set(v___x_4153_, 1, v_userPassEncoded_4151_);
                v___x_4154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4154_, 0, v___y_4152_);
                crate::leanh::lean_ctor_set(v___x_4154_, 1, v___x_4153_);
                return v___x_4154_;
            }
            2 => {
                v___x_4161_ = l_ByteArray_toByteSlice(v___y_4157_, v_lower_4159_, v_upper_4160_);
                v___x_4162_ = l_ByteSlice_toByteArray(v___x_4161_);
                v___x_4163_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_4162_);
                if crate::leanh::lean_obj_tag(v___x_4163_) == 1 {
                    v___y_4150_ = v___y_4158_;
                    v_userPassEncoded_4151_ = v___x_4163_;
                    v___y_4152_ = v___y_4156_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4163_);
                    crate::leanh::lean_dec_ref(v___y_4158_);
                    v___x_4164_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1;
                    v___x_4165_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4165_, 0, v___y_4156_);
                    crate::leanh::lean_ctor_set(v___x_4165_, 1, v___x_4164_);
                    return v___x_4165_;
                }
            }
            3 => {
                v___x_4173_ = lean_nat_dec_le(v___y_4168_, v___y_4171_);
                if v___x_4173_ == 0 {
                    crate::leanh::lean_dec(v___y_4168_);
                    v___y_4156_ = v___y_4167_;
                    v___y_4157_ = v___y_4169_;
                    v___y_4158_ = v___y_4170_;
                    v_lower_4159_ = v___y_4172_;
                    v_upper_4160_ = v___y_4171_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_4171_);
                    v___y_4156_ = v___y_4167_;
                    v___y_4157_ = v___y_4169_;
                    v___y_4158_ = v___y_4170_;
                    v_lower_4159_ = v___y_4172_;
                    v_upper_4160_ = v___y_4168_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4177_ = crate::leanh::lean_box(0);
                v___y_4150_ = v___y_4175_;
                v_userPassEncoded_4151_ = v___x_4177_;
                v___y_4152_ = v_pos_4176_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4232_ = lean_nat_add(v_idx_4186_, v_fst_4183_);
                crate::leanh::lean_dec(v_fst_4183_);
                v___x_4233_ = lean_byte_array_size(v_array_4185_);
                v___x_4237_ = lean_nat_dec_le(v_idx_4186_, v___x_4180_);
                if v___x_4237_ == 0 {
                    v___y_4235_ = v_idx_4186_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_4186_);
                    v___y_4235_ = v___x_4180_;
                    state = 11;
                    continue;
                }
            }
            6 => {
                v___x_4193_ = l_ByteArray_toByteSlice(v_array_4185_, v_lower_4191_, v_upper_4192_);
                v___x_4194_ = l_ByteSlice_toByteArray(v___x_4193_);
                v___x_4195_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_4194_);
                if crate::leanh::lean_obj_tag(v___x_4195_) == 1 {
                    v_val_4196_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                    crate::leanh::lean_inc(v_val_4196_);
                    crate::leanh::lean_dec_ref_known(v___x_4195_, 1);
                    v_array_4197_ = crate::leanh::lean_ctor_get(v_fst_4184_, 0);
                    v_idx_4198_ = crate::leanh::lean_ctor_get(v_fst_4184_, 1);
                    v___x_4199_ = lean_byte_array_size(v_array_4197_);
                    v___x_4200_ = lean_nat_dec_lt(v_idx_4198_, v___x_4199_);
                    if v___x_4200_ == 0 {
                        crate::leanh::lean_del_object(v___x_4188_);
                        v___y_4175_ = v_val_4196_;
                        v_pos_4176_ = v_fst_4184_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4201_ = lean_byte_array_fget(v_array_4197_, v_idx_4198_);
                        v___x_4202_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                        v___x_4203_ = lean_uint8_dec_eq(v___x_4201_, v___x_4202_);
                        if v___x_4203_ == 0 {
                            crate::leanh::lean_del_object(v___x_4188_);
                            v___y_4175_ = v_val_4196_;
                            v_pos_4176_ = v_fst_4184_;
                            state = 4;
                            continue;
                        } else {
                            if v___x_4203_ == 0 {
                                crate::leanh::lean_del_object(v___x_4188_);
                                v___y_4175_ = v_val_4196_;
                                v_pos_4176_ = v_fst_4184_;
                                state = 4;
                                continue;
                            } else {
                                if v___x_4200_ == 0 {
                                    crate::leanh::lean_dec(v_val_4196_);
                                    v___x_4204_ = crate::leanh::lean_box(0);
                                    if v_isShared_4189_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_4188_, 1);
                                        crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4204_);
                                        crate::leanh::lean_ctor_set(v___x_4188_, 0, v_fst_4184_);
                                        v___x_4206_ = v___x_4188_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4207_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4207_,
                                            0,
                                            v_fst_4184_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4207_,
                                            1,
                                            v___x_4204_,
                                        );
                                        v___x_4206_ = v_reuseFailAlloc_4207_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_idx_4198_);
                                    crate::leanh::lean_inc_ref(v_array_4197_);
                                    crate::leanh::lean_del_object(v___x_4188_);
                                    v_isSharedCheck_4225_ =
                                        (!crate::leanh::lean_is_exclusive(v_fst_4184_)) as u8;
                                    if v_isSharedCheck_4225_ == 0 {
                                        v_unused_4226_ =
                                            crate::leanh::lean_ctor_get(v_fst_4184_, 1);
                                        crate::leanh::lean_dec(v_unused_4226_);
                                        v_unused_4227_ =
                                            crate::leanh::lean_ctor_get(v_fst_4184_, 0);
                                        crate::leanh::lean_dec(v_unused_4227_);
                                        v___x_4209_ = v_fst_4184_;
                                        v_isShared_4210_ = v_isSharedCheck_4225_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_fst_4184_);
                                        v___x_4209_ = crate::leanh::lean_box(0);
                                        v_isShared_4210_ = v_isSharedCheck_4225_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4195_);
                    v___x_4228_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1;
                    if v_isShared_4189_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4188_, 1);
                        crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4228_);
                        crate::leanh::lean_ctor_set(v___x_4188_, 0, v_fst_4184_);
                        v___x_4230_ = v___x_4188_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_fst_4184_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___x_4228_);
                        v___x_4230_ = v_reuseFailAlloc_4231_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4206_;
            }
            8 => {
                v___x_4211_ = crate::leanh::lean_box((v___x_4202_) as usize);
                v___x_4212_ = crate::leanh::lean_box((v___x_4200_) as usize);
                v___f_4213_ = crate::leanh::lean_alloc_closure(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_4213_, 0, v___x_4211_);
                crate::leanh::lean_closure_set(v___f_4213_, 1, v___x_4212_);
                v___x_4214_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4215_ = lean_nat_add(v_idx_4198_, v___x_4214_);
                crate::leanh::lean_dec(v_idx_4198_);
                crate::leanh::lean_inc(v___x_4215_);
                crate::leanh::lean_inc_ref(v_array_4197_);
                if v_isShared_4210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4215_);
                    v___x_4217_ = v___x_4209_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_array_4197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4215_);
                    v___x_4217_ = v_reuseFailAlloc_4224_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4218_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4213_, v_maxUserInfoLength_4178_, v___x_4180_, v___x_4217_);
                v_snd_4219_ = crate::leanh::lean_ctor_get(v___x_4218_, 1);
                crate::leanh::lean_inc(v_snd_4219_);
                v_fst_4220_ = crate::leanh::lean_ctor_get(v___x_4218_, 0);
                crate::leanh::lean_inc(v_fst_4220_);
                crate::leanh::lean_dec_ref(v___x_4218_);
                v_fst_4221_ = crate::leanh::lean_ctor_get(v_snd_4219_, 0);
                crate::leanh::lean_inc(v_fst_4221_);
                crate::leanh::lean_dec(v_snd_4219_);
                v___x_4222_ = lean_nat_add(v___x_4215_, v_fst_4220_);
                crate::leanh::lean_dec(v_fst_4220_);
                v___x_4223_ = lean_nat_dec_le(v___x_4215_, v___x_4180_);
                if v___x_4223_ == 0 {
                    v___y_4167_ = v_fst_4221_;
                    v___y_4168_ = v___x_4222_;
                    v___y_4169_ = v_array_4197_;
                    v___y_4170_ = v_val_4196_;
                    v___y_4171_ = v___x_4199_;
                    v___y_4172_ = v___x_4215_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4215_);
                    v___y_4167_ = v_fst_4221_;
                    v___y_4168_ = v___x_4222_;
                    v___y_4169_ = v_array_4197_;
                    v___y_4170_ = v_val_4196_;
                    v___y_4171_ = v___x_4199_;
                    v___y_4172_ = v___x_4180_;
                    state = 3;
                    continue;
                }
            }
            10 => {
                return v___x_4230_;
            }
            11 => {
                v___x_4236_ = lean_nat_dec_le(v___x_4232_, v___x_4233_);
                if v___x_4236_ == 0 {
                    crate::leanh::lean_dec(v___x_4232_);
                    v_lower_4191_ = v___y_4235_;
                    v_upper_4192_ = v___x_4233_;
                    state = 6;
                    continue;
                } else {
                    v_lower_4191_ = v___y_4235_;
                    v_upper_4192_ = v___x_4232_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(
    mut v_config_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4241_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(
        v_config_4239_,
        v_a_4240_,
    );
    crate::leanh::lean_dec_ref(v_config_4239_);
    return v_res_4241_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0()
-> u8 {
    let mut v___x_4242_: u32 = 0;
    let mut v___x_4243_: u8 = 0;
    v___x_4242_ = 70;
    v___x_4243_ = lean_uint32_to_uint8(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1()
-> u8 {
    let mut v___x_4244_: u32 = 0;
    let mut v___x_4245_: u8 = 0;
    v___x_4244_ = 102;
    v___x_4245_ = lean_uint32_to_uint8(v___x_4244_);
    return v___x_4245_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(
    mut v___x_4246_: u8,
    mut v_x_4247_: u8,
) -> u8 {
    let mut v___y_4249_: u8 = 0;
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: u8 = 0;
    let mut v___y_4255_: u8 = 0;
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: u8 = 0;
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: u8 = 0;
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4260_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                v___x_4261_ = lean_uint8_dec_eq(v_x_4247_, v___x_4260_);
                if v___x_4261_ == 0 {
                    v___x_4262_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                    v___x_4263_ = lean_uint8_dec_eq(v_x_4247_, v___x_4262_);
                    if v___x_4263_ == 0 {
                        v___x_4264_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                        v___x_4265_ = lean_uint8_dec_le(v___x_4264_, v_x_4247_);
                        if v___x_4265_ == 0 {
                            v___y_4255_ = v___x_4265_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4266_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                            v___x_4267_ = lean_uint8_dec_le(v_x_4247_, v___x_4266_);
                            v___y_4255_ = v___x_4267_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_4246_;
                    }
                } else {
                    return v___x_4246_;
                }
            }
            1 => {
                if v___y_4249_ == 0 {
                    v___x_4250_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_4251_ = lean_uint8_dec_le(v___x_4250_, v_x_4247_);
                    if v___x_4251_ == 0 {
                        if v___x_4251_ == 0 {
                            return v___x_4251_;
                        } else {
                            return v___x_4246_;
                        }
                    } else {
                        v___x_4252_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0);
                        v___x_4253_ = lean_uint8_dec_le(v_x_4247_, v___x_4252_);
                        if v___x_4253_ == 0 {
                            return v___x_4253_;
                        } else {
                            return v___x_4246_;
                        }
                    }
                } else {
                    return v___x_4246_;
                }
            }
            2 => {
                if v___y_4255_ == 0 {
                    v___x_4256_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_4257_ = lean_uint8_dec_le(v___x_4256_, v_x_4247_);
                    if v___x_4257_ == 0 {
                        v___y_4249_ = v___x_4257_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4258_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1);
                        v___x_4259_ = lean_uint8_dec_le(v_x_4247_, v___x_4258_);
                        v___y_4249_ = v___x_4259_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4246_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(
    mut v___x_4268_: *mut crate::leanh::LeanObject,
    mut v_x_4269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493__boxed_4270_: u8 = 0;
    let mut v_x_boxed_4271_: u8 = 0;
    let mut v_res_4272_: u8 = 0;
    let mut v_r_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493__boxed_4270_ = (crate::leanh::lean_unbox(v___x_4268_) as u8);
    v_x_boxed_4271_ = (crate::leanh::lean_unbox(v_x_4269_) as u8);
    v_res_4272_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(
        v___x_1493__boxed_4270_,
        v_x_boxed_4271_,
    );
    v_r_4273_ = crate::leanh::lean_box((v_res_4272_) as usize);
    return v_r_4273_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1()
-> u8 {
    let mut v___x_4275_: u32 = 0;
    let mut v___x_4276_: u8 = 0;
    v___x_4275_ = 91;
    v___x_4276_ = lean_uint32_to_uint8(v___x_4275_);
    return v___x_4276_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1,
    );
    v___x_4279_ = lean_uint8_to_nat(v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3,
    );
    v___x_4281_ = l_Nat_reprFast(v___x_4280_);
    return v___x_4281_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4,
    );
    v___x_4283_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_4284_ = lean_string_append(v___x_4283_, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_4287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5,
    );
    v___x_4288_ = lean_string_append(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7,
    );
    v___x_4290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4290_, 0, v___x_4289_);
    return v___x_4290_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9()
-> u8 {
    let mut v___x_4291_: u32 = 0;
    let mut v___x_4292_: u8 = 0;
    v___x_4291_ = 93;
    v___x_4292_ = lean_uint32_to_uint8(v___x_4291_);
    return v___x_4292_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9,
    );
    v___x_4294_ = lean_uint8_to_nat(v___x_4293_);
    return v___x_4294_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10,
    );
    v___x_4296_ = l_Nat_reprFast(v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11,
    );
    v___x_4298_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_4299_ = lean_string_append(v___x_4298_, v___x_4297_);
    return v___x_4299_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4300_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_4301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12,
    );
    v___x_4302_ = lean_string_append(v___x_4301_, v___x_4300_);
    return v___x_4302_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once
        ),
        _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13,
    );
    v___x_4304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4304_, 0, v___x_4303_);
    return v___x_4304_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(
    mut v_a_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: u8 = 0;
    let mut v_got_4326_: u8 = 0;
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_fst_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___y_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: u8 = 0;
    let mut v_got_4362_: u8 = 0;
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4370_: u8 = 0;
    let mut v_lower_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_unused_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: u8 = 0;
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4402_: u8 = 0;
    let mut v_unused_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4404_: u8 = 0;
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_unused_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4319_ = crate::leanh::lean_ctor_get(v_a_4308_, 0);
                v_idx_4320_ = crate::leanh::lean_ctor_get(v_a_4308_, 1);
                v___x_4321_ = lean_byte_array_size(v_array_4319_);
                v___x_4322_ = lean_nat_dec_lt(v_idx_4320_, v___x_4321_);
                if v___x_4322_ == 0 {
                    v___x_4323_ = crate::leanh::lean_box(0);
                    v___x_4324_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4324_, 0, v_a_4308_);
                    crate::leanh::lean_ctor_set(v___x_4324_, 1, v___x_4323_);
                    return v___x_4324_;
                } else {
                    v___x_4325_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
                    v_got_4326_ = lean_byte_array_fget(v_array_4319_, v_idx_4320_);
                    v___x_4327_ = lean_uint8_dec_eq(v_got_4326_, v___x_4325_);
                    if v___x_4327_ == 0 {
                        v___x_4328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8);
                        v___x_4329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4329_, 0, v_a_4308_);
                        crate::leanh::lean_ctor_set(v___x_4329_, 1, v___x_4328_);
                        return v___x_4329_;
                    } else {
                        crate::leanh::lean_inc(v_idx_4320_);
                        crate::leanh::lean_inc_ref(v_array_4319_);
                        v_isSharedCheck_4406_ = (!crate::leanh::lean_is_exclusive(v_a_4308_)) as u8;
                        if v_isSharedCheck_4406_ == 0 {
                            v_unused_4407_ = crate::leanh::lean_ctor_get(v_a_4308_, 1);
                            crate::leanh::lean_dec(v_unused_4407_);
                            v_unused_4408_ = crate::leanh::lean_ctor_get(v_a_4308_, 0);
                            crate::leanh::lean_dec(v_unused_4408_);
                            v___x_4331_ = v_a_4308_;
                            v_isShared_4332_ = v_isSharedCheck_4406_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4308_);
                            v___x_4331_ = crate::leanh::lean_box(0);
                            v_isShared_4332_ = v_isSharedCheck_4406_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4312_ = lean_uv_pton_v6(v___y_4311_);
                if crate::leanh::lean_obj_tag(v___x_4312_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_4311_);
                    v_val_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    crate::leanh::lean_inc(v_val_4313_);
                    crate::leanh::lean_dec_ref_known(v___x_4312_, 1);
                    v___x_4314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4314_, 0, v___y_4310_);
                    crate::leanh::lean_ctor_set(v___x_4314_, 1, v_val_4313_);
                    return v___x_4314_;
                } else {
                    crate::leanh::lean_dec(v___x_4312_);
                    v___x_4315_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0;
                    v___x_4316_ = lean_string_append(v___x_4315_, v___y_4311_);
                    crate::leanh::lean_dec_ref(v___y_4311_);
                    v___x_4317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4316_);
                    v___x_4318_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___y_4310_);
                    crate::leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
                    return v___x_4318_;
                }
            }
            2 => {
                v___x_4333_ = crate::leanh::lean_box((v___x_4322_) as usize);
                v___f_4334_ = crate::leanh::lean_alloc_closure(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4334_, 0, v___x_4333_);
                v___x_4335_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4336_ = lean_nat_add(v_idx_4320_, v___x_4335_);
                crate::leanh::lean_dec(v_idx_4320_);
                crate::leanh::lean_inc(v___x_4336_);
                crate::leanh::lean_inc_ref(v_array_4319_);
                if v_isShared_4332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4331_, 1, v___x_4336_);
                    v___x_4338_ = v___x_4331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_array_4319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 1, v___x_4336_);
                    v___x_4338_ = v_reuseFailAlloc_4405_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4339_ = crate::leanh::lean_unsigned_to_nat(256);
                v___x_4340_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v___x_4338_);
                v___x_4341_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4334_, v___x_4339_, v___x_4340_, v___x_4338_);
                v_snd_4342_ = crate::leanh::lean_ctor_get(v___x_4341_, 1);
                v_fst_4343_ = crate::leanh::lean_ctor_get(v___x_4341_, 0);
                v_isSharedCheck_4404_ = (!crate::leanh::lean_is_exclusive(v___x_4341_)) as u8;
                if v_isSharedCheck_4404_ == 0 {
                    v___x_4345_ = v___x_4341_;
                    v_isShared_4346_ = v_isSharedCheck_4404_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4342_);
                    crate::leanh::lean_inc(v_fst_4343_);
                    crate::leanh::lean_dec(v___x_4341_);
                    v___x_4345_ = crate::leanh::lean_box(0);
                    v_isShared_4346_ = v_isSharedCheck_4404_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fst_4347_ = crate::leanh::lean_ctor_get(v_snd_4342_, 0);
                v_isSharedCheck_4402_ = (!crate::leanh::lean_is_exclusive(v_snd_4342_)) as u8;
                if v_isSharedCheck_4402_ == 0 {
                    v_unused_4403_ = crate::leanh::lean_ctor_get(v_snd_4342_, 1);
                    crate::leanh::lean_dec(v_unused_4403_);
                    v___x_4349_ = v_snd_4342_;
                    v_isShared_4350_ = v_isSharedCheck_4402_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4347_);
                    crate::leanh::lean_dec(v_snd_4342_);
                    v___x_4349_ = crate::leanh::lean_box(0);
                    v_isShared_4350_ = v_isSharedCheck_4402_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4386_ = lean_nat_dec_eq(v_fst_4343_, v___x_4340_);
                if v___x_4386_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4338_);
                    v___x_4387_ = lean_nat_add(v___x_4336_, v_fst_4343_);
                    crate::leanh::lean_dec(v_fst_4343_);
                    v___x_4397_ = lean_nat_dec_le(v___x_4336_, v___x_4340_);
                    if v___x_4397_ == 0 {
                        v___y_4389_ = v___x_4336_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4336_);
                        v___y_4389_ = v___x_4340_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4349_);
                    crate::leanh::lean_dec(v_fst_4347_);
                    crate::leanh::lean_dec(v_fst_4343_);
                    crate::leanh::lean_dec(v___x_4336_);
                    crate::leanh::lean_dec_ref(v_array_4319_);
                    v___x_4398_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16;
                    if v_isShared_4346_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4345_, 1);
                        crate::leanh::lean_ctor_set(v___x_4345_, 1, v___x_4398_);
                        crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4338_);
                        v___x_4400_ = v___x_4345_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4401_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4338_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4401_, 1, v___x_4398_);
                        v___x_4400_ = v_reuseFailAlloc_4401_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v_array_4353_ = crate::leanh::lean_ctor_get(v_fst_4347_, 0);
                v_idx_4354_ = crate::leanh::lean_ctor_get(v_fst_4347_, 1);
                v___x_4355_ = lean_byte_array_size(v_array_4353_);
                v___x_4356_ = lean_nat_dec_lt(v_idx_4354_, v___x_4355_);
                if v___x_4356_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4352_);
                    crate::leanh::lean_dec_ref(v_array_4319_);
                    v___x_4357_ = crate::leanh::lean_box(0);
                    if v_isShared_4350_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4349_, 1);
                        crate::leanh::lean_ctor_set(v___x_4349_, 1, v___x_4357_);
                        v___x_4359_ = v___x_4349_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4360_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_fst_4347_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___x_4357_);
                        v___x_4359_ = v_reuseFailAlloc_4360_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_4361_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
                    v_got_4362_ = lean_byte_array_fget(v_array_4353_, v_idx_4354_);
                    v___x_4363_ = lean_uint8_dec_eq(v_got_4362_, v___x_4361_);
                    if v___x_4363_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_4352_);
                        crate::leanh::lean_dec_ref(v_array_4319_);
                        v___x_4364_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14);
                        if v_isShared_4350_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4349_, 1);
                            crate::leanh::lean_ctor_set(v___x_4349_, 1, v___x_4364_);
                            v___x_4366_ = v___x_4349_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4367_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_fst_4347_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 1, v___x_4364_);
                            v___x_4366_ = v_reuseFailAlloc_4367_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_idx_4354_);
                        crate::leanh::lean_inc_ref(v_array_4353_);
                        crate::leanh::lean_del_object(v___x_4349_);
                        v_isSharedCheck_4383_ =
                            (!crate::leanh::lean_is_exclusive(v_fst_4347_)) as u8;
                        if v_isSharedCheck_4383_ == 0 {
                            v_unused_4384_ = crate::leanh::lean_ctor_get(v_fst_4347_, 1);
                            crate::leanh::lean_dec(v_unused_4384_);
                            v_unused_4385_ = crate::leanh::lean_ctor_get(v_fst_4347_, 0);
                            crate::leanh::lean_dec(v_unused_4385_);
                            v___x_4369_ = v_fst_4347_;
                            v_isShared_4370_ = v_isSharedCheck_4383_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_4347_);
                            v___x_4369_ = crate::leanh::lean_box(0);
                            v_isShared_4370_ = v_isSharedCheck_4383_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_4359_;
            }
            8 => {
                return v___x_4366_;
            }
            9 => {
                v_lower_4371_ = crate::leanh::lean_ctor_get(v___y_4352_, 0);
                crate::leanh::lean_inc(v_lower_4371_);
                v_upper_4372_ = crate::leanh::lean_ctor_get(v___y_4352_, 1);
                crate::leanh::lean_inc(v_upper_4372_);
                crate::leanh::lean_dec_ref(v___y_4352_);
                v___x_4373_ = l_ByteArray_toByteSlice(v_array_4319_, v_lower_4371_, v_upper_4372_);
                v___x_4374_ = lean_nat_add(v_idx_4354_, v___x_4335_);
                crate::leanh::lean_dec(v_idx_4354_);
                if v_isShared_4370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4369_, 1, v___x_4374_);
                    v___x_4376_ = v___x_4369_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_array_4353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___x_4374_);
                    v___x_4376_ = v_reuseFailAlloc_4382_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4377_ = l_ByteSlice_toByteArray(v___x_4373_);
                v___x_4378_ = lean_string_validate_utf8(v___x_4377_);
                if v___x_4378_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4377_);
                    v___x_4379_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
                    v___x_4380_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_4379_);
                    v___y_4310_ = v___x_4376_;
                    v___y_4311_ = v___x_4380_;
                    state = 1;
                    continue;
                } else {
                    v___x_4381_ = lean_string_from_utf8_unchecked(v___x_4377_);
                    v___y_4310_ = v___x_4376_;
                    v___y_4311_ = v___x_4381_;
                    state = 1;
                    continue;
                }
            }
            11 => {
                v___x_4390_ = lean_nat_dec_le(v___x_4387_, v___x_4321_);
                if v___x_4390_ == 0 {
                    crate::leanh::lean_dec(v___x_4387_);
                    if v_isShared_4346_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4345_, 1, v___x_4321_);
                        crate::leanh::lean_ctor_set(v___x_4345_, 0, v___y_4389_);
                        v___x_4392_ = v___x_4345_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___y_4389_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 1, v___x_4321_);
                        v___x_4392_ = v_reuseFailAlloc_4393_;
                        state = 12;
                        continue;
                    }
                } else {
                    if v_isShared_4346_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4345_, 1, v___x_4387_);
                        crate::leanh::lean_ctor_set(v___x_4345_, 0, v___y_4389_);
                        v___x_4395_ = v___x_4345_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___y_4389_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 1, v___x_4387_);
                        v___x_4395_ = v_reuseFailAlloc_4396_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v___y_4352_ = v___x_4392_;
                state = 6;
                continue;
            }
            13 => {
                v___y_4352_ = v___x_4395_;
                state = 6;
                continue;
            }
            14 => {
                return v___x_4400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(
    mut v_x_4409_: u8,
) -> u8 {
    let mut v___x_4410_: u8 = 0;
    let mut v___x_4411_: u8 = 0;
    v___x_4410_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
    v___x_4411_ = lean_uint8_dec_eq(v_x_4409_, v___x_4410_);
    if v___x_4411_ == 0 {
        let mut v___x_4412_: u8 = 0;
        let mut v___x_4413_: u8 = 0;
        v___x_4412_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
        v___x_4413_ = lean_uint8_dec_le(v___x_4412_, v_x_4409_);
        if v___x_4413_ == 0 {
            return v___x_4413_;
        } else {
            let mut v___x_4414_: u8 = 0;
            let mut v___x_4415_: u8 = 0;
            v___x_4414_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
            v___x_4415_ = lean_uint8_dec_le(v_x_4409_, v___x_4414_);
            return v___x_4415_;
        }
    } else {
        return v___x_4411_;
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(
    mut v_x_4416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4417_: u8 = 0;
    let mut v_res_4418_: u8 = 0;
    let mut v_r_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4417_ = (crate::leanh::lean_unbox(v_x_4416_) as u8);
    v_res_4418_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(
        v_x_boxed_4417_,
    );
    v_r_4419_ = crate::leanh::lean_box((v_res_4418_) as usize);
    return v_r_4419_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(
    mut v_a_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v_fst_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___y_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: u8 = 0;
    let mut v_array_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v_unused_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4423_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0;
                v___x_4424_ = crate::leanh::lean_unsigned_to_nat(256);
                v___x_4425_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_4422_);
                v___x_4426_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4423_, v___x_4424_, v___x_4425_, v_a_4422_);
                v_snd_4427_ = crate::leanh::lean_ctor_get(v___x_4426_, 1);
                v_fst_4428_ = crate::leanh::lean_ctor_get(v___x_4426_, 0);
                v_isSharedCheck_4473_ = (!crate::leanh::lean_is_exclusive(v___x_4426_)) as u8;
                if v_isSharedCheck_4473_ == 0 {
                    v___x_4430_ = v___x_4426_;
                    v_isShared_4431_ = v_isSharedCheck_4473_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4427_);
                    crate::leanh::lean_inc(v_fst_4428_);
                    crate::leanh::lean_dec(v___x_4426_);
                    v___x_4430_ = crate::leanh::lean_box(0);
                    v_isShared_4431_ = v_isSharedCheck_4473_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4432_ = crate::leanh::lean_ctor_get(v_snd_4427_, 0);
                v_isSharedCheck_4471_ = (!crate::leanh::lean_is_exclusive(v_snd_4427_)) as u8;
                if v_isSharedCheck_4471_ == 0 {
                    v_unused_4472_ = crate::leanh::lean_ctor_get(v_snd_4427_, 1);
                    crate::leanh::lean_dec(v_unused_4472_);
                    v___x_4434_ = v_snd_4427_;
                    v_isShared_4435_ = v_isSharedCheck_4471_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4432_);
                    crate::leanh::lean_dec(v_snd_4427_);
                    v___x_4434_ = crate::leanh::lean_box(0);
                    v_isShared_4435_ = v_isSharedCheck_4471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4449_ = lean_nat_dec_eq(v_fst_4428_, v___x_4425_);
                if v___x_4449_ == 0 {
                    crate::leanh::lean_del_object(v___x_4430_);
                    v_array_4450_ = crate::leanh::lean_ctor_get(v_a_4422_, 0);
                    crate::leanh::lean_inc_ref(v_array_4450_);
                    v_idx_4451_ = crate::leanh::lean_ctor_get(v_a_4422_, 1);
                    crate::leanh::lean_inc(v_idx_4451_);
                    crate::leanh::lean_dec_ref(v_a_4422_);
                    v___x_4461_ = lean_nat_add(v_idx_4451_, v_fst_4428_);
                    crate::leanh::lean_dec(v_fst_4428_);
                    v___x_4462_ = lean_byte_array_size(v_array_4450_);
                    v___x_4466_ = lean_nat_dec_le(v_idx_4451_, v___x_4425_);
                    if v___x_4466_ == 0 {
                        v___y_4464_ = v_idx_4451_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_idx_4451_);
                        v___y_4464_ = v___x_4425_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4434_);
                    crate::leanh::lean_dec(v_fst_4432_);
                    crate::leanh::lean_dec(v_fst_4428_);
                    v___x_4467_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16;
                    if v_isShared_4431_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4430_, 1);
                        crate::leanh::lean_ctor_set(v___x_4430_, 1, v___x_4467_);
                        crate::leanh::lean_ctor_set(v___x_4430_, 0, v_a_4422_);
                        v___x_4469_ = v___x_4430_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4422_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4467_);
                        v___x_4469_ = v_reuseFailAlloc_4470_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4438_ = lean_uv_pton_v4(v___y_4437_);
                if crate::leanh::lean_obj_tag(v___x_4438_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_4437_);
                    v_val_4439_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                    crate::leanh::lean_inc(v_val_4439_);
                    crate::leanh::lean_dec_ref_known(v___x_4438_, 1);
                    if v_isShared_4435_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4434_, 1, v_val_4439_);
                        v___x_4441_ = v___x_4434_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4442_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_fst_4432_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_val_4439_);
                        v___x_4441_ = v_reuseFailAlloc_4442_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4438_);
                    v___x_4443_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1;
                    v___x_4444_ = lean_string_append(v___x_4443_, v___y_4437_);
                    crate::leanh::lean_dec_ref(v___y_4437_);
                    v___x_4445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4445_, 0, v___x_4444_);
                    if v_isShared_4435_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4434_, 1);
                        crate::leanh::lean_ctor_set(v___x_4434_, 1, v___x_4445_);
                        v___x_4447_ = v___x_4434_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_fst_4432_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4445_);
                        v___x_4447_ = v_reuseFailAlloc_4448_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4441_;
            }
            5 => {
                return v___x_4447_;
            }
            6 => {
                v___x_4455_ = l_ByteArray_toByteSlice(v_array_4450_, v_lower_4453_, v_upper_4454_);
                v___x_4456_ = l_ByteSlice_toByteArray(v___x_4455_);
                v___x_4457_ = lean_string_validate_utf8(v___x_4456_);
                if v___x_4457_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4456_);
                    v___x_4458_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
                    v___x_4459_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_4458_);
                    v___y_4437_ = v___x_4459_;
                    state = 3;
                    continue;
                } else {
                    v___x_4460_ = lean_string_from_utf8_unchecked(v___x_4456_);
                    v___y_4437_ = v___x_4460_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_4465_ = lean_nat_dec_le(v___x_4461_, v___x_4462_);
                if v___x_4465_ == 0 {
                    crate::leanh::lean_dec(v___x_4461_);
                    v_lower_4453_ = v___y_4464_;
                    v_upper_4454_ = v___x_4462_;
                    state = 6;
                    continue;
                } else {
                    v_lower_4453_ = v___y_4464_;
                    v_upper_4454_ = v___x_4461_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(
    mut v_s_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0;
    return v___x_4477_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(
    mut v_s_4478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4479_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_4478_);
    crate::leanh::lean_dec_ref(v_s_4478_);
    return v_res_4479_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(
    mut v_x_4480_: u8,
) -> u8 {
    let mut v___y_4482_: u8 = 0;
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: u8 = 0;
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: u8 = 0;
    let mut v___y_4488_: u8 = 0;
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: u8 = 0;
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: u8 = 0;
    let mut v___y_4494_: u8 = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: u8 = 0;
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4499_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_4500_ = lean_uint8_dec_le(v___x_4499_, v_x_4480_);
                if v___x_4500_ == 0 {
                    v___y_4494_ = v___x_4500_;
                    state = 3;
                    continue;
                } else {
                    v___x_4501_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_4502_ = lean_uint8_dec_le(v_x_4480_, v___x_4501_);
                    v___y_4494_ = v___x_4502_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_4482_ == 0 {
                    v___x_4483_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_4484_ = lean_uint8_dec_eq(v_x_4480_, v___x_4483_);
                    if v___x_4484_ == 0 {
                        v___x_4485_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_4486_ = lean_uint8_dec_eq(v_x_4480_, v___x_4485_);
                        if v___x_4486_ == 0 {
                            return v___y_4482_;
                        } else {
                            return v___x_4486_;
                        }
                    } else {
                        return v___x_4484_;
                    }
                } else {
                    return v___y_4482_;
                }
            }
            2 => {
                if v___y_4488_ == 0 {
                    v___x_4489_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_4490_ = lean_uint8_dec_le(v___x_4489_, v_x_4480_);
                    if v___x_4490_ == 0 {
                        v___y_4482_ = v___x_4490_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4491_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_4492_ = lean_uint8_dec_le(v_x_4480_, v___x_4491_);
                        v___y_4482_ = v___x_4492_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_4488_;
                }
            }
            3 => {
                if v___y_4494_ == 0 {
                    v___x_4495_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_4496_ = lean_uint8_dec_le(v___x_4495_, v_x_4480_);
                    if v___x_4496_ == 0 {
                        v___y_4488_ = v___x_4496_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4497_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_4498_ = lean_uint8_dec_le(v_x_4480_, v___x_4497_);
                        v___y_4488_ = v___x_4498_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_4494_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(
    mut v_x_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4504_: u8 = 0;
    let mut v_res_4505_: u8 = 0;
    let mut v_r_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4504_ = (crate::leanh::lean_unbox(v_x_4503_) as u8);
    v_res_4505_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(
        v_x_boxed_4504_,
    );
    v_r_4506_ = crate::leanh::lean_box((v_res_4505_) as usize);
    return v_r_4506_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(
    mut v___x_4507_: *mut crate::leanh::LeanObject,
    mut v___x_4508_: *mut crate::leanh::LeanObject,
    mut v___x_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_b_4511_: u8,
) -> u8 {
    let mut v_currPos_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v_startInclusive_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v_it_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4529_: u32 = 0;
    let mut v___x_4530_: u32 = 0;
    let mut v___x_4531_: u8 = 0;
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4510_) == 0 {
                    v_currPos_4512_ = crate::leanh::lean_ctor_get(v_a_4510_, 0);
                    v_searcher_4513_ = crate::leanh::lean_ctor_get(v_a_4510_, 1);
                    v_isSharedCheck_4547_ = (!crate::leanh::lean_is_exclusive(v_a_4510_)) as u8;
                    if v_isSharedCheck_4547_ == 0 {
                        v___x_4515_ = v_a_4510_;
                        v_isShared_4516_ = v_isSharedCheck_4547_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_4513_);
                        crate::leanh::lean_inc(v_currPos_4512_);
                        crate::leanh::lean_dec(v_a_4510_);
                        v___x_4515_ = crate::leanh::lean_box(0);
                        v_isShared_4516_ = v_isSharedCheck_4547_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4509_);
                    return v_b_4511_;
                }
            }
            1 => {
                v_startInclusive_4517_ = crate::leanh::lean_ctor_get(v___x_4508_, 1);
                v_endExclusive_4518_ = crate::leanh::lean_ctor_get(v___x_4508_, 2);
                v___x_4519_ = 1;
                v___x_4527_ = lean_nat_sub(v_endExclusive_4518_, v_startInclusive_4517_);
                v___x_4528_ = lean_nat_dec_eq(v_searcher_4513_, v___x_4527_);
                crate::leanh::lean_dec(v___x_4527_);
                if v___x_4528_ == 0 {
                    v___x_4529_ = 46;
                    v___x_4530_ = lean_string_utf8_get_fast(v___x_4507_, v_searcher_4513_);
                    v___x_4531_ = lean_uint32_dec_eq(v___x_4530_, v___x_4529_);
                    if v___x_4531_ == 0 {
                        v___x_4532_ = lean_string_utf8_next_fast(v___x_4507_, v_searcher_4513_);
                        crate::leanh::lean_dec(v_searcher_4513_);
                        if v_isShared_4516_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4515_, 1, v___x_4532_);
                            v___x_4534_ = v___x_4515_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4536_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_currPos_4512_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 1, v___x_4532_);
                            v___x_4534_ = v_reuseFailAlloc_4536_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4537_ = lean_string_utf8_next_fast(v___x_4507_, v_searcher_4513_);
                        v___x_4538_ = lean_nat_sub(v___x_4537_, v_searcher_4513_);
                        v___x_4539_ = lean_nat_add(v_searcher_4513_, v___x_4538_);
                        crate::leanh::lean_dec(v___x_4538_);
                        v_slice_4540_ = l_String_Slice_subslice_x21(
                            v___x_4508_,
                            v_currPos_4512_,
                            v_searcher_4513_,
                        );
                        crate::leanh::lean_inc(v___x_4539_);
                        if v_isShared_4516_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4515_, 1, v___x_4539_);
                            crate::leanh::lean_ctor_set(v___x_4515_, 0, v___x_4539_);
                            v_nextIt_4542_ = v___x_4515_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4545_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4539_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 1, v___x_4539_);
                            v_nextIt_4542_ = v_reuseFailAlloc_4545_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4515_);
                    crate::leanh::lean_dec(v_searcher_4513_);
                    v___x_4546_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_4509_);
                    v_it_4521_ = v___x_4546_;
                    v_startInclusive_4522_ = v_currPos_4512_;
                    v_endExclusive_4523_ = v___x_4509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4524_ = lean_string_utf8_extract(
                    v___x_4507_,
                    v_startInclusive_4522_,
                    v_endExclusive_4523_,
                );
                crate::leanh::lean_dec(v_endExclusive_4523_);
                crate::leanh::lean_dec(v_startInclusive_4522_);
                v___x_4525_ = l_Std_Http_URI_isValidDomainLabel(v___x_4524_);
                if v___x_4525_ == 0 {
                    crate::leanh::lean_dec(v_it_4521_);
                    crate::leanh::lean_dec(v___x_4509_);
                    return v___x_4525_;
                } else {
                    v_a_4510_ = v_it_4521_;
                    v_b_4511_ = v___x_4519_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v_a_4510_ = v___x_4534_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_4543_ = crate::leanh::lean_ctor_get(v_slice_4540_, 0);
                crate::leanh::lean_inc(v_startInclusive_4543_);
                v_endExclusive_4544_ = crate::leanh::lean_ctor_get(v_slice_4540_, 1);
                crate::leanh::lean_inc(v_endExclusive_4544_);
                crate::leanh::lean_dec_ref(v_slice_4540_);
                v_it_4521_ = v_nextIt_4542_;
                v_startInclusive_4522_ = v_startInclusive_4543_;
                v_endExclusive_4523_ = v_endExclusive_4544_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(
    mut v___x_4548_: *mut crate::leanh::LeanObject,
    mut v___x_4549_: *mut crate::leanh::LeanObject,
    mut v___x_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_b_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4553_: u8 = 0;
    let mut v_res_4554_: u8 = 0;
    let mut v_r_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4553_ = (crate::leanh::lean_unbox(v_b_4552_) as u8);
    v_res_4554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_4548_, v___x_4549_, v___x_4550_, v_a_4551_, v_b_boxed_4553_);
    crate::leanh::lean_dec_ref(v___x_4549_);
    crate::leanh::lean_dec_ref(v___x_4548_);
    v_r_4555_ = crate::leanh::lean_box((v_res_4554_) as usize);
    return v_r_4555_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(
    mut v___x_4556_: *mut crate::leanh::LeanObject,
    mut v___x_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_b_4559_: u8,
) -> u8 {
    let mut v_currPos_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v_startInclusive_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: u32 = 0;
    let mut v___x_4571_: u32 = 0;
    let mut v___x_4572_: u8 = 0;
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4558_) == 0 {
                    v_currPos_4560_ = crate::leanh::lean_ctor_get(v_a_4558_, 0);
                    v_searcher_4561_ = crate::leanh::lean_ctor_get(v_a_4558_, 1);
                    v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v_a_4558_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4563_ = v_a_4558_;
                        v_isShared_4564_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_4561_);
                        crate::leanh::lean_inc(v_currPos_4560_);
                        crate::leanh::lean_dec(v_a_4558_);
                        v___x_4563_ = crate::leanh::lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4559_;
                }
            }
            1 => {
                v_startInclusive_4565_ = crate::leanh::lean_ctor_get(v___x_4557_, 1);
                v_endExclusive_4566_ = crate::leanh::lean_ctor_get(v___x_4557_, 2);
                v___x_4567_ = 0;
                v___x_4568_ = lean_nat_sub(v_endExclusive_4566_, v_startInclusive_4565_);
                v___x_4569_ = lean_nat_dec_eq(v_searcher_4561_, v___x_4568_);
                crate::leanh::lean_dec(v___x_4568_);
                if v___x_4569_ == 0 {
                    v___x_4570_ = 46;
                    v___x_4571_ = lean_string_utf8_get_fast(v___x_4556_, v_searcher_4561_);
                    v___x_4572_ = lean_uint32_dec_eq(v___x_4571_, v___x_4570_);
                    if v___x_4572_ == 0 {
                        v___x_4573_ = lean_string_utf8_next_fast(v___x_4556_, v_searcher_4561_);
                        crate::leanh::lean_dec(v_searcher_4561_);
                        if v_isShared_4564_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4563_, 1, v___x_4573_);
                            v___x_4575_ = v___x_4563_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4577_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_currPos_4560_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4573_);
                            v___x_4575_ = v_reuseFailAlloc_4577_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4563_);
                        crate::leanh::lean_dec(v_searcher_4561_);
                        crate::leanh::lean_dec(v_currPos_4560_);
                        return v___x_4567_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4563_);
                    crate::leanh::lean_dec(v_searcher_4561_);
                    crate::leanh::lean_dec(v_currPos_4560_);
                    return v___x_4567_;
                }
            }
            2 => {
                v_a_4558_ = v___x_4575_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(
    mut v___x_4579_: *mut crate::leanh::LeanObject,
    mut v___x_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
    mut v_b_4582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4583_: u8 = 0;
    let mut v_res_4584_: u8 = 0;
    let mut v_r_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4583_ = (crate::leanh::lean_unbox(v_b_4582_) as u8);
    v_res_4584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_4579_, v___x_4580_, v_a_4581_, v_b_boxed_4583_);
    crate::leanh::lean_dec_ref(v___x_4580_);
    crate::leanh::lean_dec_ref(v___x_4579_);
    v_r_4585_ = crate::leanh::lean_box((v_res_4584_) as usize);
    return v_r_4585_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(
    mut v_config_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4608_: u8 = 0;
    let mut v___y_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4612_: u8 = 0;
    let mut v___y_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4614_: u8 = 0;
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: u8 = 0;
    let mut v___y_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: u8 = 0;
    let mut v___y_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___y_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4646_: u8 = 0;
    let mut v___y_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: u8 = 0;
    let mut v_array_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHostLength_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4664_: u8 = 0;
    let mut v_array_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4683_: u8 = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4688_: u8 = 0;
    let mut v_err_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v_idx_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: u8 = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_unused_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4706_: u8 = 0;
    let mut v_pos_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v___x_4712_: u8 = 0;
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: u8 = 0;
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: u8 = 0;
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: u8 = 0;
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4734_: u8 = 0;
    let mut v_pos_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4739_: u8 = 0;
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4650_ = crate::leanh::lean_ctor_get(v_a_4592_, 0);
                v_idx_4651_ = crate::leanh::lean_ctor_get(v_a_4592_, 1);
                v___f_4652_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3;
                v___x_4717_ = lean_byte_array_size(v_array_4650_);
                v___x_4718_ = lean_nat_dec_lt(v_idx_4651_, v___x_4717_);
                if v___x_4718_ == 0 {
                    crate::leanh::lean_inc(v_idx_4651_);
                    crate::leanh::lean_inc_ref(v_array_4650_);
                    v___x_4719_ = crate::leanh::lean_box(0);
                    v_pos_4708_ = v_a_4592_;
                    v_res_4709_ = v___x_4719_;
                    state = 16;
                    continue;
                } else {
                    v___x_4720_ = lean_byte_array_fget(v_array_4650_, v_idx_4651_);
                    v___x_4721_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
                    v___x_4722_ = lean_uint8_dec_eq(v___x_4720_, v___x_4721_);
                    if v___x_4722_ == 0 {
                        crate::leanh::lean_inc(v_idx_4651_);
                        crate::leanh::lean_inc_ref(v_array_4650_);
                        v___x_4723_ = crate::leanh::lean_box(0);
                        v_pos_4708_ = v_a_4592_;
                        v_res_4709_ = v___x_4723_;
                        state = 16;
                        continue;
                    } else {
                        v___x_4724_ =
                            l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(
                                v_a_4592_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4724_) == 0 {
                            v_pos_4725_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
                            v_res_4726_ = crate::leanh::lean_ctor_get(v___x_4724_, 1);
                            v_isSharedCheck_4734_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4734_ == 0 {
                                v___x_4728_ = v___x_4724_;
                                v_isShared_4729_ = v_isSharedCheck_4734_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_res_4726_);
                                crate::leanh::lean_inc(v_pos_4725_);
                                crate::leanh::lean_dec(v___x_4724_);
                                v___x_4728_ = crate::leanh::lean_box(0);
                                v_isShared_4729_ = v_isSharedCheck_4734_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v_pos_4735_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
                            v_err_4736_ = crate::leanh::lean_ctor_get(v___x_4724_, 1);
                            v_isSharedCheck_4743_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4743_ == 0 {
                                v___x_4738_ = v___x_4724_;
                                v_isShared_4739_ = v_isSharedCheck_4743_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_4736_);
                                crate::leanh::lean_inc(v_pos_4735_);
                                crate::leanh::lean_dec(v___x_4724_);
                                v___x_4738_ = crate::leanh::lean_box(0);
                                v_isShared_4739_ = v_isSharedCheck_4743_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4596_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0;
                v___x_4597_ = lean_string_append(v___x_4596_, v___y_4594_);
                crate::leanh::lean_dec_ref(v___y_4594_);
                v___x_4598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4598_, 0, v___x_4597_);
                v___x_4599_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4599_, 0, v___y_4595_);
                crate::leanh::lean_ctor_set(v___x_4599_, 1, v___x_4598_);
                return v___x_4599_;
            }
            2 => {
                if v___y_4604_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4601_);
                    v___y_4594_ = v___y_4602_;
                    v___y_4595_ = v___y_4603_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4602_);
                    v___x_4605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4605_, 0, v___y_4601_);
                    v___x_4606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4606_, 0, v___y_4603_);
                    crate::leanh::lean_ctor_set(v___x_4606_, 1, v___x_4605_);
                    return v___x_4606_;
                }
            }
            3 => {
                if v___y_4614_ == 0 {
                    crate::leanh::lean_dec(v___y_4610_);
                    crate::leanh::lean_dec_ref(v___y_4609_);
                    v___y_4594_ = v___y_4611_;
                    v___y_4595_ = v___y_4613_;
                    state = 1;
                    continue;
                } else {
                    v___x_4615_ = lean_string_utf8_byte_size(v___y_4609_);
                    crate::leanh::lean_inc(v___y_4610_);
                    crate::leanh::lean_inc_ref(v___y_4609_);
                    v___x_4616_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4616_, 0, v___y_4609_);
                    crate::leanh::lean_ctor_set(v___x_4616_, 1, v___y_4610_);
                    crate::leanh::lean_ctor_set(v___x_4616_, 2, v___x_4615_);
                    v___x_4617_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_4616_);
                    v___x_4618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___y_4609_, v___x_4616_, v___x_4615_, v___x_4617_, v___y_4614_);
                    crate::leanh::lean_dec_ref_known(v___x_4616_, 3);
                    if v___x_4618_ == 0 {
                        crate::leanh::lean_dec(v___y_4610_);
                        crate::leanh::lean_dec_ref(v___y_4609_);
                        v___y_4594_ = v___y_4611_;
                        v___y_4595_ = v___y_4613_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4619_ = lean_string_length(v___y_4609_);
                        v___x_4620_ = crate::leanh::lean_unsigned_to_nat(255);
                        v___x_4621_ = lean_nat_dec_le(v___x_4619_, v___x_4620_);
                        if v___x_4621_ == 0 {
                            crate::leanh::lean_dec(v___y_4610_);
                            crate::leanh::lean_dec_ref(v___y_4609_);
                            v___y_4594_ = v___y_4611_;
                            v___y_4595_ = v___y_4613_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4622_ = lean_nat_dec_eq(v___x_4615_, v___y_4610_);
                            crate::leanh::lean_dec(v___y_4610_);
                            if v___x_4622_ == 0 {
                                v___y_4601_ = v___y_4609_;
                                v___y_4602_ = v___y_4611_;
                                v___y_4603_ = v___y_4613_;
                                v___y_4604_ = v___y_4608_;
                                state = 2;
                                continue;
                            } else {
                                v___y_4601_ = v___y_4609_;
                                v___y_4602_ = v___y_4611_;
                                v___y_4603_ = v___y_4613_;
                                v___y_4604_ = v___y_4612_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_4630_ = l_ByteArray_toByteSlice(v___y_4625_, v_lower_4628_, v_upper_4629_);
                v___x_4631_ = l_ByteSlice_toByteArray(v___x_4630_);
                v___x_4632_ = lean_string_validate_utf8(v___x_4631_);
                if v___x_4632_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4631_);
                    crate::leanh::lean_dec(v___y_4624_);
                    v___x_4633_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2;
                    v___x_4634_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4634_, 0, v___y_4627_);
                    crate::leanh::lean_ctor_set(v___x_4634_, 1, v___x_4633_);
                    return v___x_4634_;
                } else {
                    v___x_4635_ = lean_string_from_utf8_unchecked(v___x_4631_);
                    crate::leanh::lean_inc_n(v___y_4624_, 2);
                    crate::leanh::lean_inc_ref(v___x_4635_);
                    v___x_4636_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_4635_, v___y_4624_);
                    v___x_4637_ = lean_string_utf8_byte_size(v___x_4636_);
                    crate::leanh::lean_inc_ref(v___x_4636_);
                    v___x_4638_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4638_, 0, v___x_4636_);
                    crate::leanh::lean_ctor_set(v___x_4638_, 1, v___y_4624_);
                    crate::leanh::lean_ctor_set(v___x_4638_, 2, v___x_4637_);
                    v___x_4639_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_4638_);
                    v___x_4640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_4636_, v___x_4638_, v___x_4639_, v___x_4632_);
                    crate::leanh::lean_dec_ref_known(v___x_4638_, 3);
                    if v___x_4640_ == 0 {
                        v___y_4608_ = v___x_4632_;
                        v___y_4609_ = v___x_4636_;
                        v___y_4610_ = v___y_4624_;
                        v___y_4611_ = v___x_4635_;
                        v___y_4612_ = v___y_4626_;
                        v___y_4613_ = v___y_4627_;
                        v___y_4614_ = v___x_4632_;
                        state = 3;
                        continue;
                    } else {
                        v___y_4608_ = v___x_4632_;
                        v___y_4609_ = v___x_4636_;
                        v___y_4610_ = v___y_4624_;
                        v___y_4611_ = v___x_4635_;
                        v___y_4612_ = v___y_4626_;
                        v___y_4613_ = v___y_4627_;
                        v___y_4614_ = v___y_4626_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4649_ = lean_nat_dec_le(v___y_4643_, v___y_4642_);
                if v___x_4649_ == 0 {
                    crate::leanh::lean_dec(v___y_4643_);
                    v___y_4624_ = v___y_4645_;
                    v___y_4625_ = v___y_4644_;
                    v___y_4626_ = v___y_4646_;
                    v___y_4627_ = v___y_4647_;
                    v_lower_4628_ = v___y_4648_;
                    v_upper_4629_ = v___y_4642_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_4642_);
                    v___y_4624_ = v___y_4645_;
                    v___y_4625_ = v___y_4644_;
                    v___y_4626_ = v___y_4646_;
                    v___y_4627_ = v___y_4647_;
                    v_lower_4628_ = v___y_4648_;
                    v_upper_4629_ = v___y_4643_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_maxHostLength_4655_ = crate::leanh::lean_ctor_get(v_config_4591_, 1);
                v___x_4656_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v___y_4654_);
                v___x_4657_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4652_, v_maxHostLength_4655_, v___x_4656_, v___y_4654_);
                v_snd_4658_ = crate::leanh::lean_ctor_get(v___x_4657_, 1);
                crate::leanh::lean_inc(v_snd_4658_);
                v_fst_4659_ = crate::leanh::lean_ctor_get(v___x_4657_, 0);
                crate::leanh::lean_inc(v_fst_4659_);
                crate::leanh::lean_dec_ref(v___x_4657_);
                v_fst_4660_ = crate::leanh::lean_ctor_get(v_snd_4658_, 0);
                v_isSharedCheck_4674_ = (!crate::leanh::lean_is_exclusive(v_snd_4658_)) as u8;
                if v_isSharedCheck_4674_ == 0 {
                    v_unused_4675_ = crate::leanh::lean_ctor_get(v_snd_4658_, 1);
                    crate::leanh::lean_dec(v_unused_4675_);
                    v___x_4662_ = v_snd_4658_;
                    v_isShared_4663_ = v_isSharedCheck_4674_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4660_);
                    crate::leanh::lean_dec(v_snd_4658_);
                    v___x_4662_ = crate::leanh::lean_box(0);
                    v_isShared_4663_ = v_isSharedCheck_4674_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4664_ = lean_nat_dec_eq(v_fst_4659_, v___x_4656_);
                if v___x_4664_ == 0 {
                    crate::leanh::lean_del_object(v___x_4662_);
                    v_array_4665_ = crate::leanh::lean_ctor_get(v___y_4654_, 0);
                    crate::leanh::lean_inc_ref(v_array_4665_);
                    v_idx_4666_ = crate::leanh::lean_ctor_get(v___y_4654_, 1);
                    crate::leanh::lean_inc(v_idx_4666_);
                    crate::leanh::lean_dec_ref(v___y_4654_);
                    v___x_4667_ = lean_nat_add(v_idx_4666_, v_fst_4659_);
                    crate::leanh::lean_dec(v_fst_4659_);
                    v___x_4668_ = lean_byte_array_size(v_array_4665_);
                    v___x_4669_ = lean_nat_dec_le(v_idx_4666_, v___x_4656_);
                    if v___x_4669_ == 0 {
                        v___y_4642_ = v___x_4668_;
                        v___y_4643_ = v___x_4667_;
                        v___y_4644_ = v_array_4665_;
                        v___y_4645_ = v___x_4656_;
                        v___y_4646_ = v___x_4664_;
                        v___y_4647_ = v_fst_4660_;
                        v___y_4648_ = v_idx_4666_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_idx_4666_);
                        v___y_4642_ = v___x_4668_;
                        v___y_4643_ = v___x_4667_;
                        v___y_4644_ = v_array_4665_;
                        v___y_4645_ = v___x_4656_;
                        v___y_4646_ = v___x_4664_;
                        v___y_4647_ = v_fst_4660_;
                        v___y_4648_ = v___x_4656_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4660_);
                    crate::leanh::lean_dec(v_fst_4659_);
                    v___x_4670_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16;
                    if v_isShared_4663_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4662_, 1);
                        crate::leanh::lean_ctor_set(v___x_4662_, 1, v___x_4670_);
                        crate::leanh::lean_ctor_set(v___x_4662_, 0, v___y_4654_);
                        v___x_4672_ = v___x_4662_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4673_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___y_4654_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 1, v___x_4670_);
                        v___x_4672_ = v_reuseFailAlloc_4673_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_4672_;
            }
            9 => {
                crate::leanh::lean_inc_ref(v_pos_4677_);
                v___x_4678_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(
                    v_pos_4677_,
                );
                if crate::leanh::lean_obj_tag(v___x_4678_) == 0 {
                    crate::leanh::lean_dec_ref(v_pos_4677_);
                    v_pos_4679_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                    v_res_4680_ = crate::leanh::lean_ctor_get(v___x_4678_, 1);
                    v_isSharedCheck_4688_ = (!crate::leanh::lean_is_exclusive(v___x_4678_)) as u8;
                    if v_isSharedCheck_4688_ == 0 {
                        v___x_4682_ = v___x_4678_;
                        v_isShared_4683_ = v_isSharedCheck_4688_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_4680_);
                        crate::leanh::lean_inc(v_pos_4679_);
                        crate::leanh::lean_dec(v___x_4678_);
                        v___x_4682_ = crate::leanh::lean_box(0);
                        v_isShared_4683_ = v_isSharedCheck_4688_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_err_4689_ = crate::leanh::lean_ctor_get(v___x_4678_, 1);
                    v_isSharedCheck_4698_ = (!crate::leanh::lean_is_exclusive(v___x_4678_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v_unused_4699_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                        crate::leanh::lean_dec(v_unused_4699_);
                        v___x_4691_ = v___x_4678_;
                        v_isShared_4692_ = v_isSharedCheck_4698_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_4689_);
                        crate::leanh::lean_dec(v___x_4678_);
                        v___x_4691_ = crate::leanh::lean_box(0);
                        v_isShared_4692_ = v_isSharedCheck_4698_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4684_, 0, v_res_4680_);
                if v_isShared_4683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4682_, 1, v___x_4684_);
                    v___x_4686_ = v___x_4682_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_pos_4679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4687_, 1, v___x_4684_);
                    v___x_4686_ = v_reuseFailAlloc_4687_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4686_;
            }
            12 => {
                v_idx_4693_ = crate::leanh::lean_ctor_get(v_pos_4677_, 1);
                v___x_4694_ = lean_nat_dec_eq(v_idx_4693_, v_idx_4693_);
                if v___x_4694_ == 0 {
                    if v_isShared_4692_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4691_, 0, v_pos_4677_);
                        v___x_4696_ = v___x_4691_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4697_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_pos_4677_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_err_4689_);
                        v___x_4696_ = v_reuseFailAlloc_4697_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4691_);
                    crate::leanh::lean_dec(v_err_4689_);
                    v___y_4654_ = v_pos_4677_;
                    state = 6;
                    continue;
                }
            }
            13 => {
                return v___x_4696_;
            }
            14 => {
                v___y_4654_ = v_pos_4701_;
                state = 6;
                continue;
            }
            15 => {
                if v___y_4706_ == 0 {
                    v_pos_4701_ = v___y_4704_;
                    v_res_4702_ = v___y_4705_;
                    state = 14;
                    continue;
                } else {
                    v_pos_4677_ = v___y_4704_;
                    state = 9;
                    continue;
                }
            }
            16 => {
                v___x_4710_ = lean_byte_array_size(v_array_4650_);
                v___x_4711_ = lean_nat_dec_lt(v_idx_4651_, v___x_4710_);
                if v___x_4711_ == 0 {
                    crate::leanh::lean_dec(v_idx_4651_);
                    crate::leanh::lean_dec_ref(v_array_4650_);
                    v_pos_4701_ = v_pos_4708_;
                    v_res_4702_ = v_res_4709_;
                    state = 14;
                    continue;
                } else {
                    v___x_4712_ = lean_byte_array_fget(v_array_4650_, v_idx_4651_);
                    crate::leanh::lean_dec(v_idx_4651_);
                    crate::leanh::lean_dec_ref(v_array_4650_);
                    v___x_4713_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                    v___x_4714_ = lean_uint8_dec_le(v___x_4713_, v___x_4712_);
                    if v___x_4714_ == 0 {
                        v___y_4704_ = v_pos_4708_;
                        v___y_4705_ = v_res_4709_;
                        v___y_4706_ = v___x_4714_;
                        state = 15;
                        continue;
                    } else {
                        v___x_4715_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                        v___x_4716_ = lean_uint8_dec_le(v___x_4712_, v___x_4715_);
                        v___y_4704_ = v_pos_4708_;
                        v___y_4705_ = v_res_4709_;
                        v___y_4706_ = v___x_4716_;
                        state = 15;
                        continue;
                    }
                }
            }
            17 => {
                v___x_4730_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4730_, 0, v_res_4726_);
                if v_isShared_4729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4728_, 1, v___x_4730_);
                    v___x_4732_ = v___x_4728_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_pos_4725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4733_, 1, v___x_4730_);
                    v___x_4732_ = v_reuseFailAlloc_4733_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4732_;
            }
            19 => {
                if v_isShared_4739_ == 0 {
                    v___x_4741_ = v___x_4738_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4742_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_pos_4735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_err_4736_);
                    v___x_4741_ = v_reuseFailAlloc_4742_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(
    mut v_config_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(
        v_config_4744_,
        v_a_4745_,
    );
    crate::leanh::lean_dec_ref(v_config_4744_);
    return v_res_4746_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(
    mut v___x_4747_: *mut crate::leanh::LeanObject,
    mut v___x_4748_: *mut crate::leanh::LeanObject,
    mut v___x_4749_: *mut crate::leanh::LeanObject,
    mut v_inst_4750_: *mut crate::leanh::LeanObject,
    mut v_R_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_b_4753_: u8,
    mut v_c_4754_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4755_: u8 = 0;
    v___x_4755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_4747_, v___x_4748_, v___x_4749_, v_a_4752_, v_b_4753_);
    return v___x_4755_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(
    mut v___x_4756_: *mut crate::leanh::LeanObject,
    mut v___x_4757_: *mut crate::leanh::LeanObject,
    mut v___x_4758_: *mut crate::leanh::LeanObject,
    mut v_inst_4759_: *mut crate::leanh::LeanObject,
    mut v_R_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_b_4762_: *mut crate::leanh::LeanObject,
    mut v_c_4763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4764_: u8 = 0;
    let mut v_res_4765_: u8 = 0;
    let mut v_r_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4764_ = (crate::leanh::lean_unbox(v_b_4762_) as u8);
    v_res_4765_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_4756_, v___x_4757_, v___x_4758_, v_inst_4759_, v_R_4760_, v_a_4761_, v_b_boxed_4764_, v_c_4763_);
    crate::leanh::lean_dec_ref(v___x_4757_);
    crate::leanh::lean_dec_ref(v___x_4756_);
    v_r_4766_ = crate::leanh::lean_box((v_res_4765_) as usize);
    return v_r_4766_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(
    mut v___x_4767_: *mut crate::leanh::LeanObject,
    mut v___x_4768_: *mut crate::leanh::LeanObject,
    mut v___x_4769_: *mut crate::leanh::LeanObject,
    mut v_inst_4770_: *mut crate::leanh::LeanObject,
    mut v_R_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
    mut v_b_4773_: u8,
    mut v_c_4774_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4775_: u8 = 0;
    v___x_4775_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_4767_, v___x_4768_, v_a_4772_, v_b_4773_);
    return v___x_4775_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(
    mut v___x_4776_: *mut crate::leanh::LeanObject,
    mut v___x_4777_: *mut crate::leanh::LeanObject,
    mut v___x_4778_: *mut crate::leanh::LeanObject,
    mut v_inst_4779_: *mut crate::leanh::LeanObject,
    mut v_R_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_b_4782_: *mut crate::leanh::LeanObject,
    mut v_c_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4784_: u8 = 0;
    let mut v_res_4785_: u8 = 0;
    let mut v_r_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4784_ = (crate::leanh::lean_unbox(v_b_4782_) as u8);
    v_res_4785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_4776_, v___x_4777_, v___x_4778_, v_inst_4779_, v_R_4780_, v_a_4781_, v_b_boxed_4784_, v_c_4783_);
    crate::leanh::lean_dec(v___x_4778_);
    crate::leanh::lean_dec_ref(v___x_4777_);
    crate::leanh::lean_dec_ref(v___x_4776_);
    v_r_4786_ = crate::leanh::lean_box((v_res_4785_) as usize);
    return v_r_4786_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2()
-> u8 {
    let mut v___x_4790_: u32 = 0;
    let mut v___x_4791_: u8 = 0;
    v___x_4790_ = 47;
    v___x_4791_ = lean_uint32_to_uint8(v___x_4790_);
    return v___x_4791_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3()
-> u8 {
    let mut v___x_4792_: u32 = 0;
    let mut v___x_4793_: u8 = 0;
    v___x_4792_ = 63;
    v___x_4793_ = lean_uint32_to_uint8(v___x_4792_);
    return v___x_4793_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4()
-> u8 {
    let mut v___x_4794_: u32 = 0;
    let mut v___x_4795_: u8 = 0;
    v___x_4794_ = 35;
    v___x_4795_ = lean_uint32_to_uint8(v___x_4794_);
    return v___x_4795_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
    v___x_4797_ = lean_uint8_to_nat(v___x_4796_);
    return v___x_4797_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
    v___x_4799_ = l_Nat_reprFast(v___x_4798_);
    return v___x_4799_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
    v___x_4801_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_4802_ = lean_string_append(v___x_4801_, v___x_4800_);
    return v___x_4802_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4803_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_4804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
    v___x_4805_ = lean_string_append(v___x_4804_, v___x_4803_);
    return v___x_4805_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
    v___x_4807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4807_, 0, v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10()
-> u8 {
    let mut v___x_4808_: u32 = 0;
    let mut v___x_4809_: u8 = 0;
    v___x_4808_ = 64;
    v___x_4809_ = lean_uint32_to_uint8(v___x_4808_);
    return v___x_4809_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
    v___x_4811_ = lean_uint8_to_nat(v___x_4810_);
    return v___x_4811_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
    v___x_4813_ = l_Nat_reprFast(v___x_4812_);
    return v___x_4813_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
    v___x_4815_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_4816_ = lean_string_append(v___x_4815_, v___x_4814_);
    return v___x_4816_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4817_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_4818_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
    v___x_4819_ = lean_string_append(v___x_4818_, v___x_4817_);
    return v___x_4819_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4820_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
    v___x_4821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4821_, 0, v___x_4820_);
    return v___x_4821_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(
    mut v_config_4822_: *mut crate::leanh::LeanObject,
    mut v_a_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4849_: u8 = 0;
    let mut v___y_4851_: u8 = 0;
    let mut v___y_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4856_: u8 = 0;
    let mut v___y_4857_: u8 = 0;
    let mut v_val_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: u8 = 0;
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4861_: u8 = 0;
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: u8 = 0;
    let mut v___x_4865_: u8 = 0;
    let mut v___x_4866_: u8 = 0;
    let mut v___x_4867_: u8 = 0;
    let mut v___y_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4870_: u8 = 0;
    let mut v___y_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: u8 = 0;
    let mut v___y_4874_: u8 = 0;
    let mut v_array_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4884_: u8 = 0;
    let mut v___y_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: u8 = 0;
    let mut v_pos_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    let mut v___y_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4892_: u8 = 0;
    let mut v___y_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4896_: u8 = 0;
    let mut v___y_4897_: u8 = 0;
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u16 = 0;
    let mut v_pos_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4907_: u8 = 0;
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut v_pos_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4920_: u8 = 0;
    let mut v_array_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: u8 = 0;
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: u8 = 0;
    let mut v___x_4927_: u8 = 0;
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4938_: u8 = 0;
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: u8 = 0;
    let mut v_reuseFailAlloc_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v_unused_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_pos_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4960_: u8 = 0;
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_pos_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut v_got_4987_: u8 = 0;
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut v_pos_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_4823_);
                v___x_4975_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(
                        v_config_4822_,
                        v_a_4823_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4975_) == 0 {
                    v_pos_4976_ = crate::leanh::lean_ctor_get(v___x_4975_, 0);
                    crate::leanh::lean_inc(v_pos_4976_);
                    v_res_4977_ = crate::leanh::lean_ctor_get(v___x_4975_, 1);
                    crate::leanh::lean_inc(v_res_4977_);
                    crate::leanh::lean_dec_ref_known(v___x_4975_, 2);
                    v_array_4978_ = crate::leanh::lean_ctor_get(v_pos_4976_, 0);
                    v_idx_4979_ = crate::leanh::lean_ctor_get(v_pos_4976_, 1);
                    v_isSharedCheck_4995_ = (!crate::leanh::lean_is_exclusive(v_pos_4976_)) as u8;
                    if v_isSharedCheck_4995_ == 0 {
                        v___x_4981_ = v_pos_4976_;
                        v_isShared_4982_ = v_isSharedCheck_4995_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_4979_);
                        crate::leanh::lean_inc(v_array_4978_);
                        crate::leanh::lean_dec(v_pos_4976_);
                        v___x_4981_ = crate::leanh::lean_box(0);
                        v_isShared_4982_ = v_isSharedCheck_4995_;
                        state = 22;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4975_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_4823_);
                        v_pos_4996_ = crate::leanh::lean_ctor_get(v___x_4975_, 0);
                        crate::leanh::lean_inc(v_pos_4996_);
                        v_res_4997_ = crate::leanh::lean_ctor_get(v___x_4975_, 1);
                        crate::leanh::lean_inc(v_res_4997_);
                        crate::leanh::lean_dec_ref_known(v___x_4975_, 2);
                        v_pos_4966_ = v_pos_4996_;
                        v_res_4967_ = v_res_4997_;
                        state = 20;
                        continue;
                    } else {
                        v_err_4998_ = crate::leanh::lean_ctor_get(v___x_4975_, 1);
                        crate::leanh::lean_inc(v_err_4998_);
                        crate::leanh::lean_dec_ref_known(v___x_4975_, 2);
                        v_err_4970_ = v_err_4998_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4829_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4829_, 0, v___y_4826_);
                crate::leanh::lean_ctor_set(v___x_4829_, 1, v___y_4825_);
                crate::leanh::lean_ctor_set(v___x_4829_, 2, v_port_4827_);
                v___x_4830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4830_, 0, v___y_4828_);
                crate::leanh::lean_ctor_set(v___x_4830_, 1, v___x_4829_);
                return v___x_4830_;
            }
            2 => {
                v___x_4835_ = crate::leanh::lean_box(0);
                v___y_4825_ = v___y_4832_;
                v___y_4826_ = v___y_4833_;
                v_port_4827_ = v___x_4835_;
                v___y_4828_ = v_pos_4834_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4838_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1;
                v___x_4839_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4839_, 0, v___y_4837_);
                crate::leanh::lean_ctor_set(v___x_4839_, 1, v___x_4838_);
                return v___x_4839_;
            }
            4 => {
                v___x_4844_ = crate::leanh::lean_box(1);
                v___y_4825_ = v___y_4841_;
                v___y_4826_ = v___y_4843_;
                v_port_4827_ = v___x_4844_;
                v___y_4828_ = v___y_4842_;
                state = 1;
                continue;
            }
            5 => {
                if v___y_4849_ == 0 {
                    crate::leanh::lean_dec(v___y_4848_);
                    crate::leanh::lean_dec_ref(v___y_4846_);
                    v___y_4837_ = v___y_4847_;
                    state = 3;
                    continue;
                } else {
                    v___y_4841_ = v___y_4846_;
                    v___y_4842_ = v___y_4847_;
                    v___y_4843_ = v___y_4848_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_4857_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_4855_) == 0 {
                        crate::leanh::lean_dec(v___y_4854_);
                        crate::leanh::lean_dec_ref(v___y_4852_);
                        v___y_4837_ = v___y_4853_;
                        state = 3;
                        continue;
                    } else {
                        v_val_4858_ = crate::leanh::lean_ctor_get(v___y_4855_, 0);
                        crate::leanh::lean_inc(v_val_4858_);
                        crate::leanh::lean_dec_ref_known(v___y_4855_, 1);
                        v___x_4859_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                        v___x_4860_ = (crate::leanh::lean_unbox(v_val_4858_) as u8);
                        v___x_4861_ = lean_uint8_dec_eq(v___x_4860_, v___x_4859_);
                        if v___x_4861_ == 0 {
                            v___x_4862_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                            v___x_4863_ = (crate::leanh::lean_unbox(v_val_4858_) as u8);
                            v___x_4864_ = lean_uint8_dec_eq(v___x_4863_, v___x_4862_);
                            if v___x_4864_ == 0 {
                                v___x_4865_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
                                v___x_4866_ = (crate::leanh::lean_unbox(v_val_4858_) as u8);
                                crate::leanh::lean_dec(v_val_4858_);
                                v___x_4867_ = lean_uint8_dec_eq(v___x_4866_, v___x_4865_);
                                if v___x_4867_ == 0 {
                                    v___y_4846_ = v___y_4852_;
                                    v___y_4847_ = v___y_4853_;
                                    v___y_4848_ = v___y_4854_;
                                    v___y_4849_ = v___x_4867_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___y_4846_ = v___y_4852_;
                                    v___y_4847_ = v___y_4853_;
                                    v___y_4848_ = v___y_4854_;
                                    v___y_4849_ = v___y_4851_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_4858_);
                                v___y_4846_ = v___y_4852_;
                                v___y_4847_ = v___y_4853_;
                                v___y_4848_ = v___y_4854_;
                                v___y_4849_ = v___y_4851_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_4858_);
                            v___y_4846_ = v___y_4852_;
                            v___y_4847_ = v___y_4853_;
                            v___y_4848_ = v___y_4854_;
                            v___y_4849_ = v___y_4856_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4855_);
                    v___y_4841_ = v___y_4852_;
                    v___y_4842_ = v___y_4853_;
                    v___y_4843_ = v___y_4854_;
                    state = 4;
                    continue;
                }
            }
            7 => {
                v_array_4875_ = crate::leanh::lean_ctor_get(v___y_4869_, 0);
                v_idx_4876_ = crate::leanh::lean_ctor_get(v___y_4869_, 1);
                v___x_4877_ = lean_byte_array_size(v_array_4875_);
                v___x_4878_ = lean_nat_dec_lt(v_idx_4876_, v___x_4877_);
                if v___x_4878_ == 0 {
                    v___x_4879_ = crate::leanh::lean_box(0);
                    v___y_4851_ = v___y_4870_;
                    v___y_4852_ = v___y_4871_;
                    v___y_4853_ = v___y_4869_;
                    v___y_4854_ = v___y_4872_;
                    v___y_4855_ = v___x_4879_;
                    v___y_4856_ = v___y_4873_;
                    v___y_4857_ = v___y_4873_;
                    state = 6;
                    continue;
                } else {
                    v___x_4880_ = lean_byte_array_fget(v_array_4875_, v_idx_4876_);
                    v___x_4881_ = crate::leanh::lean_box((v___x_4880_) as usize);
                    v___x_4882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4882_, 0, v___x_4881_);
                    v___y_4851_ = v___y_4870_;
                    v___y_4852_ = v___y_4871_;
                    v___y_4853_ = v___y_4869_;
                    v___y_4854_ = v___y_4872_;
                    v___y_4855_ = v___x_4882_;
                    v___y_4856_ = v___y_4873_;
                    v___y_4857_ = v___y_4874_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_4889_ = 0;
                v___y_4869_ = v_pos_4888_;
                v___y_4870_ = v___y_4884_;
                v___y_4871_ = v___y_4885_;
                v___y_4872_ = v___y_4886_;
                v___y_4873_ = v___y_4887_;
                v___y_4874_ = v___x_4889_;
                state = 7;
                continue;
            }
            9 => {
                crate::leanh::lean_dec(v___y_4891_);
                if v___y_4897_ == 0 {
                    v___y_4884_ = v___y_4892_;
                    v___y_4885_ = v___y_4893_;
                    v___y_4886_ = v___y_4895_;
                    v___y_4887_ = v___y_4896_;
                    v_pos_4888_ = v___y_4894_;
                    state = 8;
                    continue;
                } else {
                    if v___y_4896_ == 0 {
                        v___y_4869_ = v___y_4894_;
                        v___y_4870_ = v___y_4892_;
                        v___y_4871_ = v___y_4893_;
                        v___y_4872_ = v___y_4895_;
                        v___y_4873_ = v___y_4896_;
                        v___y_4874_ = v___y_4896_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4898_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___y_4894_);
                        if crate::leanh::lean_obj_tag(v___x_4898_) == 0 {
                            v_pos_4899_ = crate::leanh::lean_ctor_get(v___x_4898_, 0);
                            crate::leanh::lean_inc(v_pos_4899_);
                            v_res_4900_ = crate::leanh::lean_ctor_get(v___x_4898_, 1);
                            crate::leanh::lean_inc(v_res_4900_);
                            crate::leanh::lean_dec_ref_known(v___x_4898_, 2);
                            v___x_4901_ = crate::leanh::lean_alloc_ctor(2, 0, (2) as u32);
                            v___x_4902_ = (crate::leanh::lean_unbox(v_res_4900_) as u16);
                            crate::leanh::lean_dec(v_res_4900_);
                            crate::leanh::lean_ctor_set_uint16(v___x_4901_, 0 as u32, v___x_4902_);
                            v___y_4825_ = v___y_4893_;
                            v___y_4826_ = v___y_4895_;
                            v_port_4827_ = v___x_4901_;
                            v___y_4828_ = v_pos_4899_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_4895_);
                            crate::leanh::lean_dec_ref(v___y_4893_);
                            v_pos_4903_ = crate::leanh::lean_ctor_get(v___x_4898_, 0);
                            v_err_4904_ = crate::leanh::lean_ctor_get(v___x_4898_, 1);
                            v_isSharedCheck_4911_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4898_)) as u8;
                            if v_isSharedCheck_4911_ == 0 {
                                v___x_4906_ = v___x_4898_;
                                v_isShared_4907_ = v_isSharedCheck_4911_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_4904_);
                                crate::leanh::lean_inc(v_pos_4903_);
                                crate::leanh::lean_dec(v___x_4898_);
                                v___x_4906_ = crate::leanh::lean_box(0);
                                v_isShared_4907_ = v_isSharedCheck_4911_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                if v_isShared_4907_ == 0 {
                    v___x_4909_ = v___x_4906_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_pos_4903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_err_4904_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4909_;
            }
            12 => {
                v___x_4915_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(
                    v_config_4822_,
                    v_pos_4913_,
                );
                if crate::leanh::lean_obj_tag(v___x_4915_) == 0 {
                    v_pos_4916_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                    v_res_4917_ = crate::leanh::lean_ctor_get(v___x_4915_, 1);
                    v_isSharedCheck_4955_ = (!crate::leanh::lean_is_exclusive(v___x_4915_)) as u8;
                    if v_isSharedCheck_4955_ == 0 {
                        v___x_4919_ = v___x_4915_;
                        v_isShared_4920_ = v_isSharedCheck_4955_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_4917_);
                        crate::leanh::lean_inc(v_pos_4916_);
                        crate::leanh::lean_dec(v___x_4915_);
                        v___x_4919_ = crate::leanh::lean_box(0);
                        v_isShared_4920_ = v_isSharedCheck_4955_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_res_4914_);
                    v_pos_4956_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                    v_err_4957_ = crate::leanh::lean_ctor_get(v___x_4915_, 1);
                    v_isSharedCheck_4964_ = (!crate::leanh::lean_is_exclusive(v___x_4915_)) as u8;
                    if v_isSharedCheck_4964_ == 0 {
                        v___x_4959_ = v___x_4915_;
                        v_isShared_4960_ = v_isSharedCheck_4964_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_4957_);
                        crate::leanh::lean_inc(v_pos_4956_);
                        crate::leanh::lean_dec(v___x_4915_);
                        v___x_4959_ = crate::leanh::lean_box(0);
                        v_isShared_4960_ = v_isSharedCheck_4964_;
                        state = 18;
                        continue;
                    }
                }
            }
            13 => {
                v_array_4921_ = crate::leanh::lean_ctor_get(v_pos_4916_, 0);
                v_idx_4922_ = crate::leanh::lean_ctor_get(v_pos_4916_, 1);
                v___x_4923_ = lean_byte_array_size(v_array_4921_);
                v___x_4924_ = lean_nat_dec_lt(v_idx_4922_, v___x_4923_);
                if v___x_4924_ == 0 {
                    crate::leanh::lean_del_object(v___x_4919_);
                    v___y_4832_ = v_res_4917_;
                    v___y_4833_ = v_res_4914_;
                    v_pos_4834_ = v_pos_4916_;
                    state = 2;
                    continue;
                } else {
                    v___x_4925_ = lean_byte_array_fget(v_array_4921_, v_idx_4922_);
                    v___x_4926_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_4927_ = lean_uint8_dec_eq(v___x_4925_, v___x_4926_);
                    if v___x_4927_ == 0 {
                        crate::leanh::lean_del_object(v___x_4919_);
                        v___y_4832_ = v_res_4917_;
                        v___y_4833_ = v_res_4914_;
                        v_pos_4834_ = v_pos_4916_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_4927_ == 0 {
                            crate::leanh::lean_del_object(v___x_4919_);
                            v___y_4832_ = v_res_4917_;
                            v___y_4833_ = v_res_4914_;
                            v_pos_4834_ = v_pos_4916_;
                            state = 2;
                            continue;
                        } else {
                            if v___x_4924_ == 0 {
                                crate::leanh::lean_dec(v_res_4917_);
                                crate::leanh::lean_dec(v_res_4914_);
                                v___x_4928_ = crate::leanh::lean_box(0);
                                if v_isShared_4920_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_4919_, 1);
                                    crate::leanh::lean_ctor_set(v___x_4919_, 1, v___x_4928_);
                                    v___x_4930_ = v___x_4919_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4931_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4931_,
                                        0,
                                        v_pos_4916_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4931_,
                                        1,
                                        v___x_4928_,
                                    );
                                    v___x_4930_ = v_reuseFailAlloc_4931_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                if v___x_4927_ == 0 {
                                    crate::leanh::lean_dec(v_res_4917_);
                                    crate::leanh::lean_dec(v_res_4914_);
                                    v___x_4932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                                    if v_isShared_4920_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_4919_, 1);
                                        crate::leanh::lean_ctor_set(v___x_4919_, 1, v___x_4932_);
                                        v___x_4934_ = v___x_4919_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4935_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4935_,
                                            0,
                                            v_pos_4916_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4935_,
                                            1,
                                            v___x_4932_,
                                        );
                                        v___x_4934_ = v_reuseFailAlloc_4935_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_idx_4922_);
                                    crate::leanh::lean_inc_ref(v_array_4921_);
                                    crate::leanh::lean_del_object(v___x_4919_);
                                    v_isSharedCheck_4952_ =
                                        (!crate::leanh::lean_is_exclusive(v_pos_4916_)) as u8;
                                    if v_isSharedCheck_4952_ == 0 {
                                        v_unused_4953_ =
                                            crate::leanh::lean_ctor_get(v_pos_4916_, 1);
                                        crate::leanh::lean_dec(v_unused_4953_);
                                        v_unused_4954_ =
                                            crate::leanh::lean_ctor_get(v_pos_4916_, 0);
                                        crate::leanh::lean_dec(v_unused_4954_);
                                        v___x_4937_ = v_pos_4916_;
                                        v_isShared_4938_ = v_isSharedCheck_4952_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pos_4916_);
                                        v___x_4937_ = crate::leanh::lean_box(0);
                                        v_isShared_4938_ = v_isSharedCheck_4952_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            14 => {
                return v___x_4930_;
            }
            15 => {
                return v___x_4934_;
            }
            16 => {
                v___x_4939_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4940_ = lean_nat_add(v_idx_4922_, v___x_4939_);
                crate::leanh::lean_dec(v_idx_4922_);
                crate::leanh::lean_inc(v___x_4940_);
                crate::leanh::lean_inc_ref(v_array_4921_);
                if v_isShared_4938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4937_, 1, v___x_4940_);
                    v___x_4942_ = v___x_4937_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_array_4921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 1, v___x_4940_);
                    v___x_4942_ = v_reuseFailAlloc_4951_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4943_ = lean_nat_dec_lt(v___x_4940_, v___x_4923_);
                if v___x_4943_ == 0 {
                    crate::leanh::lean_dec(v___x_4940_);
                    crate::leanh::lean_dec_ref(v_array_4921_);
                    v___y_4884_ = v___x_4927_;
                    v___y_4885_ = v_res_4917_;
                    v___y_4886_ = v_res_4914_;
                    v___y_4887_ = v___x_4924_;
                    v_pos_4888_ = v___x_4942_;
                    state = 8;
                    continue;
                } else {
                    v___x_4944_ = lean_byte_array_fget(v_array_4921_, v___x_4940_);
                    crate::leanh::lean_dec(v___x_4940_);
                    crate::leanh::lean_dec_ref(v_array_4921_);
                    v___x_4945_ = crate::leanh::lean_box((v___x_4944_) as usize);
                    v___x_4946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4946_, 0, v___x_4945_);
                    v___x_4947_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                    v___x_4948_ = lean_uint8_dec_le(v___x_4947_, v___x_4944_);
                    if v___x_4948_ == 0 {
                        v___y_4891_ = v___x_4946_;
                        v___y_4892_ = v___x_4927_;
                        v___y_4893_ = v_res_4917_;
                        v___y_4894_ = v___x_4942_;
                        v___y_4895_ = v_res_4914_;
                        v___y_4896_ = v___x_4924_;
                        v___y_4897_ = v___x_4948_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4949_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                        v___x_4950_ = lean_uint8_dec_le(v___x_4944_, v___x_4949_);
                        v___y_4891_ = v___x_4946_;
                        v___y_4892_ = v___x_4927_;
                        v___y_4893_ = v_res_4917_;
                        v___y_4894_ = v___x_4942_;
                        v___y_4895_ = v_res_4914_;
                        v___y_4896_ = v___x_4924_;
                        v___y_4897_ = v___x_4950_;
                        state = 9;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4960_ == 0 {
                    v___x_4962_ = v___x_4959_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_pos_4956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_err_4957_);
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4962_;
            }
            20 => {
                v___x_4968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4968_, 0, v_res_4967_);
                v_pos_4913_ = v_pos_4966_;
                v_res_4914_ = v___x_4968_;
                state = 12;
                continue;
            }
            21 => {
                v_idx_4971_ = crate::leanh::lean_ctor_get(v_a_4823_, 1);
                v___x_4972_ = lean_nat_dec_eq(v_idx_4971_, v_idx_4971_);
                if v___x_4972_ == 0 {
                    v___x_4973_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4973_, 0, v_a_4823_);
                    crate::leanh::lean_ctor_set(v___x_4973_, 1, v_err_4970_);
                    return v___x_4973_;
                } else {
                    crate::leanh::lean_dec(v_err_4970_);
                    v___x_4974_ = crate::leanh::lean_box(0);
                    v_pos_4913_ = v_a_4823_;
                    v_res_4914_ = v___x_4974_;
                    state = 12;
                    continue;
                }
            }
            22 => {
                v___x_4983_ = lean_byte_array_size(v_array_4978_);
                v___x_4984_ = lean_nat_dec_lt(v_idx_4979_, v___x_4983_);
                if v___x_4984_ == 0 {
                    crate::leanh::lean_del_object(v___x_4981_);
                    crate::leanh::lean_dec(v_idx_4979_);
                    crate::leanh::lean_dec_ref(v_array_4978_);
                    crate::leanh::lean_dec(v_res_4977_);
                    v___x_4985_ = crate::leanh::lean_box(0);
                    v_err_4970_ = v___x_4985_;
                    state = 21;
                    continue;
                } else {
                    v___x_4986_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                    v_got_4987_ = lean_byte_array_fget(v_array_4978_, v_idx_4979_);
                    v___x_4988_ = lean_uint8_dec_eq(v_got_4987_, v___x_4986_);
                    if v___x_4988_ == 0 {
                        crate::leanh::lean_del_object(v___x_4981_);
                        crate::leanh::lean_dec(v_idx_4979_);
                        crate::leanh::lean_dec_ref(v_array_4978_);
                        crate::leanh::lean_dec(v_res_4977_);
                        v___x_4989_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
                        v_err_4970_ = v___x_4989_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_4823_);
                        v___x_4990_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4991_ = lean_nat_add(v_idx_4979_, v___x_4990_);
                        crate::leanh::lean_dec(v_idx_4979_);
                        if v_isShared_4982_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4981_, 1, v___x_4991_);
                            v___x_4993_ = v___x_4981_;
                            state = 23;
                            continue;
                        } else {
                            v_reuseFailAlloc_4994_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_array_4978_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 1, v___x_4991_);
                            v___x_4993_ = v_reuseFailAlloc_4994_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            23 => {
                v_pos_4966_ = v___x_4993_;
                v_res_4967_ = v_res_4977_;
                state = 20;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(
    mut v_config_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5001_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(
        v_config_4999_,
        v_a_5000_,
    );
    crate::leanh::lean_dec_ref(v_config_4999_);
    return v_res_5001_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(
    mut v_c_5002_: u8,
) -> u8 {
    let mut v___y_5004_: u8 = 0;
    let mut v___x_5005_: u8 = 0;
    let mut v___x_5006_: u8 = 0;
    let mut v___y_5008_: u8 = 0;
    let mut v___x_5009_: u8 = 0;
    let mut v___x_5010_: u8 = 0;
    let mut v___x_5011_: u8 = 0;
    let mut v___x_5012_: u8 = 0;
    let mut v___y_5014_: u8 = 0;
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: u8 = 0;
    let mut v___x_5020_: u8 = 0;
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: u8 = 0;
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: u8 = 0;
    let mut v___x_5027_: u8 = 0;
    let mut v___x_5028_: u8 = 0;
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: u8 = 0;
    let mut v___x_5032_: u8 = 0;
    let mut v___y_5034_: u8 = 0;
    let mut v___x_5035_: u8 = 0;
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: u8 = 0;
    let mut v___y_5040_: u8 = 0;
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: u8 = 0;
    let mut v___x_5043_: u8 = 0;
    let mut v___x_5044_: u8 = 0;
    let mut v___y_5046_: u8 = 0;
    let mut v___x_5047_: u8 = 0;
    let mut v___x_5048_: u8 = 0;
    let mut v___x_5049_: u8 = 0;
    let mut v___x_5050_: u8 = 0;
    let mut v___y_5052_: u8 = 0;
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5054_: u8 = 0;
    let mut v___x_5055_: u8 = 0;
    let mut v___x_5056_: u8 = 0;
    let mut v___y_5058_: u8 = 0;
    let mut v___x_5059_: u8 = 0;
    let mut v___x_5060_: u8 = 0;
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: u8 = 0;
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: u8 = 0;
    let mut v___x_5066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5063_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_5064_ = lean_uint8_dec_le(v___x_5063_, v_c_5002_);
                if v___x_5064_ == 0 {
                    v___y_5058_ = v___x_5064_;
                    state = 8;
                    continue;
                } else {
                    v___x_5065_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_5066_ = lean_uint8_dec_le(v_c_5002_, v___x_5065_);
                    v___y_5058_ = v___x_5066_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                if v___y_5004_ == 0 {
                    v___x_5005_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                    v___x_5006_ = lean_uint8_dec_eq(v_c_5002_, v___x_5005_);
                    if v___x_5006_ == 0 {
                        return v___y_5004_;
                    } else {
                        return v___x_5006_;
                    }
                } else {
                    return v___y_5004_;
                }
            }
            2 => {
                if v___y_5008_ == 0 {
                    v___x_5009_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5010_ = lean_uint8_dec_eq(v_c_5002_, v___x_5009_);
                    if v___x_5010_ == 0 {
                        v___x_5011_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5012_ = lean_uint8_dec_eq(v_c_5002_, v___x_5011_);
                        v___y_5004_ = v___x_5012_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5004_ = v___x_5010_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_5008_;
                }
            }
            3 => {
                if v___y_5014_ == 0 {
                    v___x_5015_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5016_ = lean_uint8_dec_eq(v_c_5002_, v___x_5015_);
                    if v___x_5016_ == 0 {
                        v___x_5017_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5018_ = lean_uint8_dec_eq(v_c_5002_, v___x_5017_);
                        if v___x_5018_ == 0 {
                            v___x_5019_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5020_ = lean_uint8_dec_eq(v_c_5002_, v___x_5019_);
                            if v___x_5020_ == 0 {
                                v___x_5021_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5022_ = lean_uint8_dec_eq(v_c_5002_, v___x_5021_);
                                if v___x_5022_ == 0 {
                                    v___x_5023_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5024_ = lean_uint8_dec_eq(v_c_5002_, v___x_5023_);
                                    if v___x_5024_ == 0 {
                                        v___x_5025_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5026_ = lean_uint8_dec_eq(v_c_5002_, v___x_5025_);
                                        if v___x_5026_ == 0 {
                                            v___x_5027_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5028_ = lean_uint8_dec_eq(v_c_5002_, v___x_5027_);
                                            if v___x_5028_ == 0 {
                                                v___x_5029_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5030_ =
                                                    lean_uint8_dec_eq(v_c_5002_, v___x_5029_);
                                                if v___x_5030_ == 0 {
                                                    v___x_5031_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5032_ =
                                                        lean_uint8_dec_eq(v_c_5002_, v___x_5031_);
                                                    v___y_5008_ = v___x_5032_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___y_5008_ = v___x_5030_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5008_ = v___x_5028_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            v___y_5008_ = v___x_5026_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v___y_5008_ = v___x_5024_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_5008_ = v___x_5022_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_5008_ = v___x_5020_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_5008_ = v___x_5018_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_5008_ = v___x_5016_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_5014_;
                }
            }
            4 => {
                if v___y_5034_ == 0 {
                    v___x_5035_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5036_ = lean_uint8_dec_eq(v_c_5002_, v___x_5035_);
                    if v___x_5036_ == 0 {
                        v___x_5037_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5038_ = lean_uint8_dec_eq(v_c_5002_, v___x_5037_);
                        v___y_5014_ = v___x_5038_;
                        state = 3;
                        continue;
                    } else {
                        v___y_5014_ = v___x_5036_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_5034_;
                }
            }
            5 => {
                if v___y_5040_ == 0 {
                    v___x_5041_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5042_ = lean_uint8_dec_eq(v_c_5002_, v___x_5041_);
                    if v___x_5042_ == 0 {
                        v___x_5043_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5044_ = lean_uint8_dec_eq(v_c_5002_, v___x_5043_);
                        v___y_5034_ = v___x_5044_;
                        state = 4;
                        continue;
                    } else {
                        v___y_5034_ = v___x_5042_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_5040_;
                }
            }
            6 => {
                if v___y_5046_ == 0 {
                    v___x_5047_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5048_ = lean_uint8_dec_eq(v_c_5002_, v___x_5047_);
                    if v___x_5048_ == 0 {
                        v___x_5049_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5050_ = lean_uint8_dec_eq(v_c_5002_, v___x_5049_);
                        v___y_5040_ = v___x_5050_;
                        state = 5;
                        continue;
                    } else {
                        v___y_5040_ = v___x_5048_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_5046_;
                }
            }
            7 => {
                if v___y_5052_ == 0 {
                    v___x_5053_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5054_ = lean_uint8_dec_le(v___x_5053_, v_c_5002_);
                    if v___x_5054_ == 0 {
                        v___y_5046_ = v___x_5054_;
                        state = 6;
                        continue;
                    } else {
                        v___x_5055_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5056_ = lean_uint8_dec_le(v_c_5002_, v___x_5055_);
                        v___y_5046_ = v___x_5056_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_5052_;
                }
            }
            8 => {
                if v___y_5058_ == 0 {
                    v___x_5059_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5060_ = lean_uint8_dec_le(v___x_5059_, v_c_5002_);
                    if v___x_5060_ == 0 {
                        v___y_5052_ = v___x_5060_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5061_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5062_ = lean_uint8_dec_le(v_c_5002_, v___x_5061_);
                        v___y_5052_ = v___x_5062_;
                        state = 7;
                        continue;
                    }
                } else {
                    return v___y_5058_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(
    mut v_c_5067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_5068_: u8 = 0;
    let mut v_res_5069_: u8 = 0;
    let mut v_r_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_5068_ = (crate::leanh::lean_unbox(v_c_5067_) as u8);
    v_res_5069_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(
        v_c_boxed_5068_,
    );
    v_r_5070_ = crate::leanh::lean_box((v_res_5069_) as usize);
    return v_r_5070_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(
    mut v_config_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_maxSegmentLength_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v_lower_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    let mut v___x_5098_: u8 = 0;
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxSegmentLength_5074_ = crate::leanh::lean_ctor_get(v_config_5072_, 3);
                v___f_5075_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0;
                v___x_5076_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_5073_);
                v___x_5077_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_5075_, v_maxSegmentLength_5074_, v___x_5076_, v_a_5073_);
                v_snd_5078_ = crate::leanh::lean_ctor_get(v___x_5077_, 1);
                crate::leanh::lean_inc(v_snd_5078_);
                v_fst_5079_ = crate::leanh::lean_ctor_get(v___x_5077_, 0);
                crate::leanh::lean_inc(v_fst_5079_);
                crate::leanh::lean_dec_ref(v___x_5077_);
                v_fst_5080_ = crate::leanh::lean_ctor_get(v_snd_5078_, 0);
                crate::leanh::lean_inc(v_fst_5080_);
                crate::leanh::lean_dec(v_snd_5078_);
                v_array_5081_ = crate::leanh::lean_ctor_get(v_a_5073_, 0);
                v_idx_5082_ = crate::leanh::lean_ctor_get(v_a_5073_, 1);
                v_isSharedCheck_5099_ = (!crate::leanh::lean_is_exclusive(v_a_5073_)) as u8;
                if v_isSharedCheck_5099_ == 0 {
                    v___x_5084_ = v_a_5073_;
                    v_isShared_5085_ = v_isSharedCheck_5099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_5082_);
                    crate::leanh::lean_inc(v_array_5081_);
                    crate::leanh::lean_dec(v_a_5073_);
                    v___x_5084_ = crate::leanh::lean_box(0);
                    v_isShared_5085_ = v_isSharedCheck_5099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5093_ = lean_nat_add(v_idx_5082_, v_fst_5079_);
                crate::leanh::lean_dec(v_fst_5079_);
                v___x_5094_ = lean_byte_array_size(v_array_5081_);
                v___x_5098_ = lean_nat_dec_le(v_idx_5082_, v___x_5076_);
                if v___x_5098_ == 0 {
                    v___y_5096_ = v_idx_5082_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_5082_);
                    v___y_5096_ = v___x_5076_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_5089_ = l_ByteArray_toByteSlice(v_array_5081_, v_lower_5087_, v_upper_5088_);
                if v_isShared_5085_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5084_, 1, v___x_5089_);
                    crate::leanh::lean_ctor_set(v___x_5084_, 0, v_fst_5080_);
                    v___x_5091_ = v___x_5084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_fst_5080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5092_, 1, v___x_5089_);
                    v___x_5091_ = v_reuseFailAlloc_5092_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5091_;
            }
            4 => {
                v___x_5097_ = lean_nat_dec_le(v___x_5093_, v___x_5094_);
                if v___x_5097_ == 0 {
                    crate::leanh::lean_dec(v___x_5093_);
                    v_lower_5087_ = v___y_5096_;
                    v_upper_5088_ = v___x_5094_;
                    state = 2;
                    continue;
                } else {
                    v_lower_5087_ = v___y_5096_;
                    v_upper_5088_ = v___x_5093_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(
    mut v_config_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5102_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(
        v_config_5100_,
        v_a_5101_,
    );
    crate::leanh::lean_dec_ref(v_config_5100_);
    return v_res_5102_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(
    mut v___y_5103_: u8,
) -> u8 {
    let mut v___y_5105_: u8 = 0;
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: u8 = 0;
    let mut v___y_5111_: u8 = 0;
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5113_: u8 = 0;
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: u8 = 0;
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: u8 = 0;
    let mut v___x_5121_: u8 = 0;
    let mut v___x_5122_: u8 = 0;
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: u8 = 0;
    let mut v___x_5125_: u8 = 0;
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: u8 = 0;
    let mut v___x_5129_: u8 = 0;
    let mut v___y_5131_: u8 = 0;
    let mut v___x_5132_: u8 = 0;
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: u8 = 0;
    let mut v___y_5137_: u8 = 0;
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: u8 = 0;
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: u8 = 0;
    let mut v___y_5143_: u8 = 0;
    let mut v___x_5144_: u8 = 0;
    let mut v___x_5145_: u8 = 0;
    let mut v___x_5146_: u8 = 0;
    let mut v___x_5147_: u8 = 0;
    let mut v___y_5149_: u8 = 0;
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: u8 = 0;
    let mut v___y_5155_: u8 = 0;
    let mut v___x_5156_: u8 = 0;
    let mut v___x_5157_: u8 = 0;
    let mut v___x_5158_: u8 = 0;
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: u8 = 0;
    let mut v___x_5163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5160_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_5161_ = lean_uint8_dec_le(v___x_5160_, v___y_5103_);
                if v___x_5161_ == 0 {
                    v___y_5155_ = v___x_5161_;
                    state = 7;
                    continue;
                } else {
                    v___x_5162_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_5163_ = lean_uint8_dec_le(v___y_5103_, v___x_5162_);
                    v___y_5155_ = v___x_5163_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_5105_ == 0 {
                    v___x_5106_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5107_ = lean_uint8_dec_eq(v___y_5103_, v___x_5106_);
                    if v___x_5107_ == 0 {
                        v___x_5108_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5109_ = lean_uint8_dec_eq(v___y_5103_, v___x_5108_);
                        return v___x_5109_;
                    } else {
                        return v___x_5107_;
                    }
                } else {
                    return v___y_5105_;
                }
            }
            2 => {
                if v___y_5111_ == 0 {
                    v___x_5112_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5113_ = lean_uint8_dec_eq(v___y_5103_, v___x_5112_);
                    if v___x_5113_ == 0 {
                        v___x_5114_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5115_ = lean_uint8_dec_eq(v___y_5103_, v___x_5114_);
                        if v___x_5115_ == 0 {
                            v___x_5116_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5117_ = lean_uint8_dec_eq(v___y_5103_, v___x_5116_);
                            if v___x_5117_ == 0 {
                                v___x_5118_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5119_ = lean_uint8_dec_eq(v___y_5103_, v___x_5118_);
                                if v___x_5119_ == 0 {
                                    v___x_5120_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5121_ = lean_uint8_dec_eq(v___y_5103_, v___x_5120_);
                                    if v___x_5121_ == 0 {
                                        v___x_5122_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5123_ = lean_uint8_dec_eq(v___y_5103_, v___x_5122_);
                                        if v___x_5123_ == 0 {
                                            v___x_5124_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5125_ =
                                                lean_uint8_dec_eq(v___y_5103_, v___x_5124_);
                                            if v___x_5125_ == 0 {
                                                v___x_5126_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5127_ =
                                                    lean_uint8_dec_eq(v___y_5103_, v___x_5126_);
                                                if v___x_5127_ == 0 {
                                                    v___x_5128_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5129_ =
                                                        lean_uint8_dec_eq(v___y_5103_, v___x_5128_);
                                                    v___y_5105_ = v___x_5129_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_5105_ = v___x_5127_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5105_ = v___x_5125_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_5105_ = v___x_5123_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_5105_ = v___x_5121_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_5105_ = v___x_5119_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_5105_ = v___x_5117_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_5105_ = v___x_5115_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_5105_ = v___x_5113_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_5111_;
                }
            }
            3 => {
                if v___y_5131_ == 0 {
                    v___x_5132_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5133_ = lean_uint8_dec_eq(v___y_5103_, v___x_5132_);
                    if v___x_5133_ == 0 {
                        v___x_5134_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5135_ = lean_uint8_dec_eq(v___y_5103_, v___x_5134_);
                        v___y_5111_ = v___x_5135_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5111_ = v___x_5133_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_5131_;
                }
            }
            4 => {
                if v___y_5137_ == 0 {
                    v___x_5138_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5139_ = lean_uint8_dec_eq(v___y_5103_, v___x_5138_);
                    if v___x_5139_ == 0 {
                        v___x_5140_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5141_ = lean_uint8_dec_eq(v___y_5103_, v___x_5140_);
                        v___y_5131_ = v___x_5141_;
                        state = 3;
                        continue;
                    } else {
                        v___y_5131_ = v___x_5139_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_5137_;
                }
            }
            5 => {
                if v___y_5143_ == 0 {
                    v___x_5144_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5145_ = lean_uint8_dec_eq(v___y_5103_, v___x_5144_);
                    if v___x_5145_ == 0 {
                        v___x_5146_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5147_ = lean_uint8_dec_eq(v___y_5103_, v___x_5146_);
                        v___y_5137_ = v___x_5147_;
                        state = 4;
                        continue;
                    } else {
                        v___y_5137_ = v___x_5145_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_5143_;
                }
            }
            6 => {
                if v___y_5149_ == 0 {
                    v___x_5150_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5151_ = lean_uint8_dec_le(v___x_5150_, v___y_5103_);
                    if v___x_5151_ == 0 {
                        v___y_5143_ = v___x_5151_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5152_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5153_ = lean_uint8_dec_le(v___y_5103_, v___x_5152_);
                        v___y_5143_ = v___x_5153_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_5149_;
                }
            }
            7 => {
                if v___y_5155_ == 0 {
                    v___x_5156_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5157_ = lean_uint8_dec_le(v___x_5156_, v___y_5103_);
                    if v___x_5157_ == 0 {
                        v___y_5149_ = v___x_5157_;
                        state = 6;
                        continue;
                    } else {
                        v___x_5158_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5159_ = lean_uint8_dec_le(v___y_5103_, v___x_5158_);
                        v___y_5149_ = v___x_5159_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_5155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed(
    mut v___y_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_20317__boxed_5165_: u8 = 0;
    let mut v_res_5166_: u8 = 0;
    let mut v_r_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_20317__boxed_5165_ = (crate::leanh::lean_unbox(v___y_5164_) as u8);
    v_res_5166_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(v___y_20317__boxed_5165_);
    v_r_5167_ = crate::leanh::lean_box((v_res_5166_) as usize);
    return v_r_5167_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(
    mut v_c_5168_: u8,
) -> u8 {
    let mut v___x_5169_: u8 = 0;
    let mut v___x_5170_: u8 = 0;
    v___x_5169_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
    v___x_5170_ = lean_uint8_dec_eq(v_c_5168_, v___x_5169_);
    if v___x_5170_ == 0 {
        let mut v___x_5171_: u8 = 0;
        let mut v___x_5172_: u8 = 0;
        v___x_5171_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
        v___x_5172_ = lean_uint8_dec_eq(v_c_5168_, v___x_5171_);
        return v___x_5172_;
    } else {
        return v___x_5170_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(
    mut v_c_5173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_5174_: u8 = 0;
    let mut v_res_5175_: u8 = 0;
    let mut v_r_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_5174_ = (crate::leanh::lean_unbox(v_c_5173_) as u8);
    v_res_5175_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_5174_);
    v_r_5176_ = crate::leanh::lean_box((v_res_5175_) as usize);
    return v_r_5176_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5178_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0;
    v___x_5179_ = l_Std_Http_URI_EncodedString_empty(v___f_5178_);
    return v___x_5179_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(
    mut v_config_5187_: *mut crate::leanh::LeanObject,
    mut v_a_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: u8 = 0;
    let mut v___x_5220_: u8 = 0;
    let mut v___y_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: u8 = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxPathSegments_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxTotalPathLength_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: u8 = 0;
    let mut v_array_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5266_: u8 = 0;
    let mut v___x_5267_: u8 = 0;
    let mut v___x_5268_: u8 = 0;
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: u8 = 0;
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: u8 = 0;
    let mut v_reuseFailAlloc_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut v_unused_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_pos_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5334_: u8 = 0;
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5338_: u8 = 0;
    let mut v___x_5339_: u8 = 0;
    let mut v___x_5340_: u8 = 0;
    let mut v___y_5342_: u8 = 0;
    let mut v___x_5343_: u8 = 0;
    let mut v___x_5344_: u8 = 0;
    let mut v___x_5345_: u8 = 0;
    let mut v___x_5346_: u8 = 0;
    let mut v___y_5348_: u8 = 0;
    let mut v___x_5349_: u8 = 0;
    let mut v___x_5350_: u8 = 0;
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: u8 = 0;
    let mut v___x_5354_: u8 = 0;
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: u8 = 0;
    let mut v___x_5358_: u8 = 0;
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: u8 = 0;
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: u8 = 0;
    let mut v___x_5363_: u8 = 0;
    let mut v___x_5364_: u8 = 0;
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: u8 = 0;
    let mut v___y_5368_: u8 = 0;
    let mut v___x_5369_: u8 = 0;
    let mut v___x_5370_: u8 = 0;
    let mut v___x_5371_: u8 = 0;
    let mut v___x_5372_: u8 = 0;
    let mut v___y_5374_: u8 = 0;
    let mut v___x_5375_: u8 = 0;
    let mut v___x_5376_: u8 = 0;
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: u8 = 0;
    let mut v___y_5380_: u8 = 0;
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: u8 = 0;
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5384_: u8 = 0;
    let mut v___y_5386_: u8 = 0;
    let mut v___x_5387_: u8 = 0;
    let mut v___x_5388_: u8 = 0;
    let mut v___x_5389_: u8 = 0;
    let mut v___x_5390_: u8 = 0;
    let mut v___y_5392_: u8 = 0;
    let mut v___x_5393_: u8 = 0;
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: u8 = 0;
    let mut v___x_5396_: u8 = 0;
    let mut v___x_5397_: u8 = 0;
    let mut v___x_5398_: u8 = 0;
    let mut v___x_5399_: u8 = 0;
    let mut v___x_5400_: u8 = 0;
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5202_ = crate::leanh::lean_ctor_get(v___y_5189_, 0);
                v_idx_5203_ = crate::leanh::lean_ctor_get(v___y_5189_, 1);
                v_fst_5204_ = crate::leanh::lean_ctor_get(v_a_5188_, 0);
                v_snd_5205_ = crate::leanh::lean_ctor_get(v_a_5188_, 1);
                v_isSharedCheck_5407_ = (!crate::leanh::lean_is_exclusive(v_a_5188_)) as u8;
                if v_isSharedCheck_5407_ == 0 {
                    v___x_5207_ = v_a_5188_;
                    v_isShared_5208_ = v_isSharedCheck_5407_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5205_);
                    crate::leanh::lean_inc(v_fst_5204_);
                    crate::leanh::lean_dec(v_a_5188_);
                    v___x_5207_ = crate::leanh::lean_box(0);
                    v_isShared_5208_ = v_isSharedCheck_5407_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_5194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5194_, 0, v___y_5193_);
                crate::leanh::lean_ctor_set(v___x_5194_, 1, v___y_5191_);
                v_a_5188_ = v___x_5194_;
                v___y_5189_ = v___y_5192_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5200_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5200_, 0, v___y_5197_);
                crate::leanh::lean_ctor_set(v___x_5200_, 1, v___y_5198_);
                v___x_5201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5201_, 0, v___y_5199_);
                crate::leanh::lean_ctor_set(v___x_5201_, 1, v___x_5200_);
                return v___x_5201_;
            }
            3 => {
                v___x_5209_ = lean_byte_array_size(v_array_5202_);
                v___x_5210_ = lean_nat_dec_lt(v_idx_5203_, v___x_5209_);
                if v___x_5210_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_5187_);
                    if v_isShared_5208_ == 0 {
                        v___x_5212_ = v___x_5207_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_fst_5204_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 1, v_snd_5205_);
                        v___x_5212_ = v_reuseFailAlloc_5214_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v___x_5210_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_5187_);
                        if v_isShared_5208_ == 0 {
                            v___x_5216_ = v___x_5207_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_5218_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_fst_5204_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_snd_5205_);
                            v___x_5216_ = v_reuseFailAlloc_5218_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_5219_ = lean_byte_array_fget(v_array_5202_, v_idx_5203_);
                        v___x_5220_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_5219_);
                        if v___x_5220_ == 0 {
                            v___x_5397_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                            v___x_5398_ = lean_uint8_dec_eq(v___x_5219_, v___x_5397_);
                            if v___x_5398_ == 0 {
                                v___x_5399_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                                v___x_5400_ = lean_uint8_dec_le(v___x_5399_, v___x_5219_);
                                if v___x_5400_ == 0 {
                                    v___y_5392_ = v___x_5400_;
                                    state = 29;
                                    continue;
                                } else {
                                    v___x_5401_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                                    v___x_5402_ = lean_uint8_dec_le(v___x_5219_, v___x_5401_);
                                    v___y_5392_ = v___x_5402_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                v___y_5334_ = v___x_5398_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_config_5187_);
                            if v_isShared_5208_ == 0 {
                                v___x_5404_ = v___x_5207_;
                                state = 30;
                                continue;
                            } else {
                                v_reuseFailAlloc_5406_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_fst_5204_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_snd_5205_);
                                v___x_5404_ = v_reuseFailAlloc_5406_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_5213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5213_, 0, v___y_5189_);
                crate::leanh::lean_ctor_set(v___x_5213_, 1, v___x_5212_);
                return v___x_5213_;
            }
            5 => {
                v___x_5217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5217_, 0, v___y_5189_);
                crate::leanh::lean_ctor_set(v___x_5217_, 1, v___x_5216_);
                return v___x_5217_;
            }
            6 => {
                v___x_5226_ = lean_array_get_size(v___y_5225_);
                v___x_5227_ = lean_nat_dec_le(v___y_5224_, v___x_5226_);
                if v___x_5227_ == 0 {
                    crate::leanh::lean_dec(v___y_5224_);
                    v___x_5228_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
                    v___x_5229_ = lean_array_push(v___y_5225_, v___x_5228_);
                    if v_isShared_5208_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5207_, 1, v___y_5222_);
                        crate::leanh::lean_ctor_set(v___x_5207_, 0, v___x_5229_);
                        v___x_5231_ = v___x_5207_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5229_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 1, v___y_5222_);
                        v___x_5231_ = v_reuseFailAlloc_5233_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5225_);
                    crate::leanh::lean_dec(v___y_5222_);
                    crate::leanh::lean_del_object(v___x_5207_);
                    crate::leanh::lean_dec_ref(v_config_5187_);
                    v___x_5234_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2;
                    v___x_5235_ = l_Nat_reprFast(v___y_5224_);
                    v___x_5236_ = lean_string_append(v___x_5234_, v___x_5235_);
                    crate::leanh::lean_dec_ref(v___x_5235_);
                    v___x_5237_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3;
                    v___x_5238_ = lean_string_append(v___x_5236_, v___x_5237_);
                    v___x_5239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5239_, 0, v___x_5238_);
                    v___x_5240_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5240_, 0, v___y_5223_);
                    crate::leanh::lean_ctor_set(v___x_5240_, 1, v___x_5239_);
                    return v___x_5240_;
                }
            }
            7 => {
                v_a_5188_ = v___x_5231_;
                v___y_5189_ = v___y_5223_;
                state = 0;
                continue;
            }
            8 => {
                v_maxPathSegments_5242_ = crate::leanh::lean_ctor_get(v_config_5187_, 6);
                v_maxTotalPathLength_5243_ = crate::leanh::lean_ctor_get(v_config_5187_, 7);
                v___x_5244_ = lean_array_get_size(v_fst_5204_);
                v___x_5245_ = lean_nat_dec_le(v_maxPathSegments_5242_, v___x_5244_);
                if v___x_5245_ == 0 {
                    v___x_5246_ =
                        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(
                            v_config_5187_,
                            v___y_5189_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5246_) == 0 {
                        v_pos_5247_ = crate::leanh::lean_ctor_get(v___x_5246_, 0);
                        v_res_5248_ = crate::leanh::lean_ctor_get(v___x_5246_, 1);
                        v_isSharedCheck_5316_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5246_)) as u8;
                        if v_isSharedCheck_5316_ == 0 {
                            v___x_5250_ = v___x_5246_;
                            v_isShared_5251_ = v_isSharedCheck_5316_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_5248_);
                            crate::leanh::lean_inc(v_pos_5247_);
                            crate::leanh::lean_dec(v___x_5246_);
                            v___x_5250_ = crate::leanh::lean_box(0);
                            v_isShared_5251_ = v_isSharedCheck_5316_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5207_);
                        crate::leanh::lean_dec(v_snd_5205_);
                        crate::leanh::lean_dec(v_fst_5204_);
                        crate::leanh::lean_dec_ref(v_config_5187_);
                        v_pos_5317_ = crate::leanh::lean_ctor_get(v___x_5246_, 0);
                        v_err_5318_ = crate::leanh::lean_ctor_get(v___x_5246_, 1);
                        v_isSharedCheck_5325_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5246_)) as u8;
                        if v_isSharedCheck_5325_ == 0 {
                            v___x_5320_ = v___x_5246_;
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_5318_);
                            crate::leanh::lean_inc(v_pos_5317_);
                            crate::leanh::lean_dec(v___x_5246_);
                            v___x_5320_ = crate::leanh::lean_box(0);
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_maxPathSegments_5242_);
                    crate::leanh::lean_del_object(v___x_5207_);
                    crate::leanh::lean_dec(v_snd_5205_);
                    crate::leanh::lean_dec(v_fst_5204_);
                    crate::leanh::lean_dec_ref(v_config_5187_);
                    v___x_5326_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2;
                    v___x_5327_ = l_Nat_reprFast(v_maxPathSegments_5242_);
                    v___x_5328_ = lean_string_append(v___x_5326_, v___x_5327_);
                    crate::leanh::lean_dec_ref(v___x_5327_);
                    v___x_5329_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3;
                    v___x_5330_ = lean_string_append(v___x_5328_, v___x_5329_);
                    v___x_5331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5331_, 0, v___x_5330_);
                    v___x_5332_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5332_, 0, v___y_5189_);
                    crate::leanh::lean_ctor_set(v___x_5332_, 1, v___x_5331_);
                    return v___x_5332_;
                }
            }
            9 => {
                crate::leanh::lean_inc(v_res_5248_);
                v___x_5252_ = l_ByteSlice_toByteArray(v_res_5248_);
                v___x_5253_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_5252_);
                if crate::leanh::lean_obj_tag(v___x_5253_) == 1 {
                    v_val_5254_ = crate::leanh::lean_ctor_get(v___x_5253_, 0);
                    v_isSharedCheck_5311_ = (!crate::leanh::lean_is_exclusive(v___x_5253_)) as u8;
                    if v_isSharedCheck_5311_ == 0 {
                        v___x_5256_ = v___x_5253_;
                        v_isShared_5257_ = v_isSharedCheck_5311_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5254_);
                        crate::leanh::lean_dec(v___x_5253_);
                        v___x_5256_ = crate::leanh::lean_box(0);
                        v_isShared_5257_ = v_isSharedCheck_5311_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5253_);
                    crate::leanh::lean_dec(v_res_5248_);
                    crate::leanh::lean_del_object(v___x_5207_);
                    crate::leanh::lean_dec(v_snd_5205_);
                    crate::leanh::lean_dec(v_fst_5204_);
                    crate::leanh::lean_dec_ref(v_config_5187_);
                    v___x_5312_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7;
                    if v_isShared_5251_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5250_, 1);
                        crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5312_);
                        v___x_5314_ = v___x_5250_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5315_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_pos_5247_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 1, v___x_5312_);
                        v___x_5314_ = v_reuseFailAlloc_5315_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v___x_5258_ = l_ByteSlice_size(v_res_5248_);
                crate::leanh::lean_dec(v_res_5248_);
                v___x_5259_ = lean_nat_add(v_snd_5205_, v___x_5258_);
                crate::leanh::lean_dec(v___x_5258_);
                crate::leanh::lean_dec(v_snd_5205_);
                v___x_5260_ = lean_nat_dec_lt(v_maxTotalPathLength_5243_, v___x_5259_);
                if v___x_5260_ == 0 {
                    v_array_5261_ = crate::leanh::lean_ctor_get(v_pos_5247_, 0);
                    v_idx_5262_ = crate::leanh::lean_ctor_get(v_pos_5247_, 1);
                    v___x_5263_ = lean_array_push(v_fst_5204_, v_val_5254_);
                    v___x_5264_ = lean_byte_array_size(v_array_5261_);
                    v___x_5265_ = lean_nat_dec_lt(v_idx_5262_, v___x_5264_);
                    if v___x_5265_ == 0 {
                        crate::leanh::lean_del_object(v___x_5256_);
                        crate::leanh::lean_del_object(v___x_5250_);
                        crate::leanh::lean_del_object(v___x_5207_);
                        crate::leanh::lean_dec_ref(v_config_5187_);
                        v___y_5197_ = v___x_5263_;
                        v___y_5198_ = v___x_5259_;
                        v___y_5199_ = v_pos_5247_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5266_ = lean_byte_array_fget(v_array_5261_, v_idx_5262_);
                        v___x_5267_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                        v___x_5268_ = lean_uint8_dec_eq(v___x_5266_, v___x_5267_);
                        if v___x_5268_ == 0 {
                            crate::leanh::lean_del_object(v___x_5256_);
                            crate::leanh::lean_del_object(v___x_5250_);
                            crate::leanh::lean_del_object(v___x_5207_);
                            crate::leanh::lean_dec_ref(v_config_5187_);
                            v___y_5197_ = v___x_5263_;
                            v___y_5198_ = v___x_5259_;
                            v___y_5199_ = v_pos_5247_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5269_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5270_ = lean_nat_add(v___x_5259_, v___x_5269_);
                            crate::leanh::lean_dec(v___x_5259_);
                            v___x_5271_ = lean_nat_dec_lt(v_maxTotalPathLength_5243_, v___x_5270_);
                            if v___x_5271_ == 0 {
                                crate::leanh::lean_del_object(v___x_5256_);
                                if v___x_5265_ == 0 {
                                    crate::leanh::lean_dec(v___x_5270_);
                                    crate::leanh::lean_dec_ref(v___x_5263_);
                                    crate::leanh::lean_del_object(v___x_5207_);
                                    crate::leanh::lean_dec_ref(v_config_5187_);
                                    v___x_5272_ = crate::leanh::lean_box(0);
                                    if v_isShared_5251_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_5250_, 1);
                                        crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5272_);
                                        v___x_5274_ = v___x_5250_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5275_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5275_,
                                            0,
                                            v_pos_5247_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5275_,
                                            1,
                                            v___x_5272_,
                                        );
                                        v___x_5274_ = v_reuseFailAlloc_5275_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_idx_5262_);
                                    crate::leanh::lean_inc_ref(v_array_5261_);
                                    crate::leanh::lean_del_object(v___x_5250_);
                                    v_isSharedCheck_5286_ =
                                        (!crate::leanh::lean_is_exclusive(v_pos_5247_)) as u8;
                                    if v_isSharedCheck_5286_ == 0 {
                                        v_unused_5287_ =
                                            crate::leanh::lean_ctor_get(v_pos_5247_, 1);
                                        crate::leanh::lean_dec(v_unused_5287_);
                                        v_unused_5288_ =
                                            crate::leanh::lean_ctor_get(v_pos_5247_, 0);
                                        crate::leanh::lean_dec(v_unused_5288_);
                                        v___x_5277_ = v_pos_5247_;
                                        v_isShared_5278_ = v_isSharedCheck_5286_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pos_5247_);
                                        v___x_5277_ = crate::leanh::lean_box(0);
                                        v_isShared_5278_ = v_isSharedCheck_5286_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc(v_maxTotalPathLength_5243_);
                                crate::leanh::lean_dec(v___x_5270_);
                                crate::leanh::lean_dec_ref(v___x_5263_);
                                crate::leanh::lean_del_object(v___x_5207_);
                                crate::leanh::lean_dec_ref(v_config_5187_);
                                v___x_5289_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4;
                                v___x_5290_ = l_Nat_reprFast(v_maxTotalPathLength_5243_);
                                v___x_5291_ = lean_string_append(v___x_5289_, v___x_5290_);
                                crate::leanh::lean_dec_ref(v___x_5290_);
                                v___x_5292_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5;
                                v___x_5293_ = lean_string_append(v___x_5291_, v___x_5292_);
                                if v_isShared_5257_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_5256_, 0, v___x_5293_);
                                    v___x_5295_ = v___x_5256_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5299_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5299_,
                                        0,
                                        v___x_5293_,
                                    );
                                    v___x_5295_ = v_reuseFailAlloc_5299_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_maxTotalPathLength_5243_);
                    crate::leanh::lean_dec(v___x_5259_);
                    crate::leanh::lean_dec(v_val_5254_);
                    crate::leanh::lean_del_object(v___x_5207_);
                    crate::leanh::lean_dec(v_fst_5204_);
                    crate::leanh::lean_dec_ref(v_config_5187_);
                    v___x_5300_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4;
                    v___x_5301_ = l_Nat_reprFast(v_maxTotalPathLength_5243_);
                    v___x_5302_ = lean_string_append(v___x_5300_, v___x_5301_);
                    crate::leanh::lean_dec_ref(v___x_5301_);
                    v___x_5303_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5;
                    v___x_5304_ = lean_string_append(v___x_5302_, v___x_5303_);
                    if v_isShared_5257_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5256_, 0, v___x_5304_);
                        v___x_5306_ = v___x_5256_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5304_);
                        v___x_5306_ = v_reuseFailAlloc_5310_;
                        state = 16;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_5274_;
            }
            12 => {
                v___x_5279_ = lean_nat_add(v_idx_5262_, v___x_5269_);
                crate::leanh::lean_dec(v_idx_5262_);
                crate::leanh::lean_inc(v___x_5279_);
                crate::leanh::lean_inc_ref(v_array_5261_);
                if v_isShared_5278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5277_, 1, v___x_5279_);
                    v___x_5281_ = v___x_5277_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_array_5261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 1, v___x_5279_);
                    v___x_5281_ = v_reuseFailAlloc_5285_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5282_ = lean_nat_dec_lt(v___x_5279_, v___x_5264_);
                if v___x_5282_ == 0 {
                    crate::leanh::lean_dec(v___x_5279_);
                    crate::leanh::lean_dec_ref(v_array_5261_);
                    if v___x_5265_ == 0 {
                        crate::leanh::lean_del_object(v___x_5207_);
                        v___y_5191_ = v___x_5270_;
                        v___y_5192_ = v___x_5281_;
                        v___y_5193_ = v___x_5263_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxPathSegments_5242_);
                        v___y_5222_ = v___x_5270_;
                        v___y_5223_ = v___x_5281_;
                        v___y_5224_ = v_maxPathSegments_5242_;
                        v___y_5225_ = v___x_5263_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_5283_ = lean_byte_array_fget(v_array_5261_, v___x_5279_);
                    crate::leanh::lean_dec(v___x_5279_);
                    crate::leanh::lean_dec_ref(v_array_5261_);
                    v___x_5284_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_5283_);
                    if v___x_5284_ == 0 {
                        crate::leanh::lean_del_object(v___x_5207_);
                        v___y_5191_ = v___x_5270_;
                        v___y_5192_ = v___x_5281_;
                        v___y_5193_ = v___x_5263_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxPathSegments_5242_);
                        v___y_5222_ = v___x_5270_;
                        v___y_5223_ = v___x_5281_;
                        v___y_5224_ = v_maxPathSegments_5242_;
                        v___y_5225_ = v___x_5263_;
                        state = 6;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5250_, 1);
                    crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5295_);
                    v___x_5297_ = v___x_5250_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_pos_5247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 1, v___x_5295_);
                    v___x_5297_ = v_reuseFailAlloc_5298_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5297_;
            }
            16 => {
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5250_, 1);
                    crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5306_);
                    v___x_5308_ = v___x_5250_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_pos_5247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 1, v___x_5306_);
                    v___x_5308_ = v_reuseFailAlloc_5309_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5308_;
            }
            18 => {
                return v___x_5314_;
            }
            19 => {
                if v_isShared_5321_ == 0 {
                    v___x_5323_ = v___x_5320_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_pos_5317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 1, v_err_5318_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5323_;
            }
            21 => {
                if v___y_5334_ == 0 {
                    if v___x_5210_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5207_);
                        crate::leanh::lean_dec_ref(v_config_5187_);
                        v___x_5335_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5335_, 0, v_fst_5204_);
                        crate::leanh::lean_ctor_set(v___x_5335_, 1, v_snd_5205_);
                        v___x_5336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5336_, 0, v___y_5189_);
                        crate::leanh::lean_ctor_set(v___x_5336_, 1, v___x_5335_);
                        return v___x_5336_;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            22 => {
                if v___y_5338_ == 0 {
                    v___x_5339_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                    v___x_5340_ = lean_uint8_dec_eq(v___x_5219_, v___x_5339_);
                    if v___x_5340_ == 0 {
                        v___y_5334_ = v___x_5340_;
                        state = 21;
                        continue;
                    } else {
                        v___y_5334_ = v___x_5210_;
                        state = 21;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            23 => {
                if v___y_5342_ == 0 {
                    v___x_5343_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5344_ = lean_uint8_dec_eq(v___x_5219_, v___x_5343_);
                    if v___x_5344_ == 0 {
                        v___x_5345_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5346_ = lean_uint8_dec_eq(v___x_5219_, v___x_5345_);
                        v___y_5338_ = v___x_5346_;
                        state = 22;
                        continue;
                    } else {
                        v___y_5338_ = v___x_5344_;
                        state = 22;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            24 => {
                if v___y_5348_ == 0 {
                    v___x_5349_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5350_ = lean_uint8_dec_eq(v___x_5219_, v___x_5349_);
                    if v___x_5350_ == 0 {
                        v___x_5351_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5352_ = lean_uint8_dec_eq(v___x_5219_, v___x_5351_);
                        if v___x_5352_ == 0 {
                            v___x_5353_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5354_ = lean_uint8_dec_eq(v___x_5219_, v___x_5353_);
                            if v___x_5354_ == 0 {
                                v___x_5355_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5356_ = lean_uint8_dec_eq(v___x_5219_, v___x_5355_);
                                if v___x_5356_ == 0 {
                                    v___x_5357_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5358_ = lean_uint8_dec_eq(v___x_5219_, v___x_5357_);
                                    if v___x_5358_ == 0 {
                                        v___x_5359_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5360_ = lean_uint8_dec_eq(v___x_5219_, v___x_5359_);
                                        if v___x_5360_ == 0 {
                                            v___x_5361_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5362_ =
                                                lean_uint8_dec_eq(v___x_5219_, v___x_5361_);
                                            if v___x_5362_ == 0 {
                                                v___x_5363_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5364_ =
                                                    lean_uint8_dec_eq(v___x_5219_, v___x_5363_);
                                                if v___x_5364_ == 0 {
                                                    v___x_5365_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5366_ =
                                                        lean_uint8_dec_eq(v___x_5219_, v___x_5365_);
                                                    v___y_5342_ = v___x_5366_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    v___y_5342_ = v___x_5364_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5342_ = v___x_5362_;
                                                state = 23;
                                                continue;
                                            }
                                        } else {
                                            v___y_5342_ = v___x_5360_;
                                            state = 23;
                                            continue;
                                        }
                                    } else {
                                        v___y_5342_ = v___x_5358_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    v___y_5342_ = v___x_5356_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v___y_5342_ = v___x_5354_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v___y_5342_ = v___x_5352_;
                            state = 23;
                            continue;
                        }
                    } else {
                        v___y_5342_ = v___x_5350_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            25 => {
                if v___y_5368_ == 0 {
                    v___x_5369_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5370_ = lean_uint8_dec_eq(v___x_5219_, v___x_5369_);
                    if v___x_5370_ == 0 {
                        v___x_5371_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5372_ = lean_uint8_dec_eq(v___x_5219_, v___x_5371_);
                        v___y_5348_ = v___x_5372_;
                        state = 24;
                        continue;
                    } else {
                        v___y_5348_ = v___x_5370_;
                        state = 24;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            26 => {
                if v___y_5374_ == 0 {
                    v___x_5375_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5376_ = lean_uint8_dec_eq(v___x_5219_, v___x_5375_);
                    if v___x_5376_ == 0 {
                        v___x_5377_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5378_ = lean_uint8_dec_eq(v___x_5219_, v___x_5377_);
                        v___y_5368_ = v___x_5378_;
                        state = 25;
                        continue;
                    } else {
                        v___y_5368_ = v___x_5376_;
                        state = 25;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            27 => {
                if v___y_5380_ == 0 {
                    v___x_5381_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5382_ = lean_uint8_dec_eq(v___x_5219_, v___x_5381_);
                    if v___x_5382_ == 0 {
                        v___x_5383_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5384_ = lean_uint8_dec_eq(v___x_5219_, v___x_5383_);
                        v___y_5374_ = v___x_5384_;
                        state = 26;
                        continue;
                    } else {
                        v___y_5374_ = v___x_5382_;
                        state = 26;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            28 => {
                if v___y_5386_ == 0 {
                    v___x_5387_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5388_ = lean_uint8_dec_le(v___x_5387_, v___x_5219_);
                    if v___x_5388_ == 0 {
                        v___y_5380_ = v___x_5388_;
                        state = 27;
                        continue;
                    } else {
                        v___x_5389_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5390_ = lean_uint8_dec_le(v___x_5219_, v___x_5389_);
                        v___y_5380_ = v___x_5390_;
                        state = 27;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            29 => {
                if v___y_5392_ == 0 {
                    v___x_5393_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5394_ = lean_uint8_dec_le(v___x_5393_, v___x_5219_);
                    if v___x_5394_ == 0 {
                        v___y_5386_ = v___x_5394_;
                        state = 28;
                        continue;
                    } else {
                        v___x_5395_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5396_ = lean_uint8_dec_le(v___x_5219_, v___x_5395_);
                        v___y_5386_ = v___x_5396_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___y_5334_ = v___x_5210_;
                    state = 21;
                    continue;
                }
            }
            30 => {
                v___x_5405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5405_, 0, v___y_5189_);
                crate::leanh::lean_ctor_set(v___x_5405_, 1, v___x_5404_);
                return v___x_5405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(
    mut v_config_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5429_: u8 = 0;
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: u8 = 0;
    let mut v___y_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: u8 = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxPathSegments_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxTotalPathLength_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5478_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: u8 = 0;
    let mut v_array_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: u8 = 0;
    let mut v___x_5487_: u8 = 0;
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5489_: u8 = 0;
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: u8 = 0;
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: u8 = 0;
    let mut v_reuseFailAlloc_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5507_: u8 = 0;
    let mut v_unused_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5532_: u8 = 0;
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut v_pos_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5542_: u8 = 0;
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5546_: u8 = 0;
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5555_: u8 = 0;
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5559_: u8 = 0;
    let mut v___x_5560_: u8 = 0;
    let mut v___x_5561_: u8 = 0;
    let mut v___y_5563_: u8 = 0;
    let mut v___x_5564_: u8 = 0;
    let mut v___x_5565_: u8 = 0;
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5567_: u8 = 0;
    let mut v___y_5569_: u8 = 0;
    let mut v___x_5570_: u8 = 0;
    let mut v___x_5571_: u8 = 0;
    let mut v___x_5572_: u8 = 0;
    let mut v___x_5573_: u8 = 0;
    let mut v___x_5574_: u8 = 0;
    let mut v___x_5575_: u8 = 0;
    let mut v___x_5576_: u8 = 0;
    let mut v___x_5577_: u8 = 0;
    let mut v___x_5578_: u8 = 0;
    let mut v___x_5579_: u8 = 0;
    let mut v___x_5580_: u8 = 0;
    let mut v___x_5581_: u8 = 0;
    let mut v___x_5582_: u8 = 0;
    let mut v___x_5583_: u8 = 0;
    let mut v___x_5584_: u8 = 0;
    let mut v___x_5585_: u8 = 0;
    let mut v___x_5586_: u8 = 0;
    let mut v___x_5587_: u8 = 0;
    let mut v___y_5589_: u8 = 0;
    let mut v___x_5590_: u8 = 0;
    let mut v___x_5591_: u8 = 0;
    let mut v___x_5592_: u8 = 0;
    let mut v___x_5593_: u8 = 0;
    let mut v___y_5595_: u8 = 0;
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: u8 = 0;
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: u8 = 0;
    let mut v___y_5601_: u8 = 0;
    let mut v___x_5602_: u8 = 0;
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: u8 = 0;
    let mut v___x_5605_: u8 = 0;
    let mut v___y_5607_: u8 = 0;
    let mut v___x_5608_: u8 = 0;
    let mut v___x_5609_: u8 = 0;
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: u8 = 0;
    let mut v___y_5613_: u8 = 0;
    let mut v___x_5614_: u8 = 0;
    let mut v___x_5615_: u8 = 0;
    let mut v___x_5616_: u8 = 0;
    let mut v___x_5617_: u8 = 0;
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: u8 = 0;
    let mut v___x_5620_: u8 = 0;
    let mut v___x_5621_: u8 = 0;
    let mut v___x_5622_: u8 = 0;
    let mut v___x_5623_: u8 = 0;
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5423_ = crate::leanh::lean_ctor_get(v___y_5410_, 0);
                v_idx_5424_ = crate::leanh::lean_ctor_get(v___y_5410_, 1);
                v_fst_5425_ = crate::leanh::lean_ctor_get(v_a_5409_, 0);
                v_snd_5426_ = crate::leanh::lean_ctor_get(v_a_5409_, 1);
                v_isSharedCheck_5628_ = (!crate::leanh::lean_is_exclusive(v_a_5409_)) as u8;
                if v_isSharedCheck_5628_ == 0 {
                    v___x_5428_ = v_a_5409_;
                    v_isShared_5429_ = v_isSharedCheck_5628_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5426_);
                    crate::leanh::lean_inc(v_fst_5425_);
                    crate::leanh::lean_dec(v_a_5409_);
                    v___x_5428_ = crate::leanh::lean_box(0);
                    v_isShared_5429_ = v_isSharedCheck_5628_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_5415_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5415_, 0, v___y_5414_);
                crate::leanh::lean_ctor_set(v___x_5415_, 1, v___y_5413_);
                v___x_5416_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_5408_, v___x_5415_, v___y_5412_);
                return v___x_5416_;
            }
            2 => {
                v___x_5421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5421_, 0, v___y_5420_);
                crate::leanh::lean_ctor_set(v___x_5421_, 1, v___y_5419_);
                v___x_5422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5422_, 0, v___y_5418_);
                crate::leanh::lean_ctor_set(v___x_5422_, 1, v___x_5421_);
                return v___x_5422_;
            }
            3 => {
                v___x_5430_ = lean_byte_array_size(v_array_5423_);
                v___x_5431_ = lean_nat_dec_lt(v_idx_5424_, v___x_5430_);
                if v___x_5431_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_5408_);
                    if v_isShared_5429_ == 0 {
                        v___x_5433_ = v___x_5428_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_fst_5425_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_snd_5426_);
                        v___x_5433_ = v_reuseFailAlloc_5435_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v___x_5431_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_5408_);
                        if v_isShared_5429_ == 0 {
                            v___x_5437_ = v___x_5428_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_5439_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_fst_5425_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_snd_5426_);
                            v___x_5437_ = v_reuseFailAlloc_5439_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_5440_ = lean_byte_array_fget(v_array_5423_, v_idx_5424_);
                        v___x_5441_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_5440_);
                        if v___x_5441_ == 0 {
                            v___x_5618_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                            v___x_5619_ = lean_uint8_dec_eq(v___x_5440_, v___x_5618_);
                            if v___x_5619_ == 0 {
                                v___x_5620_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                                v___x_5621_ = lean_uint8_dec_le(v___x_5620_, v___x_5440_);
                                if v___x_5621_ == 0 {
                                    v___y_5613_ = v___x_5621_;
                                    state = 29;
                                    continue;
                                } else {
                                    v___x_5622_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                                    v___x_5623_ = lean_uint8_dec_le(v___x_5440_, v___x_5622_);
                                    v___y_5613_ = v___x_5623_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                v___y_5555_ = v___x_5619_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_config_5408_);
                            if v_isShared_5429_ == 0 {
                                v___x_5625_ = v___x_5428_;
                                state = 30;
                                continue;
                            } else {
                                v_reuseFailAlloc_5627_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_fst_5425_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 1, v_snd_5426_);
                                v___x_5625_ = v_reuseFailAlloc_5627_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_5434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5434_, 0, v___y_5410_);
                crate::leanh::lean_ctor_set(v___x_5434_, 1, v___x_5433_);
                return v___x_5434_;
            }
            5 => {
                v___x_5438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5438_, 0, v___y_5410_);
                crate::leanh::lean_ctor_set(v___x_5438_, 1, v___x_5437_);
                return v___x_5438_;
            }
            6 => {
                v___x_5447_ = lean_array_get_size(v___y_5446_);
                v___x_5448_ = lean_nat_dec_le(v___y_5444_, v___x_5447_);
                if v___x_5448_ == 0 {
                    crate::leanh::lean_dec(v___y_5444_);
                    v___x_5449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
                    v___x_5450_ = lean_array_push(v___y_5446_, v___x_5449_);
                    if v_isShared_5429_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5428_, 1, v___y_5445_);
                        crate::leanh::lean_ctor_set(v___x_5428_, 0, v___x_5450_);
                        v___x_5452_ = v___x_5428_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5450_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5454_, 1, v___y_5445_);
                        v___x_5452_ = v_reuseFailAlloc_5454_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5446_);
                    crate::leanh::lean_dec(v___y_5445_);
                    crate::leanh::lean_del_object(v___x_5428_);
                    crate::leanh::lean_dec_ref(v_config_5408_);
                    v___x_5455_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2;
                    v___x_5456_ = l_Nat_reprFast(v___y_5444_);
                    v___x_5457_ = lean_string_append(v___x_5455_, v___x_5456_);
                    crate::leanh::lean_dec_ref(v___x_5456_);
                    v___x_5458_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3;
                    v___x_5459_ = lean_string_append(v___x_5457_, v___x_5458_);
                    v___x_5460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5460_, 0, v___x_5459_);
                    v___x_5461_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5461_, 0, v___y_5443_);
                    crate::leanh::lean_ctor_set(v___x_5461_, 1, v___x_5460_);
                    return v___x_5461_;
                }
            }
            7 => {
                v___x_5453_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_5408_, v___x_5452_, v___y_5443_);
                return v___x_5453_;
            }
            8 => {
                v_maxPathSegments_5463_ = crate::leanh::lean_ctor_get(v_config_5408_, 6);
                v_maxTotalPathLength_5464_ = crate::leanh::lean_ctor_get(v_config_5408_, 7);
                v___x_5465_ = lean_array_get_size(v_fst_5425_);
                v___x_5466_ = lean_nat_dec_le(v_maxPathSegments_5463_, v___x_5465_);
                if v___x_5466_ == 0 {
                    v___x_5467_ =
                        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(
                            v_config_5408_,
                            v___y_5410_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5467_) == 0 {
                        v_pos_5468_ = crate::leanh::lean_ctor_get(v___x_5467_, 0);
                        v_res_5469_ = crate::leanh::lean_ctor_get(v___x_5467_, 1);
                        v_isSharedCheck_5537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5467_)) as u8;
                        if v_isSharedCheck_5537_ == 0 {
                            v___x_5471_ = v___x_5467_;
                            v_isShared_5472_ = v_isSharedCheck_5537_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_5469_);
                            crate::leanh::lean_inc(v_pos_5468_);
                            crate::leanh::lean_dec(v___x_5467_);
                            v___x_5471_ = crate::leanh::lean_box(0);
                            v_isShared_5472_ = v_isSharedCheck_5537_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5428_);
                        crate::leanh::lean_dec(v_snd_5426_);
                        crate::leanh::lean_dec(v_fst_5425_);
                        crate::leanh::lean_dec_ref(v_config_5408_);
                        v_pos_5538_ = crate::leanh::lean_ctor_get(v___x_5467_, 0);
                        v_err_5539_ = crate::leanh::lean_ctor_get(v___x_5467_, 1);
                        v_isSharedCheck_5546_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5467_)) as u8;
                        if v_isSharedCheck_5546_ == 0 {
                            v___x_5541_ = v___x_5467_;
                            v_isShared_5542_ = v_isSharedCheck_5546_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_5539_);
                            crate::leanh::lean_inc(v_pos_5538_);
                            crate::leanh::lean_dec(v___x_5467_);
                            v___x_5541_ = crate::leanh::lean_box(0);
                            v_isShared_5542_ = v_isSharedCheck_5546_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_maxPathSegments_5463_);
                    crate::leanh::lean_del_object(v___x_5428_);
                    crate::leanh::lean_dec(v_snd_5426_);
                    crate::leanh::lean_dec(v_fst_5425_);
                    crate::leanh::lean_dec_ref(v_config_5408_);
                    v___x_5547_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2;
                    v___x_5548_ = l_Nat_reprFast(v_maxPathSegments_5463_);
                    v___x_5549_ = lean_string_append(v___x_5547_, v___x_5548_);
                    crate::leanh::lean_dec_ref(v___x_5548_);
                    v___x_5550_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3;
                    v___x_5551_ = lean_string_append(v___x_5549_, v___x_5550_);
                    v___x_5552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5552_, 0, v___x_5551_);
                    v___x_5553_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5553_, 0, v___y_5410_);
                    crate::leanh::lean_ctor_set(v___x_5553_, 1, v___x_5552_);
                    return v___x_5553_;
                }
            }
            9 => {
                crate::leanh::lean_inc(v_res_5469_);
                v___x_5473_ = l_ByteSlice_toByteArray(v_res_5469_);
                v___x_5474_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_5473_);
                if crate::leanh::lean_obj_tag(v___x_5474_) == 1 {
                    v_val_5475_ = crate::leanh::lean_ctor_get(v___x_5474_, 0);
                    v_isSharedCheck_5532_ = (!crate::leanh::lean_is_exclusive(v___x_5474_)) as u8;
                    if v_isSharedCheck_5532_ == 0 {
                        v___x_5477_ = v___x_5474_;
                        v_isShared_5478_ = v_isSharedCheck_5532_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5475_);
                        crate::leanh::lean_dec(v___x_5474_);
                        v___x_5477_ = crate::leanh::lean_box(0);
                        v_isShared_5478_ = v_isSharedCheck_5532_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5474_);
                    crate::leanh::lean_dec(v_res_5469_);
                    crate::leanh::lean_del_object(v___x_5428_);
                    crate::leanh::lean_dec(v_snd_5426_);
                    crate::leanh::lean_dec(v_fst_5425_);
                    crate::leanh::lean_dec_ref(v_config_5408_);
                    v___x_5533_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7;
                    if v_isShared_5472_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5471_, 1);
                        crate::leanh::lean_ctor_set(v___x_5471_, 1, v___x_5533_);
                        v___x_5535_ = v___x_5471_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5536_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_pos_5468_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 1, v___x_5533_);
                        v___x_5535_ = v_reuseFailAlloc_5536_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v___x_5479_ = l_ByteSlice_size(v_res_5469_);
                crate::leanh::lean_dec(v_res_5469_);
                v___x_5480_ = lean_nat_add(v_snd_5426_, v___x_5479_);
                crate::leanh::lean_dec(v___x_5479_);
                crate::leanh::lean_dec(v_snd_5426_);
                v___x_5481_ = lean_nat_dec_lt(v_maxTotalPathLength_5464_, v___x_5480_);
                if v___x_5481_ == 0 {
                    v_array_5482_ = crate::leanh::lean_ctor_get(v_pos_5468_, 0);
                    v_idx_5483_ = crate::leanh::lean_ctor_get(v_pos_5468_, 1);
                    v___x_5484_ = lean_array_push(v_fst_5425_, v_val_5475_);
                    v___x_5485_ = lean_byte_array_size(v_array_5482_);
                    v___x_5486_ = lean_nat_dec_lt(v_idx_5483_, v___x_5485_);
                    if v___x_5486_ == 0 {
                        crate::leanh::lean_del_object(v___x_5477_);
                        crate::leanh::lean_del_object(v___x_5471_);
                        crate::leanh::lean_del_object(v___x_5428_);
                        crate::leanh::lean_dec_ref(v_config_5408_);
                        v___y_5418_ = v_pos_5468_;
                        v___y_5419_ = v___x_5480_;
                        v___y_5420_ = v___x_5484_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5487_ = lean_byte_array_fget(v_array_5482_, v_idx_5483_);
                        v___x_5488_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                        v___x_5489_ = lean_uint8_dec_eq(v___x_5487_, v___x_5488_);
                        if v___x_5489_ == 0 {
                            crate::leanh::lean_del_object(v___x_5477_);
                            crate::leanh::lean_del_object(v___x_5471_);
                            crate::leanh::lean_del_object(v___x_5428_);
                            crate::leanh::lean_dec_ref(v_config_5408_);
                            v___y_5418_ = v_pos_5468_;
                            v___y_5419_ = v___x_5480_;
                            v___y_5420_ = v___x_5484_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5490_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5491_ = lean_nat_add(v___x_5480_, v___x_5490_);
                            crate::leanh::lean_dec(v___x_5480_);
                            v___x_5492_ = lean_nat_dec_lt(v_maxTotalPathLength_5464_, v___x_5491_);
                            if v___x_5492_ == 0 {
                                crate::leanh::lean_del_object(v___x_5477_);
                                if v___x_5486_ == 0 {
                                    crate::leanh::lean_dec(v___x_5491_);
                                    crate::leanh::lean_dec_ref(v___x_5484_);
                                    crate::leanh::lean_del_object(v___x_5428_);
                                    crate::leanh::lean_dec_ref(v_config_5408_);
                                    v___x_5493_ = crate::leanh::lean_box(0);
                                    if v_isShared_5472_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_5471_, 1);
                                        crate::leanh::lean_ctor_set(v___x_5471_, 1, v___x_5493_);
                                        v___x_5495_ = v___x_5471_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5496_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5496_,
                                            0,
                                            v_pos_5468_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5496_,
                                            1,
                                            v___x_5493_,
                                        );
                                        v___x_5495_ = v_reuseFailAlloc_5496_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_idx_5483_);
                                    crate::leanh::lean_inc_ref(v_array_5482_);
                                    crate::leanh::lean_del_object(v___x_5471_);
                                    v_isSharedCheck_5507_ =
                                        (!crate::leanh::lean_is_exclusive(v_pos_5468_)) as u8;
                                    if v_isSharedCheck_5507_ == 0 {
                                        v_unused_5508_ =
                                            crate::leanh::lean_ctor_get(v_pos_5468_, 1);
                                        crate::leanh::lean_dec(v_unused_5508_);
                                        v_unused_5509_ =
                                            crate::leanh::lean_ctor_get(v_pos_5468_, 0);
                                        crate::leanh::lean_dec(v_unused_5509_);
                                        v___x_5498_ = v_pos_5468_;
                                        v_isShared_5499_ = v_isSharedCheck_5507_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pos_5468_);
                                        v___x_5498_ = crate::leanh::lean_box(0);
                                        v_isShared_5499_ = v_isSharedCheck_5507_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc(v_maxTotalPathLength_5464_);
                                crate::leanh::lean_dec(v___x_5491_);
                                crate::leanh::lean_dec_ref(v___x_5484_);
                                crate::leanh::lean_del_object(v___x_5428_);
                                crate::leanh::lean_dec_ref(v_config_5408_);
                                v___x_5510_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4;
                                v___x_5511_ = l_Nat_reprFast(v_maxTotalPathLength_5464_);
                                v___x_5512_ = lean_string_append(v___x_5510_, v___x_5511_);
                                crate::leanh::lean_dec_ref(v___x_5511_);
                                v___x_5513_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5;
                                v___x_5514_ = lean_string_append(v___x_5512_, v___x_5513_);
                                if v_isShared_5478_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_5477_, 0, v___x_5514_);
                                    v___x_5516_ = v___x_5477_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5520_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5520_,
                                        0,
                                        v___x_5514_,
                                    );
                                    v___x_5516_ = v_reuseFailAlloc_5520_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_maxTotalPathLength_5464_);
                    crate::leanh::lean_dec(v___x_5480_);
                    crate::leanh::lean_dec(v_val_5475_);
                    crate::leanh::lean_del_object(v___x_5428_);
                    crate::leanh::lean_dec(v_fst_5425_);
                    crate::leanh::lean_dec_ref(v_config_5408_);
                    v___x_5521_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4;
                    v___x_5522_ = l_Nat_reprFast(v_maxTotalPathLength_5464_);
                    v___x_5523_ = lean_string_append(v___x_5521_, v___x_5522_);
                    crate::leanh::lean_dec_ref(v___x_5522_);
                    v___x_5524_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5;
                    v___x_5525_ = lean_string_append(v___x_5523_, v___x_5524_);
                    if v_isShared_5478_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5477_, 0, v___x_5525_);
                        v___x_5527_ = v___x_5477_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5525_);
                        v___x_5527_ = v_reuseFailAlloc_5531_;
                        state = 16;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_5495_;
            }
            12 => {
                v___x_5500_ = lean_nat_add(v_idx_5483_, v___x_5490_);
                crate::leanh::lean_dec(v_idx_5483_);
                crate::leanh::lean_inc(v___x_5500_);
                crate::leanh::lean_inc_ref(v_array_5482_);
                if v_isShared_5499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5498_, 1, v___x_5500_);
                    v___x_5502_ = v___x_5498_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_array_5482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5506_, 1, v___x_5500_);
                    v___x_5502_ = v_reuseFailAlloc_5506_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5503_ = lean_nat_dec_lt(v___x_5500_, v___x_5485_);
                if v___x_5503_ == 0 {
                    crate::leanh::lean_dec(v___x_5500_);
                    crate::leanh::lean_dec_ref(v_array_5482_);
                    if v___x_5486_ == 0 {
                        crate::leanh::lean_del_object(v___x_5428_);
                        v___y_5412_ = v___x_5502_;
                        v___y_5413_ = v___x_5491_;
                        v___y_5414_ = v___x_5484_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxPathSegments_5463_);
                        v___y_5443_ = v___x_5502_;
                        v___y_5444_ = v_maxPathSegments_5463_;
                        v___y_5445_ = v___x_5491_;
                        v___y_5446_ = v___x_5484_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_5504_ = lean_byte_array_fget(v_array_5482_, v___x_5500_);
                    crate::leanh::lean_dec(v___x_5500_);
                    crate::leanh::lean_dec_ref(v_array_5482_);
                    v___x_5505_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_5504_);
                    if v___x_5505_ == 0 {
                        crate::leanh::lean_del_object(v___x_5428_);
                        v___y_5412_ = v___x_5502_;
                        v___y_5413_ = v___x_5491_;
                        v___y_5414_ = v___x_5484_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxPathSegments_5463_);
                        v___y_5443_ = v___x_5502_;
                        v___y_5444_ = v_maxPathSegments_5463_;
                        v___y_5445_ = v___x_5491_;
                        v___y_5446_ = v___x_5484_;
                        state = 6;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_5472_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5471_, 1);
                    crate::leanh::lean_ctor_set(v___x_5471_, 1, v___x_5516_);
                    v___x_5518_ = v___x_5471_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_pos_5468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5516_);
                    v___x_5518_ = v_reuseFailAlloc_5519_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5518_;
            }
            16 => {
                if v_isShared_5472_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5471_, 1);
                    crate::leanh::lean_ctor_set(v___x_5471_, 1, v___x_5527_);
                    v___x_5529_ = v___x_5471_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_pos_5468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 1, v___x_5527_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5529_;
            }
            18 => {
                return v___x_5535_;
            }
            19 => {
                if v_isShared_5542_ == 0 {
                    v___x_5544_ = v___x_5541_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5545_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_pos_5538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5545_, 1, v_err_5539_);
                    v___x_5544_ = v_reuseFailAlloc_5545_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5544_;
            }
            21 => {
                if v___y_5555_ == 0 {
                    if v___x_5431_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5428_);
                        crate::leanh::lean_dec_ref(v_config_5408_);
                        v___x_5556_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5556_, 0, v_fst_5425_);
                        crate::leanh::lean_ctor_set(v___x_5556_, 1, v_snd_5426_);
                        v___x_5557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5557_, 0, v___y_5410_);
                        crate::leanh::lean_ctor_set(v___x_5557_, 1, v___x_5556_);
                        return v___x_5557_;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            22 => {
                if v___y_5559_ == 0 {
                    v___x_5560_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                    v___x_5561_ = lean_uint8_dec_eq(v___x_5440_, v___x_5560_);
                    if v___x_5561_ == 0 {
                        v___y_5555_ = v___x_5561_;
                        state = 21;
                        continue;
                    } else {
                        v___y_5555_ = v___x_5431_;
                        state = 21;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            23 => {
                if v___y_5563_ == 0 {
                    v___x_5564_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5565_ = lean_uint8_dec_eq(v___x_5440_, v___x_5564_);
                    if v___x_5565_ == 0 {
                        v___x_5566_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5567_ = lean_uint8_dec_eq(v___x_5440_, v___x_5566_);
                        v___y_5559_ = v___x_5567_;
                        state = 22;
                        continue;
                    } else {
                        v___y_5559_ = v___x_5565_;
                        state = 22;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            24 => {
                if v___y_5569_ == 0 {
                    v___x_5570_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5571_ = lean_uint8_dec_eq(v___x_5440_, v___x_5570_);
                    if v___x_5571_ == 0 {
                        v___x_5572_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5573_ = lean_uint8_dec_eq(v___x_5440_, v___x_5572_);
                        if v___x_5573_ == 0 {
                            v___x_5574_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5575_ = lean_uint8_dec_eq(v___x_5440_, v___x_5574_);
                            if v___x_5575_ == 0 {
                                v___x_5576_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5577_ = lean_uint8_dec_eq(v___x_5440_, v___x_5576_);
                                if v___x_5577_ == 0 {
                                    v___x_5578_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5579_ = lean_uint8_dec_eq(v___x_5440_, v___x_5578_);
                                    if v___x_5579_ == 0 {
                                        v___x_5580_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5581_ = lean_uint8_dec_eq(v___x_5440_, v___x_5580_);
                                        if v___x_5581_ == 0 {
                                            v___x_5582_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5583_ =
                                                lean_uint8_dec_eq(v___x_5440_, v___x_5582_);
                                            if v___x_5583_ == 0 {
                                                v___x_5584_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5585_ =
                                                    lean_uint8_dec_eq(v___x_5440_, v___x_5584_);
                                                if v___x_5585_ == 0 {
                                                    v___x_5586_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5587_ =
                                                        lean_uint8_dec_eq(v___x_5440_, v___x_5586_);
                                                    v___y_5563_ = v___x_5587_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    v___y_5563_ = v___x_5585_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5563_ = v___x_5583_;
                                                state = 23;
                                                continue;
                                            }
                                        } else {
                                            v___y_5563_ = v___x_5581_;
                                            state = 23;
                                            continue;
                                        }
                                    } else {
                                        v___y_5563_ = v___x_5579_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    v___y_5563_ = v___x_5577_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v___y_5563_ = v___x_5575_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v___y_5563_ = v___x_5573_;
                            state = 23;
                            continue;
                        }
                    } else {
                        v___y_5563_ = v___x_5571_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            25 => {
                if v___y_5589_ == 0 {
                    v___x_5590_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5591_ = lean_uint8_dec_eq(v___x_5440_, v___x_5590_);
                    if v___x_5591_ == 0 {
                        v___x_5592_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5593_ = lean_uint8_dec_eq(v___x_5440_, v___x_5592_);
                        v___y_5569_ = v___x_5593_;
                        state = 24;
                        continue;
                    } else {
                        v___y_5569_ = v___x_5591_;
                        state = 24;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            26 => {
                if v___y_5595_ == 0 {
                    v___x_5596_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5597_ = lean_uint8_dec_eq(v___x_5440_, v___x_5596_);
                    if v___x_5597_ == 0 {
                        v___x_5598_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5599_ = lean_uint8_dec_eq(v___x_5440_, v___x_5598_);
                        v___y_5589_ = v___x_5599_;
                        state = 25;
                        continue;
                    } else {
                        v___y_5589_ = v___x_5597_;
                        state = 25;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            27 => {
                if v___y_5601_ == 0 {
                    v___x_5602_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5603_ = lean_uint8_dec_eq(v___x_5440_, v___x_5602_);
                    if v___x_5603_ == 0 {
                        v___x_5604_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5605_ = lean_uint8_dec_eq(v___x_5440_, v___x_5604_);
                        v___y_5595_ = v___x_5605_;
                        state = 26;
                        continue;
                    } else {
                        v___y_5595_ = v___x_5603_;
                        state = 26;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            28 => {
                if v___y_5607_ == 0 {
                    v___x_5608_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5609_ = lean_uint8_dec_le(v___x_5608_, v___x_5440_);
                    if v___x_5609_ == 0 {
                        v___y_5601_ = v___x_5609_;
                        state = 27;
                        continue;
                    } else {
                        v___x_5610_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5611_ = lean_uint8_dec_le(v___x_5440_, v___x_5610_);
                        v___y_5601_ = v___x_5611_;
                        state = 27;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            29 => {
                if v___y_5613_ == 0 {
                    v___x_5614_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5615_ = lean_uint8_dec_le(v___x_5614_, v___x_5440_);
                    if v___x_5615_ == 0 {
                        v___y_5607_ = v___x_5615_;
                        state = 28;
                        continue;
                    } else {
                        v___x_5616_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5617_ = lean_uint8_dec_le(v___x_5440_, v___x_5616_);
                        v___y_5607_ = v___x_5617_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___y_5555_ = v___x_5431_;
                    state = 21;
                    continue;
                }
            }
            30 => {
                v___x_5626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5626_, 0, v___y_5410_);
                crate::leanh::lean_ctor_set(v___x_5626_, 1, v___x_5625_);
                return v___x_5626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Parser_parsePath(
    mut v_config_5640_: *mut crate::leanh::LeanObject,
    mut v_forceAbsolute_5641_: u8,
    mut v_allowEmpty_5642_: u8,
    mut v_a_5643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isAbsolute_5654_: u8 = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isAbsolute_5658_: u8 = 0;
    let mut v_totalLength_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5667_: u8 = 0;
    let mut v_fst_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5673_: u8 = 0;
    let mut v_pos_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5678_: u8 = 0;
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5682_: u8 = 0;
    let mut v___y_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5688_: u8 = 0;
    let mut v_pos_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5690_: u8 = 0;
    let mut v___y_5692_: u8 = 0;
    let mut v_pos_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: u8 = 0;
    let mut v___y_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5700_: u8 = 0;
    let mut v_array_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: u8 = 0;
    let mut v___x_5705_: u8 = 0;
    let mut v___x_5706_: u8 = 0;
    let mut v___x_5707_: u8 = 0;
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5718_: u8 = 0;
    let mut v_unused_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5722_: u8 = 0;
    let mut v_pos_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5724_: u8 = 0;
    let mut v_pos_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5729_: u8 = 0;
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: u8 = 0;
    let mut v___y_5734_: u8 = 0;
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: u8 = 0;
    let mut v___x_5737_: u8 = 0;
    let mut v___y_5739_: u8 = 0;
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: u8 = 0;
    let mut v___y_5745_: u8 = 0;
    let mut v___x_5746_: u8 = 0;
    let mut v___x_5747_: u8 = 0;
    let mut v___x_5748_: u8 = 0;
    let mut v___x_5749_: u8 = 0;
    let mut v___y_5751_: u8 = 0;
    let mut v___x_5752_: u8 = 0;
    let mut v___x_5753_: u8 = 0;
    let mut v___x_5754_: u8 = 0;
    let mut v___x_5755_: u8 = 0;
    let mut v___x_5756_: u8 = 0;
    let mut v___x_5757_: u8 = 0;
    let mut v___x_5758_: u8 = 0;
    let mut v___x_5759_: u8 = 0;
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: u8 = 0;
    let mut v___x_5762_: u8 = 0;
    let mut v___x_5763_: u8 = 0;
    let mut v___x_5764_: u8 = 0;
    let mut v___x_5765_: u8 = 0;
    let mut v___x_5766_: u8 = 0;
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: u8 = 0;
    let mut v___y_5771_: u8 = 0;
    let mut v___x_5772_: u8 = 0;
    let mut v___x_5773_: u8 = 0;
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: u8 = 0;
    let mut v___y_5777_: u8 = 0;
    let mut v___x_5778_: u8 = 0;
    let mut v___x_5779_: u8 = 0;
    let mut v___x_5780_: u8 = 0;
    let mut v___x_5781_: u8 = 0;
    let mut v___y_5783_: u8 = 0;
    let mut v___x_5784_: u8 = 0;
    let mut v___x_5785_: u8 = 0;
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5787_: u8 = 0;
    let mut v___y_5789_: u8 = 0;
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: u8 = 0;
    let mut v___x_5793_: u8 = 0;
    let mut v___y_5795_: u8 = 0;
    let mut v___x_5796_: u8 = 0;
    let mut v___x_5797_: u8 = 0;
    let mut v___x_5798_: u8 = 0;
    let mut v___x_5799_: u8 = 0;
    let mut v___x_5800_: u8 = 0;
    let mut v___x_5801_: u8 = 0;
    let mut v___x_5802_: u8 = 0;
    let mut v___x_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5652_ = crate::leanh::lean_ctor_get(v_a_5643_, 0);
                crate::leanh::lean_inc_ref(v_array_5652_);
                v_idx_5653_ = crate::leanh::lean_ctor_get(v_a_5643_, 1);
                crate::leanh::lean_inc(v_idx_5653_);
                v_isAbsolute_5654_ = 0;
                v___x_5655_ = crate::leanh::lean_unsigned_to_nat(0);
                v_segments_5656_ = l_Std_Http_URI_Parser_parsePath___closed__4;
                v___x_5735_ = lean_byte_array_size(v_array_5652_);
                v___x_5736_ = lean_nat_dec_lt(v_idx_5653_, v___x_5735_);
                if v___x_5736_ == 0 {
                    v_pos_5726_ = v_a_5643_;
                    v_array_5727_ = v_array_5652_;
                    v_idx_5728_ = v_idx_5653_;
                    v_res_5729_ = v_isAbsolute_5654_;
                    state = 15;
                    continue;
                } else {
                    v___x_5737_ = lean_byte_array_fget(v_array_5652_, v_idx_5653_);
                    v___x_5800_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                    v___x_5801_ = lean_uint8_dec_le(v___x_5800_, v___x_5737_);
                    if v___x_5801_ == 0 {
                        v___y_5795_ = v___x_5801_;
                        state = 24;
                        continue;
                    } else {
                        v___x_5802_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                        v___x_5803_ = lean_uint8_dec_le(v___x_5737_, v___x_5802_);
                        v___y_5795_ = v___x_5803_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5646_ = l_Std_Http_URI_Parser_parsePath___closed__1;
                v___x_5647_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5647_, 0, v___y_5645_);
                crate::leanh::lean_ctor_set(v___x_5647_, 1, v___x_5646_);
                return v___x_5647_;
            }
            2 => {
                v___x_5650_ = l_Std_Http_URI_Parser_parsePath___closed__3;
                v___x_5651_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5651_, 0, v___y_5649_);
                crate::leanh::lean_ctor_set(v___x_5651_, 1, v___x_5650_);
                return v___x_5651_;
            }
            3 => {
                v___x_5661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5661_, 0, v_segments_5656_);
                crate::leanh::lean_ctor_set(v___x_5661_, 1, v_totalLength_5659_);
                v___x_5662_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_5640_, v___x_5661_, v___y_5660_);
                if crate::leanh::lean_obj_tag(v___x_5662_) == 0 {
                    v_res_5663_ = crate::leanh::lean_ctor_get(v___x_5662_, 1);
                    v_pos_5664_ = crate::leanh::lean_ctor_get(v___x_5662_, 0);
                    v_isSharedCheck_5673_ = (!crate::leanh::lean_is_exclusive(v___x_5662_)) as u8;
                    if v_isSharedCheck_5673_ == 0 {
                        v___x_5666_ = v___x_5662_;
                        v_isShared_5667_ = v_isSharedCheck_5673_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_5663_);
                        crate::leanh::lean_inc(v_pos_5664_);
                        crate::leanh::lean_dec(v___x_5662_);
                        v___x_5666_ = crate::leanh::lean_box(0);
                        v_isShared_5667_ = v_isSharedCheck_5673_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_pos_5674_ = crate::leanh::lean_ctor_get(v___x_5662_, 0);
                    v_err_5675_ = crate::leanh::lean_ctor_get(v___x_5662_, 1);
                    v_isSharedCheck_5682_ = (!crate::leanh::lean_is_exclusive(v___x_5662_)) as u8;
                    if v_isSharedCheck_5682_ == 0 {
                        v___x_5677_ = v___x_5662_;
                        v_isShared_5678_ = v_isSharedCheck_5682_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_5675_);
                        crate::leanh::lean_inc(v_pos_5674_);
                        crate::leanh::lean_dec(v___x_5662_);
                        v___x_5677_ = crate::leanh::lean_box(0);
                        v_isShared_5678_ = v_isSharedCheck_5682_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_5668_ = crate::leanh::lean_ctor_get(v_res_5663_, 0);
                crate::leanh::lean_inc(v_fst_5668_);
                crate::leanh::lean_dec(v_res_5663_);
                v___x_5669_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5669_, 0, v_fst_5668_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5669_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isAbsolute_5658_,
                );
                if v_isShared_5667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5666_, 1, v___x_5669_);
                    v___x_5671_ = v___x_5666_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5672_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_pos_5664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5672_, 1, v___x_5669_);
                    v___x_5671_ = v_reuseFailAlloc_5672_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5671_;
            }
            6 => {
                if v_isShared_5678_ == 0 {
                    v___x_5680_ = v___x_5677_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5681_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_pos_5674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_err_5675_);
                    v___x_5680_ = v_reuseFailAlloc_5681_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5680_;
            }
            8 => {
                v___x_5685_ = l_Std_Http_URI_Parser_parsePath___closed__5;
                v___x_5686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5686_, 0, v___y_5684_);
                crate::leanh::lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                return v___x_5686_;
            }
            9 => {
                if v_allowEmpty_5642_ == 0 {
                    v___y_5645_ = v_pos_5689_;
                    state = 1;
                    continue;
                } else {
                    if v_res_5690_ == 0 {
                        if v___y_5688_ == 0 {
                            v___y_5684_ = v_pos_5689_;
                            state = 8;
                            continue;
                        } else {
                            v___y_5645_ = v_pos_5689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_5684_ = v_pos_5689_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                if v_forceAbsolute_5641_ == 0 {
                    v_isAbsolute_5658_ = v_isAbsolute_5654_;
                    v_totalLength_5659_ = v___x_5655_;
                    v___y_5660_ = v_pos_5693_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_config_5640_);
                    v_array_5694_ = crate::leanh::lean_ctor_get(v_pos_5693_, 0);
                    v_idx_5695_ = crate::leanh::lean_ctor_get(v_pos_5693_, 1);
                    v___x_5696_ = lean_byte_array_size(v_array_5694_);
                    v___x_5697_ = lean_nat_dec_lt(v_idx_5695_, v___x_5696_);
                    if v___x_5697_ == 0 {
                        v___y_5688_ = v___y_5692_;
                        v_pos_5689_ = v_pos_5693_;
                        v_res_5690_ = v_forceAbsolute_5641_;
                        state = 9;
                        continue;
                    } else {
                        v___y_5688_ = v___y_5692_;
                        v_pos_5689_ = v_pos_5693_;
                        v_res_5690_ = v_isAbsolute_5654_;
                        state = 9;
                        continue;
                    }
                }
            }
            11 => {
                v_array_5701_ = crate::leanh::lean_ctor_get(v___y_5699_, 0);
                v_idx_5702_ = crate::leanh::lean_ctor_get(v___y_5699_, 1);
                v___x_5703_ = lean_byte_array_size(v_array_5701_);
                v___x_5704_ = lean_nat_dec_lt(v_idx_5702_, v___x_5703_);
                if v___x_5704_ == 0 {
                    v___y_5692_ = v___y_5700_;
                    v_pos_5693_ = v___y_5699_;
                    state = 10;
                    continue;
                } else {
                    v___x_5705_ = lean_byte_array_fget(v_array_5701_, v_idx_5702_);
                    v___x_5706_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                    v___x_5707_ = lean_uint8_dec_eq(v___x_5705_, v___x_5706_);
                    if v___x_5707_ == 0 {
                        v___y_5692_ = v___y_5700_;
                        v_pos_5693_ = v___y_5699_;
                        state = 10;
                        continue;
                    } else {
                        if v___x_5704_ == 0 {
                            crate::leanh::lean_dec_ref(v_config_5640_);
                            v___x_5708_ = crate::leanh::lean_box(0);
                            v___x_5709_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5709_, 0, v___y_5699_);
                            crate::leanh::lean_ctor_set(v___x_5709_, 1, v___x_5708_);
                            return v___x_5709_;
                        } else {
                            crate::leanh::lean_inc(v_idx_5702_);
                            crate::leanh::lean_inc_ref(v_array_5701_);
                            v_isSharedCheck_5718_ =
                                (!crate::leanh::lean_is_exclusive(v___y_5699_)) as u8;
                            if v_isSharedCheck_5718_ == 0 {
                                v_unused_5719_ = crate::leanh::lean_ctor_get(v___y_5699_, 1);
                                crate::leanh::lean_dec(v_unused_5719_);
                                v_unused_5720_ = crate::leanh::lean_ctor_get(v___y_5699_, 0);
                                crate::leanh::lean_dec(v_unused_5720_);
                                v___x_5711_ = v___y_5699_;
                                v_isShared_5712_ = v_isSharedCheck_5718_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_5699_);
                                v___x_5711_ = crate::leanh::lean_box(0);
                                v_isShared_5712_ = v_isSharedCheck_5718_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
            }
            12 => {
                v___x_5713_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5714_ = lean_nat_add(v_idx_5702_, v___x_5713_);
                crate::leanh::lean_dec(v_idx_5702_);
                if v_isShared_5712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5711_, 1, v___x_5714_);
                    v___x_5716_ = v___x_5711_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_array_5701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 1, v___x_5714_);
                    v___x_5716_ = v_reuseFailAlloc_5717_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_isAbsolute_5658_ = v___x_5704_;
                v_totalLength_5659_ = v___x_5713_;
                v___y_5660_ = v___x_5716_;
                state = 3;
                continue;
            }
            14 => {
                if v_allowEmpty_5642_ == 0 {
                    if v_res_5724_ == 0 {
                        if v___y_5722_ == 0 {
                            crate::leanh::lean_dec_ref(v_config_5640_);
                            v___y_5649_ = v_pos_5723_;
                            state = 2;
                            continue;
                        } else {
                            v___y_5699_ = v_pos_5723_;
                            v___y_5700_ = v___y_5722_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_config_5640_);
                        v___y_5649_ = v_pos_5723_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_5699_ = v_pos_5723_;
                    v___y_5700_ = v___y_5722_;
                    state = 11;
                    continue;
                }
            }
            15 => {
                v___x_5730_ = lean_byte_array_size(v_array_5727_);
                crate::leanh::lean_dec_ref(v_array_5727_);
                v___x_5731_ = lean_nat_dec_lt(v_idx_5728_, v___x_5730_);
                crate::leanh::lean_dec(v_idx_5728_);
                if v___x_5731_ == 0 {
                    v___x_5732_ = 1;
                    v___y_5722_ = v_res_5729_;
                    v_pos_5723_ = v_pos_5726_;
                    v_res_5724_ = v___x_5732_;
                    state = 14;
                    continue;
                } else {
                    v___y_5722_ = v_res_5729_;
                    v_pos_5723_ = v_pos_5726_;
                    v_res_5724_ = v_isAbsolute_5654_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                if v___y_5734_ == 0 {
                    v_pos_5726_ = v_a_5643_;
                    v_array_5727_ = v_array_5652_;
                    v_idx_5728_ = v_idx_5653_;
                    v_res_5729_ = v_isAbsolute_5654_;
                    state = 15;
                    continue;
                } else {
                    v_pos_5726_ = v_a_5643_;
                    v_array_5727_ = v_array_5652_;
                    v_idx_5728_ = v_idx_5653_;
                    v_res_5729_ = v___y_5734_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                if v___y_5739_ == 0 {
                    v___x_5740_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                    v___x_5741_ = lean_uint8_dec_eq(v___x_5737_, v___x_5740_);
                    if v___x_5741_ == 0 {
                        v___x_5742_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                        v___x_5743_ = lean_uint8_dec_eq(v___x_5737_, v___x_5742_);
                        v___y_5734_ = v___x_5743_;
                        state = 16;
                        continue;
                    } else {
                        v___y_5734_ = v___x_5741_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                if v___y_5745_ == 0 {
                    v___x_5746_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5747_ = lean_uint8_dec_eq(v___x_5737_, v___x_5746_);
                    if v___x_5747_ == 0 {
                        v___x_5748_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5749_ = lean_uint8_dec_eq(v___x_5737_, v___x_5748_);
                        v___y_5739_ = v___x_5749_;
                        state = 17;
                        continue;
                    } else {
                        v___y_5739_ = v___x_5747_;
                        state = 17;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            19 => {
                if v___y_5751_ == 0 {
                    v___x_5752_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5753_ = lean_uint8_dec_eq(v___x_5737_, v___x_5752_);
                    if v___x_5753_ == 0 {
                        v___x_5754_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5755_ = lean_uint8_dec_eq(v___x_5737_, v___x_5754_);
                        if v___x_5755_ == 0 {
                            v___x_5756_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5757_ = lean_uint8_dec_eq(v___x_5737_, v___x_5756_);
                            if v___x_5757_ == 0 {
                                v___x_5758_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5759_ = lean_uint8_dec_eq(v___x_5737_, v___x_5758_);
                                if v___x_5759_ == 0 {
                                    v___x_5760_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5761_ = lean_uint8_dec_eq(v___x_5737_, v___x_5760_);
                                    if v___x_5761_ == 0 {
                                        v___x_5762_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5763_ = lean_uint8_dec_eq(v___x_5737_, v___x_5762_);
                                        if v___x_5763_ == 0 {
                                            v___x_5764_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5765_ =
                                                lean_uint8_dec_eq(v___x_5737_, v___x_5764_);
                                            if v___x_5765_ == 0 {
                                                v___x_5766_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5767_ =
                                                    lean_uint8_dec_eq(v___x_5737_, v___x_5766_);
                                                if v___x_5767_ == 0 {
                                                    v___x_5768_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5769_ =
                                                        lean_uint8_dec_eq(v___x_5737_, v___x_5768_);
                                                    v___y_5745_ = v___x_5769_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    v___y_5745_ = v___x_5767_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5745_ = v___x_5765_;
                                                state = 18;
                                                continue;
                                            }
                                        } else {
                                            v___y_5745_ = v___x_5763_;
                                            state = 18;
                                            continue;
                                        }
                                    } else {
                                        v___y_5745_ = v___x_5761_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___y_5745_ = v___x_5759_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                v___y_5745_ = v___x_5757_;
                                state = 18;
                                continue;
                            }
                        } else {
                            v___y_5745_ = v___x_5755_;
                            state = 18;
                            continue;
                        }
                    } else {
                        v___y_5745_ = v___x_5753_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            20 => {
                if v___y_5771_ == 0 {
                    v___x_5772_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5773_ = lean_uint8_dec_eq(v___x_5737_, v___x_5772_);
                    if v___x_5773_ == 0 {
                        v___x_5774_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5775_ = lean_uint8_dec_eq(v___x_5737_, v___x_5774_);
                        v___y_5751_ = v___x_5775_;
                        state = 19;
                        continue;
                    } else {
                        v___y_5751_ = v___x_5773_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            21 => {
                if v___y_5777_ == 0 {
                    v___x_5778_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5779_ = lean_uint8_dec_eq(v___x_5737_, v___x_5778_);
                    if v___x_5779_ == 0 {
                        v___x_5780_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5781_ = lean_uint8_dec_eq(v___x_5737_, v___x_5780_);
                        v___y_5771_ = v___x_5781_;
                        state = 20;
                        continue;
                    } else {
                        v___y_5771_ = v___x_5779_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            22 => {
                if v___y_5783_ == 0 {
                    v___x_5784_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5785_ = lean_uint8_dec_eq(v___x_5737_, v___x_5784_);
                    if v___x_5785_ == 0 {
                        v___x_5786_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5787_ = lean_uint8_dec_eq(v___x_5737_, v___x_5786_);
                        v___y_5777_ = v___x_5787_;
                        state = 21;
                        continue;
                    } else {
                        v___y_5777_ = v___x_5785_;
                        state = 21;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            23 => {
                if v___y_5789_ == 0 {
                    v___x_5790_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5791_ = lean_uint8_dec_le(v___x_5790_, v___x_5737_);
                    if v___x_5791_ == 0 {
                        v___y_5783_ = v___x_5791_;
                        state = 22;
                        continue;
                    } else {
                        v___x_5792_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5793_ = lean_uint8_dec_le(v___x_5737_, v___x_5792_);
                        v___y_5783_ = v___x_5793_;
                        state = 22;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            24 => {
                if v___y_5795_ == 0 {
                    v___x_5796_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5797_ = lean_uint8_dec_le(v___x_5796_, v___x_5737_);
                    if v___x_5797_ == 0 {
                        v___y_5789_ = v___x_5797_;
                        state = 23;
                        continue;
                    } else {
                        v___x_5798_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5799_ = lean_uint8_dec_le(v___x_5737_, v___x_5798_);
                        v___y_5789_ = v___x_5799_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___y_5734_ = v___x_5736_;
                    state = 16;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Parser_parsePath___boxed(
    mut v_config_5804_: *mut crate::leanh::LeanObject,
    mut v_forceAbsolute_5805_: *mut crate::leanh::LeanObject,
    mut v_allowEmpty_5806_: *mut crate::leanh::LeanObject,
    mut v_a_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_forceAbsolute_boxed_5808_: u8 = 0;
    let mut v_allowEmpty_boxed_5809_: u8 = 0;
    let mut v_res_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_forceAbsolute_boxed_5808_ = (crate::leanh::lean_unbox(v_forceAbsolute_5805_) as u8);
    v_allowEmpty_boxed_5809_ = (crate::leanh::lean_unbox(v_allowEmpty_5806_) as u8);
    v_res_5810_ = l_Std_Http_URI_Parser_parsePath(
        v_config_5804_,
        v_forceAbsolute_boxed_5808_,
        v_allowEmpty_boxed_5809_,
        v_a_5807_,
    );
    return v_res_5810_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(
    mut v_config_5811_: *mut crate::leanh::LeanObject,
    mut v_inst_5812_: *mut crate::leanh::LeanObject,
    mut v_a_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_5811_, v_a_5813_, v___y_5814_);
    return v___x_5815_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(
    mut v_config_5816_: *mut crate::leanh::LeanObject,
    mut v_inst_5817_: *mut crate::leanh::LeanObject,
    mut v_a_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5820_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_5816_, v_a_5818_, v___y_5819_);
    return v___x_5820_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(
    mut v_s_5821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5822_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0;
    return v___x_5822_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(
    mut v_s_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_5823_);
    crate::leanh::lean_dec_ref(v_s_5823_);
    return v_res_5824_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(
    mut v_s_5825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5826_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0;
    return v___x_5826_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(
    mut v_s_5827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5828_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_5827_);
    crate::leanh::lean_dec_ref(v_s_5827_);
    return v_res_5828_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(
    mut v_c_5829_: u8,
) -> u8 {
    let mut v___y_5831_: u8 = 0;
    let mut v___x_5832_: u8 = 0;
    let mut v___x_5833_: u8 = 0;
    let mut v___y_5835_: u8 = 0;
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: u8 = 0;
    let mut v___x_5839_: u8 = 0;
    let mut v___y_5841_: u8 = 0;
    let mut v___x_5842_: u8 = 0;
    let mut v___x_5843_: u8 = 0;
    let mut v___x_5844_: u8 = 0;
    let mut v___x_5845_: u8 = 0;
    let mut v___y_5847_: u8 = 0;
    let mut v___x_5848_: u8 = 0;
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: u8 = 0;
    let mut v___x_5853_: u8 = 0;
    let mut v___x_5854_: u8 = 0;
    let mut v___x_5855_: u8 = 0;
    let mut v___x_5856_: u8 = 0;
    let mut v___x_5857_: u8 = 0;
    let mut v___x_5858_: u8 = 0;
    let mut v___x_5859_: u8 = 0;
    let mut v___x_5860_: u8 = 0;
    let mut v___x_5861_: u8 = 0;
    let mut v___x_5862_: u8 = 0;
    let mut v___x_5863_: u8 = 0;
    let mut v___x_5864_: u8 = 0;
    let mut v___x_5865_: u8 = 0;
    let mut v___y_5867_: u8 = 0;
    let mut v___x_5868_: u8 = 0;
    let mut v___x_5869_: u8 = 0;
    let mut v___x_5870_: u8 = 0;
    let mut v___x_5871_: u8 = 0;
    let mut v___y_5873_: u8 = 0;
    let mut v___x_5874_: u8 = 0;
    let mut v___x_5875_: u8 = 0;
    let mut v___x_5876_: u8 = 0;
    let mut v___x_5877_: u8 = 0;
    let mut v___y_5879_: u8 = 0;
    let mut v___x_5880_: u8 = 0;
    let mut v___x_5881_: u8 = 0;
    let mut v___x_5882_: u8 = 0;
    let mut v___x_5883_: u8 = 0;
    let mut v___y_5885_: u8 = 0;
    let mut v___x_5886_: u8 = 0;
    let mut v___x_5887_: u8 = 0;
    let mut v___x_5888_: u8 = 0;
    let mut v___x_5889_: u8 = 0;
    let mut v___y_5891_: u8 = 0;
    let mut v___x_5892_: u8 = 0;
    let mut v___x_5893_: u8 = 0;
    let mut v___x_5894_: u8 = 0;
    let mut v___x_5895_: u8 = 0;
    let mut v___x_5896_: u8 = 0;
    let mut v___x_5897_: u8 = 0;
    let mut v___x_5898_: u8 = 0;
    let mut v___x_5899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5896_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                v___x_5897_ = lean_uint8_dec_le(v___x_5896_, v_c_5829_);
                if v___x_5897_ == 0 {
                    v___y_5891_ = v___x_5897_;
                    state = 9;
                    continue;
                } else {
                    v___x_5898_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                    v___x_5899_ = lean_uint8_dec_le(v_c_5829_, v___x_5898_);
                    v___y_5891_ = v___x_5899_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                if v___y_5831_ == 0 {
                    v___x_5832_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
                    v___x_5833_ = lean_uint8_dec_eq(v_c_5829_, v___x_5832_);
                    if v___x_5833_ == 0 {
                        return v___y_5831_;
                    } else {
                        return v___x_5833_;
                    }
                } else {
                    return v___y_5831_;
                }
            }
            2 => {
                if v___y_5835_ == 0 {
                    v___x_5836_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                    v___x_5837_ = lean_uint8_dec_eq(v_c_5829_, v___x_5836_);
                    if v___x_5837_ == 0 {
                        v___x_5838_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                        v___x_5839_ = lean_uint8_dec_eq(v_c_5829_, v___x_5838_);
                        v___y_5831_ = v___x_5839_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5831_ = v___x_5837_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_5835_;
                }
            }
            3 => {
                if v___y_5841_ == 0 {
                    v___x_5842_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_5843_ = lean_uint8_dec_eq(v_c_5829_, v___x_5842_);
                    if v___x_5843_ == 0 {
                        v___x_5844_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
                        v___x_5845_ = lean_uint8_dec_eq(v_c_5829_, v___x_5844_);
                        v___y_5835_ = v___x_5845_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5835_ = v___x_5843_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_5841_;
                }
            }
            4 => {
                if v___y_5847_ == 0 {
                    v___x_5848_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
                    v___x_5849_ = lean_uint8_dec_eq(v_c_5829_, v___x_5848_);
                    if v___x_5849_ == 0 {
                        v___x_5850_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
                        v___x_5851_ = lean_uint8_dec_eq(v_c_5829_, v___x_5850_);
                        if v___x_5851_ == 0 {
                            v___x_5852_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
                            v___x_5853_ = lean_uint8_dec_eq(v_c_5829_, v___x_5852_);
                            if v___x_5853_ == 0 {
                                v___x_5854_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
                                v___x_5855_ = lean_uint8_dec_eq(v_c_5829_, v___x_5854_);
                                if v___x_5855_ == 0 {
                                    v___x_5856_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                                    v___x_5857_ = lean_uint8_dec_eq(v_c_5829_, v___x_5856_);
                                    if v___x_5857_ == 0 {
                                        v___x_5858_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
                                        v___x_5859_ = lean_uint8_dec_eq(v_c_5829_, v___x_5858_);
                                        if v___x_5859_ == 0 {
                                            v___x_5860_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
                                            v___x_5861_ = lean_uint8_dec_eq(v_c_5829_, v___x_5860_);
                                            if v___x_5861_ == 0 {
                                                v___x_5862_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
                                                v___x_5863_ =
                                                    lean_uint8_dec_eq(v_c_5829_, v___x_5862_);
                                                if v___x_5863_ == 0 {
                                                    v___x_5864_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
                                                    v___x_5865_ =
                                                        lean_uint8_dec_eq(v_c_5829_, v___x_5864_);
                                                    v___y_5841_ = v___x_5865_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    v___y_5841_ = v___x_5863_;
                                                    state = 3;
                                                    continue;
                                                }
                                            } else {
                                                v___y_5841_ = v___x_5861_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            v___y_5841_ = v___x_5859_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        v___y_5841_ = v___x_5857_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    v___y_5841_ = v___x_5855_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___y_5841_ = v___x_5853_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___y_5841_ = v___x_5851_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_5841_ = v___x_5849_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_5847_;
                }
            }
            5 => {
                if v___y_5867_ == 0 {
                    v___x_5868_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
                    v___x_5869_ = lean_uint8_dec_eq(v_c_5829_, v___x_5868_);
                    if v___x_5869_ == 0 {
                        v___x_5870_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
                        v___x_5871_ = lean_uint8_dec_eq(v_c_5829_, v___x_5870_);
                        v___y_5847_ = v___x_5871_;
                        state = 4;
                        continue;
                    } else {
                        v___y_5847_ = v___x_5869_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_5867_;
                }
            }
            6 => {
                if v___y_5873_ == 0 {
                    v___x_5874_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
                    v___x_5875_ = lean_uint8_dec_eq(v_c_5829_, v___x_5874_);
                    if v___x_5875_ == 0 {
                        v___x_5876_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
                        v___x_5877_ = lean_uint8_dec_eq(v_c_5829_, v___x_5876_);
                        v___y_5867_ = v___x_5877_;
                        state = 5;
                        continue;
                    } else {
                        v___y_5867_ = v___x_5875_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_5873_;
                }
            }
            7 => {
                if v___y_5879_ == 0 {
                    v___x_5880_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
                    v___x_5881_ = lean_uint8_dec_eq(v_c_5829_, v___x_5880_);
                    if v___x_5881_ == 0 {
                        v___x_5882_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
                        v___x_5883_ = lean_uint8_dec_eq(v_c_5829_, v___x_5882_);
                        v___y_5873_ = v___x_5883_;
                        state = 6;
                        continue;
                    } else {
                        v___y_5873_ = v___x_5881_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_5879_;
                }
            }
            8 => {
                if v___y_5885_ == 0 {
                    v___x_5886_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
                    v___x_5887_ = lean_uint8_dec_le(v___x_5886_, v_c_5829_);
                    if v___x_5887_ == 0 {
                        v___y_5879_ = v___x_5887_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5888_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
                        v___x_5889_ = lean_uint8_dec_le(v_c_5829_, v___x_5888_);
                        v___y_5879_ = v___x_5889_;
                        state = 7;
                        continue;
                    }
                } else {
                    return v___y_5885_;
                }
            }
            9 => {
                if v___y_5891_ == 0 {
                    v___x_5892_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
                    v___x_5893_ = lean_uint8_dec_le(v___x_5892_, v_c_5829_);
                    if v___x_5893_ == 0 {
                        v___y_5885_ = v___x_5893_;
                        state = 8;
                        continue;
                    } else {
                        v___x_5894_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
                        v___x_5895_ = lean_uint8_dec_le(v_c_5829_, v___x_5894_);
                        v___y_5885_ = v___x_5895_;
                        state = 8;
                        continue;
                    }
                } else {
                    return v___y_5891_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(
    mut v_c_5900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_5901_: u8 = 0;
    let mut v_res_5902_: u8 = 0;
    let mut v_r_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_5901_ = (crate::leanh::lean_unbox(v_c_5900_) as u8);
    v_res_5902_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(
        v_c_boxed_5901_,
    );
    v_r_5903_ = crate::leanh::lean_box((v_res_5902_) as usize);
    return v_r_5903_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(
    mut v___x_5904_: *mut crate::leanh::LeanObject,
    mut v___x_5905_: *mut crate::leanh::LeanObject,
    mut v_a_5906_: *mut crate::leanh::LeanObject,
    mut v_b_5907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v_str_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: u8 = 0;
    let mut v___x_5923_: u32 = 0;
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: u32 = 0;
    let mut v___x_5926_: u8 = 0;
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5906_) == 0 {
                    v_currPos_5913_ = crate::leanh::lean_ctor_get(v_a_5906_, 0);
                    v_searcher_5914_ = crate::leanh::lean_ctor_get(v_a_5906_, 1);
                    v_isSharedCheck_5940_ = (!crate::leanh::lean_is_exclusive(v_a_5906_)) as u8;
                    if v_isSharedCheck_5940_ == 0 {
                        v___x_5916_ = v_a_5906_;
                        v_isShared_5917_ = v_isSharedCheck_5940_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_5914_);
                        crate::leanh::lean_inc(v_currPos_5913_);
                        crate::leanh::lean_dec(v_a_5906_);
                        v___x_5916_ = crate::leanh::lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5940_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_5907_;
                }
            }
            1 => {
                v___x_5910_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5911_ = lean_nat_add(v_b_5907_, v___x_5910_);
                crate::leanh::lean_dec(v_b_5907_);
                v_a_5906_ = v_it_5909_;
                v_b_5907_ = v___x_5911_;
                state = 0;
                continue;
            }
            2 => {
                v_str_5918_ = crate::leanh::lean_ctor_get(v___x_5904_, 0);
                v_startInclusive_5919_ = crate::leanh::lean_ctor_get(v___x_5904_, 1);
                v_endExclusive_5920_ = crate::leanh::lean_ctor_get(v___x_5904_, 2);
                v___x_5921_ = lean_nat_sub(v_endExclusive_5920_, v_startInclusive_5919_);
                v___x_5922_ = lean_nat_dec_eq(v_searcher_5914_, v___x_5921_);
                crate::leanh::lean_dec(v___x_5921_);
                if v___x_5922_ == 0 {
                    v___x_5923_ = 38;
                    v___x_5924_ = lean_nat_add(v_startInclusive_5919_, v_searcher_5914_);
                    v___x_5925_ = lean_string_utf8_get_fast(v_str_5918_, v___x_5924_);
                    v___x_5926_ = lean_uint32_dec_eq(v___x_5925_, v___x_5923_);
                    if v___x_5926_ == 0 {
                        crate::leanh::lean_dec(v_searcher_5914_);
                        v___x_5927_ = lean_string_utf8_next_fast(v_str_5918_, v___x_5924_);
                        crate::leanh::lean_dec(v___x_5924_);
                        v___x_5928_ = lean_nat_sub(v___x_5927_, v_startInclusive_5919_);
                        if v_isShared_5917_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5916_, 1, v___x_5928_);
                            v___x_5930_ = v___x_5916_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5932_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_currPos_5913_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 1, v___x_5928_);
                            v___x_5930_ = v_reuseFailAlloc_5932_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_currPos_5913_);
                        v___x_5933_ = lean_string_utf8_next_fast(v_str_5918_, v___x_5924_);
                        v___x_5934_ = lean_nat_sub(v___x_5933_, v___x_5924_);
                        crate::leanh::lean_dec(v___x_5924_);
                        v___x_5935_ = lean_nat_add(v_searcher_5914_, v___x_5934_);
                        crate::leanh::lean_dec(v___x_5934_);
                        crate::leanh::lean_dec(v_searcher_5914_);
                        crate::leanh::lean_inc(v___x_5935_);
                        if v_isShared_5917_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5916_, 1, v___x_5935_);
                            crate::leanh::lean_ctor_set(v___x_5916_, 0, v___x_5935_);
                            v_nextIt_5937_ = v___x_5916_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5938_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 0, v___x_5935_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 1, v___x_5935_);
                            v_nextIt_5937_ = v_reuseFailAlloc_5938_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5916_);
                    crate::leanh::lean_dec(v_searcher_5914_);
                    crate::leanh::lean_dec(v_currPos_5913_);
                    v___x_5939_ = crate::leanh::lean_box(1);
                    v_it_5909_ = v___x_5939_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_5906_ = v___x_5930_;
                state = 0;
                continue;
            }
            4 => {
                v_it_5909_ = v_nextIt_5937_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(
    mut v___x_5941_: *mut crate::leanh::LeanObject,
    mut v___x_5942_: *mut crate::leanh::LeanObject,
    mut v_a_5943_: *mut crate::leanh::LeanObject,
    mut v_b_5944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5945_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_5941_, v___x_5942_, v_a_5943_, v_b_5944_);
    crate::leanh::lean_dec(v___x_5942_);
    crate::leanh::lean_dec_ref(v___x_5941_);
    return v_res_5945_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(
    mut v___x_5946_: *mut crate::leanh::LeanObject,
    mut v___x_5947_: *mut crate::leanh::LeanObject,
    mut v___x_5948_: *mut crate::leanh::LeanObject,
    mut v_a_5949_: *mut crate::leanh::LeanObject,
    mut v_b_5950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v_str_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: u32 = 0;
    let mut v___x_5968_: u32 = 0;
    let mut v___x_5969_: u8 = 0;
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5949_) == 0 {
                    v_currPos_5956_ = crate::leanh::lean_ctor_get(v_a_5949_, 0);
                    v_searcher_5957_ = crate::leanh::lean_ctor_get(v_a_5949_, 1);
                    v_isSharedCheck_5983_ = (!crate::leanh::lean_is_exclusive(v_a_5949_)) as u8;
                    if v_isSharedCheck_5983_ == 0 {
                        v___x_5959_ = v_a_5949_;
                        v_isShared_5960_ = v_isSharedCheck_5983_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_5957_);
                        crate::leanh::lean_inc(v_currPos_5956_);
                        crate::leanh::lean_dec(v_a_5949_);
                        v___x_5959_ = crate::leanh::lean_box(0);
                        v_isShared_5960_ = v_isSharedCheck_5983_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_5950_;
                }
            }
            1 => {
                v___x_5953_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5954_ = lean_nat_add(v_b_5950_, v___x_5953_);
                crate::leanh::lean_dec(v_b_5950_);
                v___x_5955_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_5947_, v___x_5948_, v_it_5952_, v___x_5954_);
                return v___x_5955_;
            }
            2 => {
                v_str_5961_ = crate::leanh::lean_ctor_get(v___x_5947_, 0);
                v_startInclusive_5962_ = crate::leanh::lean_ctor_get(v___x_5947_, 1);
                v_endExclusive_5963_ = crate::leanh::lean_ctor_get(v___x_5947_, 2);
                v___x_5964_ = lean_nat_sub(v_endExclusive_5963_, v_startInclusive_5962_);
                v___x_5965_ = lean_nat_dec_eq(v_searcher_5957_, v___x_5964_);
                crate::leanh::lean_dec(v___x_5964_);
                if v___x_5965_ == 0 {
                    v___x_5966_ = lean_nat_add(v_startInclusive_5962_, v_searcher_5957_);
                    v___x_5967_ = lean_string_utf8_get_fast(v_str_5961_, v___x_5966_);
                    v___x_5968_ = 38;
                    v___x_5969_ = lean_uint32_dec_eq(v___x_5967_, v___x_5968_);
                    if v___x_5969_ == 0 {
                        crate::leanh::lean_dec(v_searcher_5957_);
                        v___x_5970_ = lean_string_utf8_next_fast(v_str_5961_, v___x_5966_);
                        crate::leanh::lean_dec(v___x_5966_);
                        v___x_5971_ = lean_nat_sub(v___x_5970_, v_startInclusive_5962_);
                        if v_isShared_5960_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5959_, 1, v___x_5971_);
                            v___x_5973_ = v___x_5959_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5975_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_currPos_5956_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5971_);
                            v___x_5973_ = v_reuseFailAlloc_5975_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_currPos_5956_);
                        v___x_5976_ = lean_string_utf8_next_fast(v_str_5961_, v___x_5966_);
                        v___x_5977_ = lean_nat_sub(v___x_5976_, v___x_5966_);
                        crate::leanh::lean_dec(v___x_5966_);
                        v___x_5978_ = lean_nat_add(v_searcher_5957_, v___x_5977_);
                        crate::leanh::lean_dec(v___x_5977_);
                        crate::leanh::lean_dec(v_searcher_5957_);
                        crate::leanh::lean_inc(v___x_5978_);
                        if v_isShared_5960_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5959_, 1, v___x_5978_);
                            crate::leanh::lean_ctor_set(v___x_5959_, 0, v___x_5978_);
                            v_nextIt_5980_ = v___x_5959_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5981_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5978_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5981_, 1, v___x_5978_);
                            v_nextIt_5980_ = v_reuseFailAlloc_5981_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5959_);
                    crate::leanh::lean_dec(v_searcher_5957_);
                    crate::leanh::lean_dec(v_currPos_5956_);
                    v___x_5982_ = crate::leanh::lean_box(1);
                    v_it_5952_ = v___x_5982_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5974_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_5947_, v___x_5948_, v___x_5973_, v_b_5950_);
                return v___x_5974_;
            }
            4 => {
                v_it_5952_ = v_nextIt_5980_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(
    mut v___x_5984_: *mut crate::leanh::LeanObject,
    mut v___x_5985_: *mut crate::leanh::LeanObject,
    mut v___x_5986_: *mut crate::leanh::LeanObject,
    mut v_a_5987_: *mut crate::leanh::LeanObject,
    mut v_b_5988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_5984_, v___x_5985_, v___x_5986_, v_a_5987_, v_b_5988_);
    crate::leanh::lean_dec(v___x_5986_);
    crate::leanh::lean_dec_ref(v___x_5985_);
    crate::leanh::lean_dec_ref(v___x_5984_);
    return v_res_5989_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(
    mut v_out_5990_: *mut crate::leanh::LeanObject,
    mut v_a_5991_: *mut crate::leanh::LeanObject,
    mut v_b_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currPos_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5997_: u8 = 0;
    let mut v_str_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: u8 = 0;
    let mut v___x_6013_: u32 = 0;
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u32 = 0;
    let mut v___x_6016_: u8 = 0;
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5991_) == 0 {
                    v_currPos_5993_ = crate::leanh::lean_ctor_get(v_a_5991_, 0);
                    v_searcher_5994_ = crate::leanh::lean_ctor_get(v_a_5991_, 1);
                    v_isSharedCheck_6033_ = (!crate::leanh::lean_is_exclusive(v_a_5991_)) as u8;
                    if v_isSharedCheck_6033_ == 0 {
                        v___x_5996_ = v_a_5991_;
                        v_isShared_5997_ = v_isSharedCheck_6033_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_5994_);
                        crate::leanh::lean_inc(v_currPos_5993_);
                        crate::leanh::lean_dec(v_a_5991_);
                        v___x_5996_ = crate::leanh::lean_box(0);
                        v_isShared_5997_ = v_isSharedCheck_6033_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5992_;
                }
            }
            1 => {
                v_str_5998_ = crate::leanh::lean_ctor_get(v_out_5990_, 0);
                v_startInclusive_5999_ = crate::leanh::lean_ctor_get(v_out_5990_, 1);
                v_endExclusive_6000_ = crate::leanh::lean_ctor_get(v_out_5990_, 2);
                v___x_6011_ = lean_nat_sub(v_endExclusive_6000_, v_startInclusive_5999_);
                v___x_6012_ = lean_nat_dec_eq(v_searcher_5994_, v___x_6011_);
                if v___x_6012_ == 0 {
                    crate::leanh::lean_dec(v___x_6011_);
                    v___x_6013_ = 61;
                    v___x_6014_ = lean_nat_add(v_startInclusive_5999_, v_searcher_5994_);
                    v___x_6015_ = lean_string_utf8_get_fast(v_str_5998_, v___x_6014_);
                    v___x_6016_ = lean_uint32_dec_eq(v___x_6015_, v___x_6013_);
                    if v___x_6016_ == 0 {
                        crate::leanh::lean_dec(v_searcher_5994_);
                        v___x_6017_ = lean_string_utf8_next_fast(v_str_5998_, v___x_6014_);
                        crate::leanh::lean_dec(v___x_6014_);
                        v___x_6018_ = lean_nat_sub(v___x_6017_, v_startInclusive_5999_);
                        if v_isShared_5997_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5996_, 1, v___x_6018_);
                            v___x_6020_ = v___x_5996_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6022_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_currPos_5993_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 1, v___x_6018_);
                            v___x_6020_ = v_reuseFailAlloc_6022_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6023_ = lean_string_utf8_next_fast(v_str_5998_, v___x_6014_);
                        v___x_6024_ = lean_nat_sub(v___x_6023_, v___x_6014_);
                        crate::leanh::lean_dec(v___x_6014_);
                        v___x_6025_ = lean_nat_add(v_searcher_5994_, v___x_6024_);
                        crate::leanh::lean_dec(v___x_6024_);
                        v_slice_6026_ = l_String_Slice_subslice_x21(
                            v_out_5990_,
                            v_currPos_5993_,
                            v_searcher_5994_,
                        );
                        crate::leanh::lean_inc(v___x_6025_);
                        if v_isShared_5997_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5996_, 1, v___x_6025_);
                            crate::leanh::lean_ctor_set(v___x_5996_, 0, v___x_6025_);
                            v_nextIt_6028_ = v___x_5996_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6031_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6025_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 1, v___x_6025_);
                            v_nextIt_6028_ = v_reuseFailAlloc_6031_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5996_);
                    crate::leanh::lean_dec(v_searcher_5994_);
                    v___x_6032_ = crate::leanh::lean_box(1);
                    v_it_6002_ = v___x_6032_;
                    v_startInclusive_6003_ = v_currPos_5993_;
                    v_endExclusive_6004_ = v___x_6011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6005_ = lean_nat_add(v_startInclusive_5999_, v_startInclusive_6003_);
                crate::leanh::lean_dec(v_startInclusive_6003_);
                v___x_6006_ = lean_nat_add(v_startInclusive_5999_, v_endExclusive_6004_);
                crate::leanh::lean_dec(v_endExclusive_6004_);
                crate::leanh::lean_inc_ref(v_str_5998_);
                v___x_6007_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6007_, 0, v_str_5998_);
                crate::leanh::lean_ctor_set(v___x_6007_, 1, v___x_6005_);
                crate::leanh::lean_ctor_set(v___x_6007_, 2, v___x_6006_);
                v___x_6008_ = l_String_Slice_toString(v___x_6007_);
                crate::leanh::lean_dec_ref_known(v___x_6007_, 3);
                v___x_6009_ = lean_array_push(v_b_5992_, v___x_6008_);
                v_a_5991_ = v_it_6002_;
                v_b_5992_ = v___x_6009_;
                state = 0;
                continue;
            }
            3 => {
                v_a_5991_ = v___x_6020_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_6029_ = crate::leanh::lean_ctor_get(v_slice_6026_, 0);
                crate::leanh::lean_inc(v_startInclusive_6029_);
                v_endExclusive_6030_ = crate::leanh::lean_ctor_get(v_slice_6026_, 1);
                crate::leanh::lean_inc(v_endExclusive_6030_);
                crate::leanh::lean_dec_ref(v_slice_6026_);
                v_it_6002_ = v_nextIt_6028_;
                v_startInclusive_6003_ = v_startInclusive_6029_;
                v_endExclusive_6004_ = v_endExclusive_6030_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(
    mut v_out_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v_b_6036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6037_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_6034_, v_a_6035_, v_b_6036_);
    crate::leanh::lean_dec_ref(v_out_6034_);
    return v_res_6037_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(
    mut v___x_6041_: *mut crate::leanh::LeanObject,
    mut v___x_6042_: *mut crate::leanh::LeanObject,
    mut v___x_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_b_6045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6078_: u8 = 0;
    let mut v_str_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: u8 = 0;
    let mut v___x_6084_: u32 = 0;
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: u32 = 0;
    let mut v___x_6087_: u8 = 0;
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6104_: u8 = 0;
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6044_) == 0 {
                    v_currPos_6074_ = crate::leanh::lean_ctor_get(v_a_6044_, 0);
                    v_searcher_6075_ = crate::leanh::lean_ctor_get(v_a_6044_, 1);
                    v_isSharedCheck_6104_ = (!crate::leanh::lean_is_exclusive(v_a_6044_)) as u8;
                    if v_isSharedCheck_6104_ == 0 {
                        v___x_6077_ = v_a_6044_;
                        v_isShared_6078_ = v_isSharedCheck_6104_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_6075_);
                        crate::leanh::lean_inc(v_currPos_6074_);
                        crate::leanh::lean_dec(v_a_6044_);
                        v___x_6077_ = crate::leanh::lean_box(0);
                        v_isShared_6078_ = v_isSharedCheck_6104_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6043_);
                    crate::leanh::lean_dec_ref(v___x_6041_);
                    v___x_6105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6105_, 0, v_b_6045_);
                    return v___x_6105_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_6041_);
                v___x_6050_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6050_, 0, v___x_6041_);
                crate::leanh::lean_ctor_set(v___x_6050_, 1, v_startInclusive_6048_);
                crate::leanh::lean_ctor_set(v___x_6050_, 2, v_endExclusive_6049_);
                v___x_6051_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_6050_);
                v___x_6052_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0;
                v___x_6053_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_6050_, v___x_6051_, v___x_6052_);
                crate::leanh::lean_dec_ref_known(v___x_6050_, 3);
                v___x_6054_ = lean_array_to_list(v___x_6053_);
                if crate::leanh::lean_obj_tag(v___x_6054_) == 0 {
                    v_a_6044_ = v_it_6047_;
                    state = 0;
                    continue;
                } else {
                    v_tail_6056_ = crate::leanh::lean_ctor_get(v___x_6054_, 1);
                    crate::leanh::lean_inc(v_tail_6056_);
                    if crate::leanh::lean_obj_tag(v_tail_6056_) == 0 {
                        v_head_6057_ = crate::leanh::lean_ctor_get(v___x_6054_, 0);
                        crate::leanh::lean_inc(v_head_6057_);
                        crate::leanh::lean_dec_ref_known(v___x_6054_, 2);
                        v___x_6058_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_6057_);
                        crate::leanh::lean_dec(v_head_6057_);
                        if crate::leanh::lean_obj_tag(v___x_6058_) == 0 {
                            crate::leanh::lean_dec(v_it_6047_);
                            crate::leanh::lean_dec_ref(v_b_6045_);
                            crate::leanh::lean_dec(v___x_6043_);
                            crate::leanh::lean_dec_ref(v___x_6041_);
                            v___x_6059_ = crate::leanh::lean_box(0);
                            return v___x_6059_;
                        } else {
                            v_val_6060_ = crate::leanh::lean_ctor_get(v___x_6058_, 0);
                            crate::leanh::lean_inc(v_val_6060_);
                            crate::leanh::lean_dec_ref_known(v___x_6058_, 1);
                            v___x_6061_ = crate::leanh::lean_box(0);
                            v___x_6062_ = l_Std_Http_URI_Query_insertEncoded(
                                v_b_6045_,
                                v_val_6060_,
                                v___x_6061_,
                            );
                            v_a_6044_ = v_it_6047_;
                            v_b_6045_ = v___x_6062_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_head_6064_ = crate::leanh::lean_ctor_get(v___x_6054_, 0);
                        crate::leanh::lean_inc(v_head_6064_);
                        crate::leanh::lean_dec_ref_known(v___x_6054_, 2);
                        v___x_6065_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_6064_);
                        crate::leanh::lean_dec(v_head_6064_);
                        if crate::leanh::lean_obj_tag(v___x_6065_) == 0 {
                            crate::leanh::lean_dec(v_tail_6056_);
                            crate::leanh::lean_dec(v_it_6047_);
                            crate::leanh::lean_dec_ref(v_b_6045_);
                            crate::leanh::lean_dec(v___x_6043_);
                            crate::leanh::lean_dec_ref(v___x_6041_);
                            v___x_6066_ = crate::leanh::lean_box(0);
                            return v___x_6066_;
                        } else {
                            v_val_6067_ = crate::leanh::lean_ctor_get(v___x_6065_, 0);
                            crate::leanh::lean_inc(v_val_6067_);
                            crate::leanh::lean_dec_ref_known(v___x_6065_, 1);
                            v___x_6068_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1;
                            v___x_6069_ = l_String_intercalate(v___x_6068_, v_tail_6056_);
                            v___x_6070_ =
                                l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_6069_);
                            crate::leanh::lean_dec_ref(v___x_6069_);
                            if crate::leanh::lean_obj_tag(v___x_6070_) == 0 {
                                crate::leanh::lean_dec(v_val_6067_);
                                crate::leanh::lean_dec(v_it_6047_);
                                crate::leanh::lean_dec_ref(v_b_6045_);
                                crate::leanh::lean_dec(v___x_6043_);
                                crate::leanh::lean_dec_ref(v___x_6041_);
                                v___x_6071_ = crate::leanh::lean_box(0);
                                return v___x_6071_;
                            } else {
                                v___x_6072_ = l_Std_Http_URI_Query_insertEncoded(
                                    v_b_6045_,
                                    v_val_6067_,
                                    v___x_6070_,
                                );
                                v_a_6044_ = v_it_6047_;
                                v_b_6045_ = v___x_6072_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_str_6079_ = crate::leanh::lean_ctor_get(v___x_6042_, 0);
                v_startInclusive_6080_ = crate::leanh::lean_ctor_get(v___x_6042_, 1);
                v_endExclusive_6081_ = crate::leanh::lean_ctor_get(v___x_6042_, 2);
                v___x_6082_ = lean_nat_sub(v_endExclusive_6081_, v_startInclusive_6080_);
                v___x_6083_ = lean_nat_dec_eq(v_searcher_6075_, v___x_6082_);
                crate::leanh::lean_dec(v___x_6082_);
                if v___x_6083_ == 0 {
                    v___x_6084_ = 38;
                    v___x_6085_ = lean_nat_add(v_startInclusive_6080_, v_searcher_6075_);
                    v___x_6086_ = lean_string_utf8_get_fast(v_str_6079_, v___x_6085_);
                    v___x_6087_ = lean_uint32_dec_eq(v___x_6086_, v___x_6084_);
                    if v___x_6087_ == 0 {
                        crate::leanh::lean_dec(v_searcher_6075_);
                        v___x_6088_ = lean_string_utf8_next_fast(v_str_6079_, v___x_6085_);
                        crate::leanh::lean_dec(v___x_6085_);
                        v___x_6089_ = lean_nat_sub(v___x_6088_, v_startInclusive_6080_);
                        if v_isShared_6078_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6077_, 1, v___x_6089_);
                            v___x_6091_ = v___x_6077_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6093_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_currPos_6074_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 1, v___x_6089_);
                            v___x_6091_ = v_reuseFailAlloc_6093_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6094_ = lean_string_utf8_next_fast(v_str_6079_, v___x_6085_);
                        v___x_6095_ = lean_nat_sub(v___x_6094_, v___x_6085_);
                        crate::leanh::lean_dec(v___x_6085_);
                        v___x_6096_ = lean_nat_add(v_searcher_6075_, v___x_6095_);
                        crate::leanh::lean_dec(v___x_6095_);
                        v_slice_6097_ = l_String_Slice_subslice_x21(
                            v___x_6042_,
                            v_currPos_6074_,
                            v_searcher_6075_,
                        );
                        crate::leanh::lean_inc(v___x_6096_);
                        if v_isShared_6078_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6077_, 1, v___x_6096_);
                            crate::leanh::lean_ctor_set(v___x_6077_, 0, v___x_6096_);
                            v_nextIt_6099_ = v___x_6077_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6102_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v___x_6096_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 1, v___x_6096_);
                            v_nextIt_6099_ = v_reuseFailAlloc_6102_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6077_);
                    crate::leanh::lean_dec(v_searcher_6075_);
                    v___x_6103_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_6043_);
                    v_it_6047_ = v___x_6103_;
                    v_startInclusive_6048_ = v_currPos_6074_;
                    v_endExclusive_6049_ = v___x_6043_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_6044_ = v___x_6091_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_6100_ = crate::leanh::lean_ctor_get(v_slice_6097_, 0);
                crate::leanh::lean_inc(v_startInclusive_6100_);
                v_endExclusive_6101_ = crate::leanh::lean_ctor_get(v_slice_6097_, 1);
                crate::leanh::lean_inc(v_endExclusive_6101_);
                crate::leanh::lean_dec_ref(v_slice_6097_);
                v_it_6047_ = v_nextIt_6099_;
                v_startInclusive_6048_ = v_startInclusive_6100_;
                v_endExclusive_6049_ = v_endExclusive_6101_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(
    mut v___x_6106_: *mut crate::leanh::LeanObject,
    mut v___x_6107_: *mut crate::leanh::LeanObject,
    mut v___x_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
    mut v_b_6110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6111_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6106_, v___x_6107_, v___x_6108_, v_a_6109_, v_b_6110_);
    crate::leanh::lean_dec_ref(v___x_6107_);
    return v_res_6111_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(
    mut v___x_6112_: *mut crate::leanh::LeanObject,
    mut v___x_6113_: *mut crate::leanh::LeanObject,
    mut v___x_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
    mut v_b_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6149_: u8 = 0;
    let mut v_str_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: u8 = 0;
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: u32 = 0;
    let mut v___x_6157_: u32 = 0;
    let mut v___x_6158_: u8 = 0;
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6175_: u8 = 0;
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6115_) == 0 {
                    v_currPos_6145_ = crate::leanh::lean_ctor_get(v_a_6115_, 0);
                    v_searcher_6146_ = crate::leanh::lean_ctor_get(v_a_6115_, 1);
                    v_isSharedCheck_6175_ = (!crate::leanh::lean_is_exclusive(v_a_6115_)) as u8;
                    if v_isSharedCheck_6175_ == 0 {
                        v___x_6148_ = v_a_6115_;
                        v_isShared_6149_ = v_isSharedCheck_6175_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_6146_);
                        crate::leanh::lean_inc(v_currPos_6145_);
                        crate::leanh::lean_dec(v_a_6115_);
                        v___x_6148_ = crate::leanh::lean_box(0);
                        v_isShared_6149_ = v_isSharedCheck_6175_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6114_);
                    crate::leanh::lean_dec_ref(v___x_6112_);
                    v___x_6176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6176_, 0, v_b_6116_);
                    return v___x_6176_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_6112_);
                v___x_6121_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6121_, 0, v___x_6112_);
                crate::leanh::lean_ctor_set(v___x_6121_, 1, v_startInclusive_6119_);
                crate::leanh::lean_ctor_set(v___x_6121_, 2, v_endExclusive_6120_);
                v___x_6122_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_6121_);
                v___x_6123_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0;
                v___x_6124_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_6121_, v___x_6122_, v___x_6123_);
                crate::leanh::lean_dec_ref_known(v___x_6121_, 3);
                v___x_6125_ = lean_array_to_list(v___x_6124_);
                if crate::leanh::lean_obj_tag(v___x_6125_) == 0 {
                    v___x_6126_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6112_, v___x_6113_, v___x_6114_, v_it_6118_, v_b_6116_);
                    return v___x_6126_;
                } else {
                    v_tail_6127_ = crate::leanh::lean_ctor_get(v___x_6125_, 1);
                    crate::leanh::lean_inc(v_tail_6127_);
                    if crate::leanh::lean_obj_tag(v_tail_6127_) == 0 {
                        v_head_6128_ = crate::leanh::lean_ctor_get(v___x_6125_, 0);
                        crate::leanh::lean_inc(v_head_6128_);
                        crate::leanh::lean_dec_ref_known(v___x_6125_, 2);
                        v___x_6129_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_6128_);
                        crate::leanh::lean_dec(v_head_6128_);
                        if crate::leanh::lean_obj_tag(v___x_6129_) == 0 {
                            crate::leanh::lean_dec(v_it_6118_);
                            crate::leanh::lean_dec_ref(v_b_6116_);
                            crate::leanh::lean_dec(v___x_6114_);
                            crate::leanh::lean_dec_ref(v___x_6112_);
                            v___x_6130_ = crate::leanh::lean_box(0);
                            return v___x_6130_;
                        } else {
                            v_val_6131_ = crate::leanh::lean_ctor_get(v___x_6129_, 0);
                            crate::leanh::lean_inc(v_val_6131_);
                            crate::leanh::lean_dec_ref_known(v___x_6129_, 1);
                            v___x_6132_ = crate::leanh::lean_box(0);
                            v___x_6133_ = l_Std_Http_URI_Query_insertEncoded(
                                v_b_6116_,
                                v_val_6131_,
                                v___x_6132_,
                            );
                            v___x_6134_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6112_, v___x_6113_, v___x_6114_, v_it_6118_, v___x_6133_);
                            return v___x_6134_;
                        }
                    } else {
                        v_head_6135_ = crate::leanh::lean_ctor_get(v___x_6125_, 0);
                        crate::leanh::lean_inc(v_head_6135_);
                        crate::leanh::lean_dec_ref_known(v___x_6125_, 2);
                        v___x_6136_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_6135_);
                        crate::leanh::lean_dec(v_head_6135_);
                        if crate::leanh::lean_obj_tag(v___x_6136_) == 0 {
                            crate::leanh::lean_dec(v_tail_6127_);
                            crate::leanh::lean_dec(v_it_6118_);
                            crate::leanh::lean_dec_ref(v_b_6116_);
                            crate::leanh::lean_dec(v___x_6114_);
                            crate::leanh::lean_dec_ref(v___x_6112_);
                            v___x_6137_ = crate::leanh::lean_box(0);
                            return v___x_6137_;
                        } else {
                            v_val_6138_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
                            crate::leanh::lean_inc(v_val_6138_);
                            crate::leanh::lean_dec_ref_known(v___x_6136_, 1);
                            v___x_6139_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1;
                            v___x_6140_ = l_String_intercalate(v___x_6139_, v_tail_6127_);
                            v___x_6141_ =
                                l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_6140_);
                            crate::leanh::lean_dec_ref(v___x_6140_);
                            if crate::leanh::lean_obj_tag(v___x_6141_) == 0 {
                                crate::leanh::lean_dec(v_val_6138_);
                                crate::leanh::lean_dec(v_it_6118_);
                                crate::leanh::lean_dec_ref(v_b_6116_);
                                crate::leanh::lean_dec(v___x_6114_);
                                crate::leanh::lean_dec_ref(v___x_6112_);
                                v___x_6142_ = crate::leanh::lean_box(0);
                                return v___x_6142_;
                            } else {
                                v___x_6143_ = l_Std_Http_URI_Query_insertEncoded(
                                    v_b_6116_,
                                    v_val_6138_,
                                    v___x_6141_,
                                );
                                v___x_6144_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6112_, v___x_6113_, v___x_6114_, v_it_6118_, v___x_6143_);
                                return v___x_6144_;
                            }
                        }
                    }
                }
            }
            2 => {
                v_str_6150_ = crate::leanh::lean_ctor_get(v___x_6113_, 0);
                v_startInclusive_6151_ = crate::leanh::lean_ctor_get(v___x_6113_, 1);
                v_endExclusive_6152_ = crate::leanh::lean_ctor_get(v___x_6113_, 2);
                v___x_6153_ = lean_nat_sub(v_endExclusive_6152_, v_startInclusive_6151_);
                v___x_6154_ = lean_nat_dec_eq(v_searcher_6146_, v___x_6153_);
                crate::leanh::lean_dec(v___x_6153_);
                if v___x_6154_ == 0 {
                    v___x_6155_ = lean_nat_add(v_startInclusive_6151_, v_searcher_6146_);
                    v___x_6156_ = lean_string_utf8_get_fast(v_str_6150_, v___x_6155_);
                    v___x_6157_ = 38;
                    v___x_6158_ = lean_uint32_dec_eq(v___x_6156_, v___x_6157_);
                    if v___x_6158_ == 0 {
                        crate::leanh::lean_dec(v_searcher_6146_);
                        v___x_6159_ = lean_string_utf8_next_fast(v_str_6150_, v___x_6155_);
                        crate::leanh::lean_dec(v___x_6155_);
                        v___x_6160_ = lean_nat_sub(v___x_6159_, v_startInclusive_6151_);
                        if v_isShared_6149_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6148_, 1, v___x_6160_);
                            v___x_6162_ = v___x_6148_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6164_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_currPos_6145_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6164_, 1, v___x_6160_);
                            v___x_6162_ = v_reuseFailAlloc_6164_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6165_ = lean_string_utf8_next_fast(v_str_6150_, v___x_6155_);
                        v___x_6166_ = lean_nat_sub(v___x_6165_, v___x_6155_);
                        crate::leanh::lean_dec(v___x_6155_);
                        v___x_6167_ = lean_nat_add(v_searcher_6146_, v___x_6166_);
                        crate::leanh::lean_dec(v___x_6166_);
                        v_slice_6168_ = l_String_Slice_subslice_x21(
                            v___x_6113_,
                            v_currPos_6145_,
                            v_searcher_6146_,
                        );
                        crate::leanh::lean_inc(v___x_6167_);
                        if v_isShared_6149_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6148_, 1, v___x_6167_);
                            crate::leanh::lean_ctor_set(v___x_6148_, 0, v___x_6167_);
                            v_nextIt_6170_ = v___x_6148_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6173_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6173_, 0, v___x_6167_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6173_, 1, v___x_6167_);
                            v_nextIt_6170_ = v_reuseFailAlloc_6173_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6148_);
                    crate::leanh::lean_dec(v_searcher_6146_);
                    v___x_6174_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_6114_);
                    v_it_6118_ = v___x_6174_;
                    v_startInclusive_6119_ = v_currPos_6145_;
                    v_endExclusive_6120_ = v___x_6114_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6163_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6112_, v___x_6113_, v___x_6114_, v___x_6162_, v_b_6116_);
                return v___x_6163_;
            }
            4 => {
                v_startInclusive_6171_ = crate::leanh::lean_ctor_get(v_slice_6168_, 0);
                crate::leanh::lean_inc(v_startInclusive_6171_);
                v_endExclusive_6172_ = crate::leanh::lean_ctor_get(v_slice_6168_, 1);
                crate::leanh::lean_inc(v_endExclusive_6172_);
                crate::leanh::lean_dec_ref(v_slice_6168_);
                v_it_6118_ = v_nextIt_6170_;
                v_startInclusive_6119_ = v_startInclusive_6171_;
                v_endExclusive_6120_ = v_endExclusive_6172_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(
    mut v___x_6177_: *mut crate::leanh::LeanObject,
    mut v___x_6178_: *mut crate::leanh::LeanObject,
    mut v___x_6179_: *mut crate::leanh::LeanObject,
    mut v_a_6180_: *mut crate::leanh::LeanObject,
    mut v_b_6181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6182_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_6177_, v___x_6178_, v___x_6179_, v_a_6180_, v_b_6181_);
    crate::leanh::lean_dec_ref(v___x_6178_);
    return v_res_6182_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(
    mut v_config_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_maxQueryLength_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxQueryParams_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v_lower_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: u8 = 0;
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: u8 = 0;
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: u8 = 0;
    let mut v___x_6248_: u8 = 0;
    let mut v_isSharedCheck_6249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxQueryLength_6190_ = crate::leanh::lean_ctor_get(v_config_6188_, 4);
                crate::leanh::lean_inc(v_maxQueryLength_6190_);
                v_maxQueryParams_6191_ = crate::leanh::lean_ctor_get(v_config_6188_, 8);
                crate::leanh::lean_inc(v_maxQueryParams_6191_);
                crate::leanh::lean_dec_ref(v_config_6188_);
                v___f_6192_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0;
                v___x_6193_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_6189_);
                v___x_6194_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_6192_, v_maxQueryLength_6190_, v___x_6193_, v_a_6189_);
                crate::leanh::lean_dec(v_maxQueryLength_6190_);
                v_snd_6195_ = crate::leanh::lean_ctor_get(v___x_6194_, 1);
                crate::leanh::lean_inc(v_snd_6195_);
                v_fst_6196_ = crate::leanh::lean_ctor_get(v___x_6194_, 0);
                crate::leanh::lean_inc(v_fst_6196_);
                crate::leanh::lean_dec_ref(v___x_6194_);
                v_fst_6197_ = crate::leanh::lean_ctor_get(v_snd_6195_, 0);
                crate::leanh::lean_inc(v_fst_6197_);
                crate::leanh::lean_dec(v_snd_6195_);
                v_array_6198_ = crate::leanh::lean_ctor_get(v_a_6189_, 0);
                v_idx_6199_ = crate::leanh::lean_ctor_get(v_a_6189_, 1);
                v_isSharedCheck_6249_ = (!crate::leanh::lean_is_exclusive(v_a_6189_)) as u8;
                if v_isSharedCheck_6249_ == 0 {
                    v___x_6201_ = v_a_6189_;
                    v_isShared_6202_ = v_isSharedCheck_6249_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_6199_);
                    crate::leanh::lean_inc(v_array_6198_);
                    crate::leanh::lean_dec(v_a_6189_);
                    v___x_6201_ = crate::leanh::lean_box(0);
                    v_isShared_6202_ = v_isSharedCheck_6249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6243_ = lean_nat_add(v_idx_6199_, v_fst_6196_);
                crate::leanh::lean_dec(v_fst_6196_);
                v___x_6244_ = lean_byte_array_size(v_array_6198_);
                v___x_6248_ = lean_nat_dec_le(v_idx_6199_, v___x_6193_);
                if v___x_6248_ == 0 {
                    v___y_6246_ = v_idx_6199_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_6199_);
                    v___y_6246_ = v___x_6193_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                v___x_6206_ = l_ByteArray_toByteSlice(v_array_6198_, v_lower_6204_, v_upper_6205_);
                v___x_6207_ = l_ByteSlice_toByteArray(v___x_6206_);
                v___x_6208_ = lean_string_validate_utf8(v___x_6207_);
                if v___x_6208_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_6207_);
                    crate::leanh::lean_dec(v_maxQueryParams_6191_);
                    v___x_6209_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2;
                    if v_isShared_6202_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6201_, 1);
                        crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6209_);
                        crate::leanh::lean_ctor_set(v___x_6201_, 0, v_fst_6197_);
                        v___x_6211_ = v___x_6201_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6212_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6212_, 0, v_fst_6197_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6212_, 1, v___x_6209_);
                        v___x_6211_ = v_reuseFailAlloc_6212_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6213_ = lean_string_from_utf8_unchecked(v___x_6207_);
                    v___x_6214_ = lean_string_utf8_byte_size(v___x_6213_);
                    v___x_6215_ = lean_nat_dec_eq(v___x_6214_, v___x_6193_);
                    if v___x_6215_ == 0 {
                        crate::leanh::lean_inc_ref(v___x_6213_);
                        v___x_6216_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6216_, 0, v___x_6213_);
                        crate::leanh::lean_ctor_set(v___x_6216_, 1, v___x_6193_);
                        crate::leanh::lean_ctor_set(v___x_6216_, 2, v___x_6214_);
                        v___x_6217_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_6216_);
                        crate::leanh::lean_inc(v___x_6217_);
                        v___x_6218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_6213_, v___x_6216_, v___x_6214_, v___x_6217_, v___x_6193_);
                        v___x_6219_ = lean_nat_dec_lt(v_maxQueryParams_6191_, v___x_6218_);
                        crate::leanh::lean_dec(v___x_6218_);
                        if v___x_6219_ == 0 {
                            crate::leanh::lean_dec(v_maxQueryParams_6191_);
                            v___x_6220_ = l_Std_Http_URI_Query_empty;
                            v___x_6221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_6213_, v___x_6216_, v___x_6214_, v___x_6217_, v___x_6220_);
                            crate::leanh::lean_dec_ref_known(v___x_6216_, 3);
                            if crate::leanh::lean_obj_tag(v___x_6221_) == 1 {
                                v_val_6222_ = crate::leanh::lean_ctor_get(v___x_6221_, 0);
                                crate::leanh::lean_inc(v_val_6222_);
                                crate::leanh::lean_dec_ref_known(v___x_6221_, 1);
                                if v_isShared_6202_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6201_, 1, v_val_6222_);
                                    crate::leanh::lean_ctor_set(v___x_6201_, 0, v_fst_6197_);
                                    v___x_6224_ = v___x_6201_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6225_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6225_,
                                        0,
                                        v_fst_6197_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6225_,
                                        1,
                                        v_val_6222_,
                                    );
                                    v___x_6224_ = v_reuseFailAlloc_6225_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6221_);
                                v___x_6226_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2;
                                if v_isShared_6202_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_6201_, 1);
                                    crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6226_);
                                    crate::leanh::lean_ctor_set(v___x_6201_, 0, v_fst_6197_);
                                    v___x_6228_ = v___x_6201_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6229_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6229_,
                                        0,
                                        v_fst_6197_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6229_,
                                        1,
                                        v___x_6226_,
                                    );
                                    v___x_6228_ = v_reuseFailAlloc_6229_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6217_);
                            crate::leanh::lean_dec_ref_known(v___x_6216_, 3);
                            crate::leanh::lean_dec_ref(v___x_6213_);
                            v___x_6230_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3;
                            v___x_6231_ = l_Nat_reprFast(v_maxQueryParams_6191_);
                            v___x_6232_ = lean_string_append(v___x_6230_, v___x_6231_);
                            crate::leanh::lean_dec_ref(v___x_6231_);
                            v___x_6233_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3;
                            v___x_6234_ = lean_string_append(v___x_6232_, v___x_6233_);
                            v___x_6235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6235_, 0, v___x_6234_);
                            if v_isShared_6202_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6201_, 1);
                                crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6235_);
                                crate::leanh::lean_ctor_set(v___x_6201_, 0, v_fst_6197_);
                                v___x_6237_ = v___x_6201_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_6238_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_fst_6197_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 1, v___x_6235_);
                                v___x_6237_ = v_reuseFailAlloc_6238_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6213_);
                        crate::leanh::lean_dec(v_maxQueryParams_6191_);
                        v___x_6239_ = l_Std_Http_URI_Query_empty;
                        if v_isShared_6202_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6239_);
                            crate::leanh::lean_ctor_set(v___x_6201_, 0, v_fst_6197_);
                            v___x_6241_ = v___x_6201_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6242_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_fst_6197_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 1, v___x_6239_);
                            v___x_6241_ = v_reuseFailAlloc_6242_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6211_;
            }
            4 => {
                return v___x_6224_;
            }
            5 => {
                return v___x_6228_;
            }
            6 => {
                return v___x_6237_;
            }
            7 => {
                return v___x_6241_;
            }
            8 => {
                v___x_6247_ = lean_nat_dec_le(v___x_6243_, v___x_6244_);
                if v___x_6247_ == 0 {
                    crate::leanh::lean_dec(v___x_6243_);
                    v_lower_6204_ = v___y_6246_;
                    v_upper_6205_ = v___x_6244_;
                    state = 2;
                    continue;
                } else {
                    v_lower_6204_ = v___y_6246_;
                    v_upper_6205_ = v___x_6243_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(
    mut v___x_6250_: *mut crate::leanh::LeanObject,
    mut v___x_6251_: *mut crate::leanh::LeanObject,
    mut v___x_6252_: *mut crate::leanh::LeanObject,
    mut v_inst_6253_: *mut crate::leanh::LeanObject,
    mut v_R_6254_: *mut crate::leanh::LeanObject,
    mut v_a_6255_: *mut crate::leanh::LeanObject,
    mut v_b_6256_: *mut crate::leanh::LeanObject,
    mut v_c_6257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_6250_, v___x_6251_, v___x_6252_, v_a_6255_, v_b_6256_);
    return v___x_6258_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(
    mut v___x_6259_: *mut crate::leanh::LeanObject,
    mut v___x_6260_: *mut crate::leanh::LeanObject,
    mut v___x_6261_: *mut crate::leanh::LeanObject,
    mut v_inst_6262_: *mut crate::leanh::LeanObject,
    mut v_R_6263_: *mut crate::leanh::LeanObject,
    mut v_a_6264_: *mut crate::leanh::LeanObject,
    mut v_b_6265_: *mut crate::leanh::LeanObject,
    mut v_c_6266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_6259_, v___x_6260_, v___x_6261_, v_inst_6262_, v_R_6263_, v_a_6264_, v_b_6265_, v_c_6266_);
    crate::leanh::lean_dec(v___x_6261_);
    crate::leanh::lean_dec_ref(v___x_6260_);
    crate::leanh::lean_dec_ref(v___x_6259_);
    return v_res_6267_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(
    mut v_out_6268_: *mut crate::leanh::LeanObject,
    mut v_inst_6269_: *mut crate::leanh::LeanObject,
    mut v_R_6270_: *mut crate::leanh::LeanObject,
    mut v_a_6271_: *mut crate::leanh::LeanObject,
    mut v_b_6272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6273_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_6268_, v_a_6271_, v_b_6272_);
    return v___x_6273_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(
    mut v_out_6274_: *mut crate::leanh::LeanObject,
    mut v_inst_6275_: *mut crate::leanh::LeanObject,
    mut v_R_6276_: *mut crate::leanh::LeanObject,
    mut v_a_6277_: *mut crate::leanh::LeanObject,
    mut v_b_6278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_6274_, v_inst_6275_, v_R_6276_, v_a_6277_, v_b_6278_);
    crate::leanh::lean_dec_ref(v_out_6274_);
    return v_res_6279_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(
    mut v___x_6280_: *mut crate::leanh::LeanObject,
    mut v___x_6281_: *mut crate::leanh::LeanObject,
    mut v___x_6282_: *mut crate::leanh::LeanObject,
    mut v_inst_6283_: *mut crate::leanh::LeanObject,
    mut v_R_6284_: *mut crate::leanh::LeanObject,
    mut v_a_6285_: *mut crate::leanh::LeanObject,
    mut v_b_6286_: *mut crate::leanh::LeanObject,
    mut v_c_6287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_6280_, v___x_6281_, v___x_6282_, v_a_6285_, v_b_6286_);
    return v___x_6288_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(
    mut v___x_6289_: *mut crate::leanh::LeanObject,
    mut v___x_6290_: *mut crate::leanh::LeanObject,
    mut v___x_6291_: *mut crate::leanh::LeanObject,
    mut v_inst_6292_: *mut crate::leanh::LeanObject,
    mut v_R_6293_: *mut crate::leanh::LeanObject,
    mut v_a_6294_: *mut crate::leanh::LeanObject,
    mut v_b_6295_: *mut crate::leanh::LeanObject,
    mut v_c_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_6289_, v___x_6290_, v___x_6291_, v_inst_6292_, v_R_6293_, v_a_6294_, v_b_6295_, v_c_6296_);
    crate::leanh::lean_dec_ref(v___x_6290_);
    return v_res_6297_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(
    mut v___x_6298_: *mut crate::leanh::LeanObject,
    mut v___x_6299_: *mut crate::leanh::LeanObject,
    mut v___x_6300_: *mut crate::leanh::LeanObject,
    mut v_inst_6301_: *mut crate::leanh::LeanObject,
    mut v_R_6302_: *mut crate::leanh::LeanObject,
    mut v_a_6303_: *mut crate::leanh::LeanObject,
    mut v_b_6304_: *mut crate::leanh::LeanObject,
    mut v_c_6305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_6299_, v___x_6300_, v_a_6303_, v_b_6304_);
    return v___x_6306_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(
    mut v___x_6307_: *mut crate::leanh::LeanObject,
    mut v___x_6308_: *mut crate::leanh::LeanObject,
    mut v___x_6309_: *mut crate::leanh::LeanObject,
    mut v_inst_6310_: *mut crate::leanh::LeanObject,
    mut v_R_6311_: *mut crate::leanh::LeanObject,
    mut v_a_6312_: *mut crate::leanh::LeanObject,
    mut v_b_6313_: *mut crate::leanh::LeanObject,
    mut v_c_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6315_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_6307_, v___x_6308_, v___x_6309_, v_inst_6310_, v_R_6311_, v_a_6312_, v_b_6313_, v_c_6314_);
    crate::leanh::lean_dec(v___x_6309_);
    crate::leanh::lean_dec_ref(v___x_6308_);
    crate::leanh::lean_dec_ref(v___x_6307_);
    return v_res_6315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(
    mut v___x_6316_: *mut crate::leanh::LeanObject,
    mut v___x_6317_: *mut crate::leanh::LeanObject,
    mut v___x_6318_: *mut crate::leanh::LeanObject,
    mut v_inst_6319_: *mut crate::leanh::LeanObject,
    mut v_R_6320_: *mut crate::leanh::LeanObject,
    mut v_a_6321_: *mut crate::leanh::LeanObject,
    mut v_b_6322_: *mut crate::leanh::LeanObject,
    mut v_c_6323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6324_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_6316_, v___x_6317_, v___x_6318_, v_a_6321_, v_b_6322_);
    return v___x_6324_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(
    mut v___x_6325_: *mut crate::leanh::LeanObject,
    mut v___x_6326_: *mut crate::leanh::LeanObject,
    mut v___x_6327_: *mut crate::leanh::LeanObject,
    mut v_inst_6328_: *mut crate::leanh::LeanObject,
    mut v_R_6329_: *mut crate::leanh::LeanObject,
    mut v_a_6330_: *mut crate::leanh::LeanObject,
    mut v_b_6331_: *mut crate::leanh::LeanObject,
    mut v_c_6332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6333_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_6325_, v___x_6326_, v___x_6327_, v_inst_6328_, v_R_6329_, v_a_6330_, v_b_6331_, v_c_6332_);
    crate::leanh::lean_dec_ref(v___x_6326_);
    return v_res_6333_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(
    mut v_config_6337_: *mut crate::leanh::LeanObject,
    mut v_a_6338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_maxFragmentLength_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v_lower_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: u8 = 0;
    let mut v___x_6370_: u8 = 0;
    let mut v_isSharedCheck_6371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxFragmentLength_6339_ = crate::leanh::lean_ctor_get(v_config_6337_, 5);
                v___f_6340_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0;
                v___x_6341_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_6338_);
                v___x_6342_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_6340_, v_maxFragmentLength_6339_, v___x_6341_, v_a_6338_);
                v_snd_6343_ = crate::leanh::lean_ctor_get(v___x_6342_, 1);
                crate::leanh::lean_inc(v_snd_6343_);
                v_fst_6344_ = crate::leanh::lean_ctor_get(v___x_6342_, 0);
                crate::leanh::lean_inc(v_fst_6344_);
                crate::leanh::lean_dec_ref(v___x_6342_);
                v_fst_6345_ = crate::leanh::lean_ctor_get(v_snd_6343_, 0);
                crate::leanh::lean_inc(v_fst_6345_);
                crate::leanh::lean_dec(v_snd_6343_);
                v_array_6346_ = crate::leanh::lean_ctor_get(v_a_6338_, 0);
                v_idx_6347_ = crate::leanh::lean_ctor_get(v_a_6338_, 1);
                v_isSharedCheck_6371_ = (!crate::leanh::lean_is_exclusive(v_a_6338_)) as u8;
                if v_isSharedCheck_6371_ == 0 {
                    v___x_6349_ = v_a_6338_;
                    v_isShared_6350_ = v_isSharedCheck_6371_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_6347_);
                    crate::leanh::lean_inc(v_array_6346_);
                    crate::leanh::lean_dec(v_a_6338_);
                    v___x_6349_ = crate::leanh::lean_box(0);
                    v_isShared_6350_ = v_isSharedCheck_6371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6365_ = lean_nat_add(v_idx_6347_, v_fst_6344_);
                crate::leanh::lean_dec(v_fst_6344_);
                v___x_6366_ = lean_byte_array_size(v_array_6346_);
                v___x_6370_ = lean_nat_dec_le(v_idx_6347_, v___x_6341_);
                if v___x_6370_ == 0 {
                    v___y_6368_ = v_idx_6347_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_6347_);
                    v___y_6368_ = v___x_6341_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_6354_ = l_ByteArray_toByteSlice(v_array_6346_, v_lower_6352_, v_upper_6353_);
                v___x_6355_ = l_ByteSlice_toByteArray(v___x_6354_);
                v___x_6356_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_6355_);
                if crate::leanh::lean_obj_tag(v___x_6356_) == 1 {
                    v_val_6357_ = crate::leanh::lean_ctor_get(v___x_6356_, 0);
                    crate::leanh::lean_inc(v_val_6357_);
                    crate::leanh::lean_dec_ref_known(v___x_6356_, 1);
                    if v_isShared_6350_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6349_, 1, v_val_6357_);
                        crate::leanh::lean_ctor_set(v___x_6349_, 0, v_fst_6345_);
                        v___x_6359_ = v___x_6349_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_fst_6345_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6360_, 1, v_val_6357_);
                        v___x_6359_ = v_reuseFailAlloc_6360_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6356_);
                    v___x_6361_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1;
                    if v_isShared_6350_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6349_, 1);
                        crate::leanh::lean_ctor_set(v___x_6349_, 1, v___x_6361_);
                        crate::leanh::lean_ctor_set(v___x_6349_, 0, v_fst_6345_);
                        v___x_6363_ = v___x_6349_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6364_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6364_, 0, v_fst_6345_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6364_, 1, v___x_6361_);
                        v___x_6363_ = v_reuseFailAlloc_6364_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6359_;
            }
            4 => {
                return v___x_6363_;
            }
            5 => {
                v___x_6369_ = lean_nat_dec_le(v___x_6365_, v___x_6366_);
                if v___x_6369_ == 0 {
                    crate::leanh::lean_dec(v___x_6365_);
                    v_lower_6352_ = v___y_6368_;
                    v_upper_6353_ = v___x_6366_;
                    state = 2;
                    continue;
                } else {
                    v_lower_6352_ = v___y_6368_;
                    v_upper_6353_ = v___x_6365_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(
    mut v_config_6372_: *mut crate::leanh::LeanObject,
    mut v_a_6373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6374_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(
        v_config_6372_,
        v_a_6373_,
    );
    crate::leanh::lean_dec_ref(v_config_6372_);
    return v_res_6374_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6376_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0;
    v_utf8_6377_ = lean_string_to_utf8(v___x_6376_);
    return v_utf8_6377_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(
    mut v_config_6378_: *mut crate::leanh::LeanObject,
    mut v_a_6379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6391_: u8 = 0;
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6397_: u8 = 0;
    let mut v_pos_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6402_: u8 = 0;
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6406_: u8 = 0;
    let mut v_pos_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6411_: u8 = 0;
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6415_: u8 = 0;
    let mut v_utf8_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6423_: u8 = 0;
    let mut v_idx_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: u8 = 0;
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: u8 = 0;
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6435_: u8 = 0;
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6441_: u8 = 0;
    let mut v_pos_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut v_isSharedCheck_6451_: u8 = 0;
    let mut v_unused_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_6416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
                crate::leanh::lean_inc_ref(v_a_6379_);
                v___x_6417_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_6416_, v_a_6379_);
                if crate::leanh::lean_obj_tag(v___x_6417_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_6379_);
                    v_pos_6418_ = crate::leanh::lean_ctor_get(v___x_6417_, 0);
                    crate::leanh::lean_inc(v_pos_6418_);
                    crate::leanh::lean_dec_ref_known(v___x_6417_, 2);
                    v_pos_6381_ = v_pos_6418_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_6417_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_6379_);
                        v_pos_6419_ = crate::leanh::lean_ctor_get(v___x_6417_, 0);
                        crate::leanh::lean_inc(v_pos_6419_);
                        crate::leanh::lean_dec_ref_known(v___x_6417_, 2);
                        v_pos_6381_ = v_pos_6419_;
                        state = 1;
                        continue;
                    } else {
                        v_err_6420_ = crate::leanh::lean_ctor_get(v___x_6417_, 1);
                        v_isSharedCheck_6451_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6417_)) as u8;
                        if v_isSharedCheck_6451_ == 0 {
                            v_unused_6452_ = crate::leanh::lean_ctor_get(v___x_6417_, 0);
                            crate::leanh::lean_dec(v_unused_6452_);
                            v___x_6422_ = v___x_6417_;
                            v_isShared_6423_ = v_isSharedCheck_6451_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_6420_);
                            crate::leanh::lean_dec(v___x_6417_);
                            v___x_6422_ = crate::leanh::lean_box(0);
                            v_isShared_6423_ = v_isSharedCheck_6451_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6382_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(
                        v_config_6378_,
                        v_pos_6381_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6382_) == 0 {
                    v_pos_6383_ = crate::leanh::lean_ctor_get(v___x_6382_, 0);
                    crate::leanh::lean_inc(v_pos_6383_);
                    v_res_6384_ = crate::leanh::lean_ctor_get(v___x_6382_, 1);
                    crate::leanh::lean_inc(v_res_6384_);
                    crate::leanh::lean_dec_ref_known(v___x_6382_, 2);
                    v___x_6385_ = 1;
                    v___x_6386_ = l_Std_Http_URI_Parser_parsePath(
                        v_config_6378_,
                        v___x_6385_,
                        v___x_6385_,
                        v_pos_6383_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6386_) == 0 {
                        v_pos_6387_ = crate::leanh::lean_ctor_get(v___x_6386_, 0);
                        v_res_6388_ = crate::leanh::lean_ctor_get(v___x_6386_, 1);
                        v_isSharedCheck_6397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6386_)) as u8;
                        if v_isSharedCheck_6397_ == 0 {
                            v___x_6390_ = v___x_6386_;
                            v_isShared_6391_ = v_isSharedCheck_6397_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_6388_);
                            crate::leanh::lean_inc(v_pos_6387_);
                            crate::leanh::lean_dec(v___x_6386_);
                            v___x_6390_ = crate::leanh::lean_box(0);
                            v_isShared_6391_ = v_isSharedCheck_6397_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_6384_);
                        v_pos_6398_ = crate::leanh::lean_ctor_get(v___x_6386_, 0);
                        v_err_6399_ = crate::leanh::lean_ctor_get(v___x_6386_, 1);
                        v_isSharedCheck_6406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6386_)) as u8;
                        if v_isSharedCheck_6406_ == 0 {
                            v___x_6401_ = v___x_6386_;
                            v_isShared_6402_ = v_isSharedCheck_6406_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_6399_);
                            crate::leanh::lean_inc(v_pos_6398_);
                            crate::leanh::lean_dec(v___x_6386_);
                            v___x_6401_ = crate::leanh::lean_box(0);
                            v_isShared_6402_ = v_isSharedCheck_6406_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_6378_);
                    v_pos_6407_ = crate::leanh::lean_ctor_get(v___x_6382_, 0);
                    v_err_6408_ = crate::leanh::lean_ctor_get(v___x_6382_, 1);
                    v_isSharedCheck_6415_ = (!crate::leanh::lean_is_exclusive(v___x_6382_)) as u8;
                    if v_isSharedCheck_6415_ == 0 {
                        v___x_6410_ = v___x_6382_;
                        v_isShared_6411_ = v_isSharedCheck_6415_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6408_);
                        crate::leanh::lean_inc(v_pos_6407_);
                        crate::leanh::lean_dec(v___x_6382_);
                        v___x_6410_ = crate::leanh::lean_box(0);
                        v_isShared_6411_ = v_isSharedCheck_6415_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6392_, 0, v_res_6384_);
                v___x_6393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6393_, 0, v___x_6392_);
                crate::leanh::lean_ctor_set(v___x_6393_, 1, v_res_6388_);
                if v_isShared_6391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6390_, 1, v___x_6393_);
                    v___x_6395_ = v___x_6390_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_pos_6387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6396_, 1, v___x_6393_);
                    v___x_6395_ = v_reuseFailAlloc_6396_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6395_;
            }
            4 => {
                if v_isShared_6402_ == 0 {
                    v___x_6404_ = v___x_6401_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6405_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_pos_6398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6405_, 1, v_err_6399_);
                    v___x_6404_ = v_reuseFailAlloc_6405_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6404_;
            }
            6 => {
                if v_isShared_6411_ == 0 {
                    v___x_6413_ = v___x_6410_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6414_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_pos_6407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 1, v_err_6408_);
                    v___x_6413_ = v_reuseFailAlloc_6414_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6413_;
            }
            8 => {
                v_idx_6424_ = crate::leanh::lean_ctor_get(v_a_6379_, 1);
                v___x_6425_ = lean_nat_dec_eq(v_idx_6424_, v_idx_6424_);
                if v___x_6425_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6378_);
                    if v_isShared_6423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6422_, 0, v_a_6379_);
                        v___x_6427_ = v___x_6422_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6428_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_a_6379_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6428_, 1, v_err_6420_);
                        v___x_6427_ = v_reuseFailAlloc_6428_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6422_);
                    crate::leanh::lean_dec(v_err_6420_);
                    v___x_6429_ = 0;
                    v___x_6430_ = l_Std_Http_URI_Parser_parsePath(
                        v_config_6378_,
                        v___x_6429_,
                        v___x_6425_,
                        v_a_6379_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6430_) == 0 {
                        v_pos_6431_ = crate::leanh::lean_ctor_get(v___x_6430_, 0);
                        v_res_6432_ = crate::leanh::lean_ctor_get(v___x_6430_, 1);
                        v_isSharedCheck_6441_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6430_)) as u8;
                        if v_isSharedCheck_6441_ == 0 {
                            v___x_6434_ = v___x_6430_;
                            v_isShared_6435_ = v_isSharedCheck_6441_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_6432_);
                            crate::leanh::lean_inc(v_pos_6431_);
                            crate::leanh::lean_dec(v___x_6430_);
                            v___x_6434_ = crate::leanh::lean_box(0);
                            v_isShared_6435_ = v_isSharedCheck_6441_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_pos_6442_ = crate::leanh::lean_ctor_get(v___x_6430_, 0);
                        v_err_6443_ = crate::leanh::lean_ctor_get(v___x_6430_, 1);
                        v_isSharedCheck_6450_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6430_)) as u8;
                        if v_isSharedCheck_6450_ == 0 {
                            v___x_6445_ = v___x_6430_;
                            v_isShared_6446_ = v_isSharedCheck_6450_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_6443_);
                            crate::leanh::lean_inc(v_pos_6442_);
                            crate::leanh::lean_dec(v___x_6430_);
                            v___x_6445_ = crate::leanh::lean_box(0);
                            v_isShared_6446_ = v_isSharedCheck_6450_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_6427_;
            }
            10 => {
                v___x_6436_ = crate::leanh::lean_box(0);
                v___x_6437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6437_, 0, v___x_6436_);
                crate::leanh::lean_ctor_set(v___x_6437_, 1, v_res_6432_);
                if v_isShared_6435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6434_, 1, v___x_6437_);
                    v___x_6439_ = v___x_6434_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_pos_6431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 1, v___x_6437_);
                    v___x_6439_ = v_reuseFailAlloc_6440_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6439_;
            }
            12 => {
                if v_isShared_6446_ == 0 {
                    v___x_6448_ = v___x_6445_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_pos_6442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 1, v_err_6443_);
                    v___x_6448_ = v_reuseFailAlloc_6449_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6453_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
    v___x_6454_ = lean_uint8_to_nat(v___x_6453_);
    return v___x_6454_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__0_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__0,
    );
    v___x_6456_ = l_Nat_reprFast(v___x_6455_);
    return v___x_6456_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__1_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__1,
    );
    v___x_6458_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_6459_ = lean_string_append(v___x_6458_, v___x_6457_);
    return v___x_6459_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6460_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_6461_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__2_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__2,
    );
    v___x_6462_ = lean_string_append(v___x_6461_, v___x_6460_);
    return v___x_6462_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__3_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__3,
    );
    v___x_6464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6464_, 0, v___x_6463_);
    return v___x_6464_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_6468_: u8 = 0;
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6468_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
    v___x_6469_ = lean_uint8_to_nat(v___x_6468_);
    return v___x_6469_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__7_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__7,
    );
    v___x_6471_ = l_Nat_reprFast(v___x_6470_);
    return v___x_6471_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6472_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__8),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__8_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__8,
    );
    v___x_6473_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_6474_ = lean_string_append(v___x_6473_, v___x_6472_);
    return v___x_6474_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6475_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_6476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__9),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__9_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__9,
    );
    v___x_6477_ = lean_string_append(v___x_6476_, v___x_6475_);
    return v___x_6477_;
}
pub unsafe fn _init_l_Std_Http_URI_Parser_parseURI___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__10),
        core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__10_once),
        _init_l_Std_Http_URI_Parser_parseURI___closed__10,
    );
    v___x_6479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6479_, 0, v___x_6478_);
    return v___x_6479_;
}
pub unsafe fn l_Std_Http_URI_Parser_parseURI(
    mut v_config_6480_: *mut crate::leanh::LeanObject,
    mut v_a_6481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6487_: u8 = 0;
    let mut v_array_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: u8 = 0;
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: u8 = 0;
    let mut v_got_6497_: u8 = 0;
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6505_: u8 = 0;
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6515_: u8 = 0;
    let mut v_fst_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6520_: u8 = 0;
    let mut v___y_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: u8 = 0;
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: u8 = 0;
    let mut v_got_6555_: u8 = 0;
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6560_: u8 = 0;
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v_unused_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: u8 = 0;
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: u8 = 0;
    let mut v_got_6590_: u8 = 0;
    let mut v___x_6591_: u8 = 0;
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6595_: u8 = 0;
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6606_: u8 = 0;
    let mut v_unused_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut v_pos_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6615_: u8 = 0;
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6619_: u8 = 0;
    let mut v_reuseFailAlloc_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6621_: u8 = 0;
    let mut v_unused_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6624_: u8 = 0;
    let mut v_pos_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6482_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(
                        v_config_6480_,
                        v_a_6481_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6482_) == 0 {
                    v_pos_6483_ = crate::leanh::lean_ctor_get(v___x_6482_, 0);
                    v_res_6484_ = crate::leanh::lean_ctor_get(v___x_6482_, 1);
                    v_isSharedCheck_6624_ = (!crate::leanh::lean_is_exclusive(v___x_6482_)) as u8;
                    if v_isSharedCheck_6624_ == 0 {
                        v___x_6486_ = v___x_6482_;
                        v_isShared_6487_ = v_isSharedCheck_6624_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_6484_);
                        crate::leanh::lean_inc(v_pos_6483_);
                        crate::leanh::lean_dec(v___x_6482_);
                        v___x_6486_ = crate::leanh::lean_box(0);
                        v_isShared_6487_ = v_isSharedCheck_6624_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_6480_);
                    v_pos_6625_ = crate::leanh::lean_ctor_get(v___x_6482_, 0);
                    v_err_6626_ = crate::leanh::lean_ctor_get(v___x_6482_, 1);
                    v_isSharedCheck_6633_ = (!crate::leanh::lean_is_exclusive(v___x_6482_)) as u8;
                    if v_isSharedCheck_6633_ == 0 {
                        v___x_6628_ = v___x_6482_;
                        v_isShared_6629_ = v_isSharedCheck_6633_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6626_);
                        crate::leanh::lean_inc(v_pos_6625_);
                        crate::leanh::lean_dec(v___x_6482_);
                        v___x_6628_ = crate::leanh::lean_box(0);
                        v_isShared_6629_ = v_isSharedCheck_6633_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v_array_6488_ = crate::leanh::lean_ctor_get(v_pos_6483_, 0);
                v_idx_6489_ = crate::leanh::lean_ctor_get(v_pos_6483_, 1);
                v___x_6490_ = lean_byte_array_size(v_array_6488_);
                v___x_6491_ = lean_nat_dec_lt(v_idx_6489_, v___x_6490_);
                if v___x_6491_ == 0 {
                    crate::leanh::lean_dec(v_res_6484_);
                    crate::leanh::lean_dec_ref(v_config_6480_);
                    v___x_6492_ = crate::leanh::lean_box(0);
                    if v_isShared_6487_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6486_, 1);
                        crate::leanh::lean_ctor_set(v___x_6486_, 1, v___x_6492_);
                        v___x_6494_ = v___x_6486_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6495_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_pos_6483_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6495_, 1, v___x_6492_);
                        v___x_6494_ = v_reuseFailAlloc_6495_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6496_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v_got_6497_ = lean_byte_array_fget(v_array_6488_, v_idx_6489_);
                    v___x_6498_ = lean_uint8_dec_eq(v_got_6497_, v___x_6496_);
                    if v___x_6498_ == 0 {
                        crate::leanh::lean_dec(v_res_6484_);
                        crate::leanh::lean_dec_ref(v_config_6480_);
                        v___x_6499_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                        if v_isShared_6487_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6486_, 1);
                            crate::leanh::lean_ctor_set(v___x_6486_, 1, v___x_6499_);
                            v___x_6501_ = v___x_6486_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6502_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_pos_6483_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6502_, 1, v___x_6499_);
                            v___x_6501_ = v_reuseFailAlloc_6502_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_idx_6489_);
                        crate::leanh::lean_inc_ref(v_array_6488_);
                        v_isSharedCheck_6621_ =
                            (!crate::leanh::lean_is_exclusive(v_pos_6483_)) as u8;
                        if v_isSharedCheck_6621_ == 0 {
                            v_unused_6622_ = crate::leanh::lean_ctor_get(v_pos_6483_, 1);
                            crate::leanh::lean_dec(v_unused_6622_);
                            v_unused_6623_ = crate::leanh::lean_ctor_get(v_pos_6483_, 0);
                            crate::leanh::lean_dec(v_unused_6623_);
                            v___x_6504_ = v_pos_6483_;
                            v_isShared_6505_ = v_isSharedCheck_6621_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_pos_6483_);
                            v___x_6504_ = crate::leanh::lean_box(0);
                            v_isShared_6505_ = v_isSharedCheck_6621_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6494_;
            }
            3 => {
                return v___x_6501_;
            }
            4 => {
                v___x_6506_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6507_ = lean_nat_add(v_idx_6489_, v___x_6506_);
                crate::leanh::lean_dec(v_idx_6489_);
                if v_isShared_6505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6504_, 1, v___x_6507_);
                    v___x_6509_ = v___x_6504_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6620_, 0, v_array_6488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6620_, 1, v___x_6507_);
                    v___x_6509_ = v_reuseFailAlloc_6620_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_config_6480_);
                v___x_6510_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(
                        v_config_6480_,
                        v___x_6509_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6510_) == 0 {
                    v_res_6511_ = crate::leanh::lean_ctor_get(v___x_6510_, 1);
                    v_pos_6512_ = crate::leanh::lean_ctor_get(v___x_6510_, 0);
                    v_isSharedCheck_6610_ = (!crate::leanh::lean_is_exclusive(v___x_6510_)) as u8;
                    if v_isSharedCheck_6610_ == 0 {
                        v___x_6514_ = v___x_6510_;
                        v_isShared_6515_ = v_isSharedCheck_6610_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_6511_);
                        crate::leanh::lean_inc(v_pos_6512_);
                        crate::leanh::lean_dec(v___x_6510_);
                        v___x_6514_ = crate::leanh::lean_box(0);
                        v_isShared_6515_ = v_isSharedCheck_6610_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6486_);
                    crate::leanh::lean_dec(v_res_6484_);
                    crate::leanh::lean_dec_ref(v_config_6480_);
                    v_pos_6611_ = crate::leanh::lean_ctor_get(v___x_6510_, 0);
                    v_err_6612_ = crate::leanh::lean_ctor_get(v___x_6510_, 1);
                    v_isSharedCheck_6619_ = (!crate::leanh::lean_is_exclusive(v___x_6510_)) as u8;
                    if v_isSharedCheck_6619_ == 0 {
                        v___x_6614_ = v___x_6510_;
                        v_isShared_6615_ = v_isSharedCheck_6619_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6612_);
                        crate::leanh::lean_inc(v_pos_6611_);
                        crate::leanh::lean_dec(v___x_6510_);
                        v___x_6614_ = crate::leanh::lean_box(0);
                        v_isShared_6615_ = v_isSharedCheck_6619_;
                        state = 20;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_6516_ = crate::leanh::lean_ctor_get(v_res_6511_, 0);
                v_snd_6517_ = crate::leanh::lean_ctor_get(v_res_6511_, 1);
                v_isSharedCheck_6609_ = (!crate::leanh::lean_is_exclusive(v_res_6511_)) as u8;
                if v_isSharedCheck_6609_ == 0 {
                    v___x_6519_ = v_res_6511_;
                    v_isShared_6520_ = v_isSharedCheck_6609_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6517_);
                    crate::leanh::lean_inc(v_fst_6516_);
                    crate::leanh::lean_dec(v_res_6511_);
                    v___x_6519_ = crate::leanh::lean_box(0);
                    v_isShared_6520_ = v_isSharedCheck_6609_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_array_6575_ = crate::leanh::lean_ctor_get(v_pos_6512_, 0);
                v_idx_6576_ = crate::leanh::lean_ctor_get(v_pos_6512_, 1);
                crate::leanh::lean_inc(v_idx_6576_);
                v___x_6586_ = lean_byte_array_size(v_array_6575_);
                v___x_6587_ = lean_nat_dec_lt(v_idx_6576_, v___x_6586_);
                if v___x_6587_ == 0 {
                    v___x_6588_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_idx_6576_);
                    v_pos_6578_ = v_pos_6512_;
                    v_idx_6579_ = v_idx_6576_;
                    v_err_6580_ = v___x_6588_;
                    state = 16;
                    continue;
                } else {
                    v___x_6589_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                    v_got_6590_ = lean_byte_array_fget(v_array_6575_, v_idx_6576_);
                    v___x_6591_ = lean_uint8_dec_eq(v_got_6590_, v___x_6589_);
                    if v___x_6591_ == 0 {
                        v___x_6592_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_Parser_parseURI___closed__11_once
                            ),
                            _init_l_Std_Http_URI_Parser_parseURI___closed__11,
                        );
                        crate::leanh::lean_inc(v_idx_6576_);
                        v_pos_6578_ = v_pos_6512_;
                        v_idx_6579_ = v_idx_6576_;
                        v_err_6580_ = v___x_6592_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_array_6575_);
                        v_isSharedCheck_6606_ =
                            (!crate::leanh::lean_is_exclusive(v_pos_6512_)) as u8;
                        if v_isSharedCheck_6606_ == 0 {
                            v_unused_6607_ = crate::leanh::lean_ctor_get(v_pos_6512_, 1);
                            crate::leanh::lean_dec(v_unused_6607_);
                            v_unused_6608_ = crate::leanh::lean_ctor_get(v_pos_6512_, 0);
                            crate::leanh::lean_dec(v_unused_6608_);
                            v___x_6594_ = v_pos_6512_;
                            v_isShared_6595_ = v_isSharedCheck_6606_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_pos_6512_);
                            v___x_6594_ = crate::leanh::lean_box(0);
                            v_isShared_6595_ = v_isSharedCheck_6606_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_6525_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6525_, 0, v_res_6484_);
                crate::leanh::lean_ctor_set(v___x_6525_, 1, v_fst_6516_);
                crate::leanh::lean_ctor_set(v___x_6525_, 2, v_snd_6517_);
                crate::leanh::lean_ctor_set(v___x_6525_, 3, v___y_6522_);
                crate::leanh::lean_ctor_set(v___x_6525_, 4, v_res_6524_);
                if v_isShared_6515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6514_, 1, v___x_6525_);
                    crate::leanh::lean_ctor_set(v___x_6514_, 0, v_pos_6523_);
                    v___x_6527_ = v___x_6514_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_pos_6523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 1, v___x_6525_);
                    v___x_6527_ = v_reuseFailAlloc_6528_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6527_;
            }
            10 => {
                v___x_6535_ = lean_nat_dec_eq(v_idx_6531_, v_idx_6533_);
                crate::leanh::lean_dec(v_idx_6533_);
                crate::leanh::lean_dec(v_idx_6531_);
                if v___x_6535_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6530_);
                    crate::leanh::lean_dec(v_snd_6517_);
                    crate::leanh::lean_dec(v_fst_6516_);
                    crate::leanh::lean_del_object(v___x_6514_);
                    crate::leanh::lean_dec(v_res_6484_);
                    if v_isShared_6487_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6486_, 1);
                        crate::leanh::lean_ctor_set(v___x_6486_, 1, v_err_6534_);
                        crate::leanh::lean_ctor_set(v___x_6486_, 0, v_pos_6532_);
                        v___x_6537_ = v___x_6486_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6538_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_pos_6532_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6538_, 1, v_err_6534_);
                        v___x_6537_ = v_reuseFailAlloc_6538_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_6534_);
                    crate::leanh::lean_del_object(v___x_6486_);
                    v___x_6539_ = crate::leanh::lean_box(0);
                    v___y_6522_ = v___y_6530_;
                    v_pos_6523_ = v_pos_6532_;
                    v_res_6524_ = v___x_6539_;
                    state = 8;
                    continue;
                }
            }
            11 => {
                return v___x_6537_;
            }
            12 => {
                v_idx_6545_ = crate::leanh::lean_ctor_get(v_pos_6543_, 1);
                crate::leanh::lean_inc(v_idx_6545_);
                v___y_6530_ = v___y_6541_;
                v_idx_6531_ = v_idx_6542_;
                v_pos_6532_ = v_pos_6543_;
                v_idx_6533_ = v_idx_6545_;
                v_err_6534_ = v_err_6544_;
                state = 10;
                continue;
            }
            13 => {
                v_array_6549_ = crate::leanh::lean_ctor_get(v___y_6547_, 0);
                v_idx_6550_ = crate::leanh::lean_ctor_get(v___y_6547_, 1);
                crate::leanh::lean_inc(v_idx_6550_);
                v___x_6551_ = lean_byte_array_size(v_array_6549_);
                v___x_6552_ = lean_nat_dec_lt(v_idx_6550_, v___x_6551_);
                if v___x_6552_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6480_);
                    v___x_6553_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_idx_6550_);
                    v___y_6530_ = v___y_6548_;
                    v_idx_6531_ = v_idx_6550_;
                    v_pos_6532_ = v___y_6547_;
                    v_idx_6533_ = v_idx_6550_;
                    v_err_6534_ = v___x_6553_;
                    state = 10;
                    continue;
                } else {
                    v___x_6554_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
                    v_got_6555_ = lean_byte_array_fget(v_array_6549_, v_idx_6550_);
                    v___x_6556_ = lean_uint8_dec_eq(v_got_6555_, v___x_6554_);
                    if v___x_6556_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_6480_);
                        v___x_6557_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_Parser_parseURI___closed__4_once
                            ),
                            _init_l_Std_Http_URI_Parser_parseURI___closed__4,
                        );
                        crate::leanh::lean_inc(v_idx_6550_);
                        v___y_6530_ = v___y_6548_;
                        v_idx_6531_ = v_idx_6550_;
                        v_pos_6532_ = v___y_6547_;
                        v_idx_6533_ = v_idx_6550_;
                        v_err_6534_ = v___x_6557_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_array_6549_);
                        v_isSharedCheck_6572_ =
                            (!crate::leanh::lean_is_exclusive(v___y_6547_)) as u8;
                        if v_isSharedCheck_6572_ == 0 {
                            v_unused_6573_ = crate::leanh::lean_ctor_get(v___y_6547_, 1);
                            crate::leanh::lean_dec(v_unused_6573_);
                            v_unused_6574_ = crate::leanh::lean_ctor_get(v___y_6547_, 0);
                            crate::leanh::lean_dec(v_unused_6574_);
                            v___x_6559_ = v___y_6547_;
                            v_isShared_6560_ = v_isSharedCheck_6572_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_6547_);
                            v___x_6559_ = crate::leanh::lean_box(0);
                            v_isShared_6560_ = v_isSharedCheck_6572_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                v___x_6561_ = lean_nat_add(v_idx_6550_, v___x_6506_);
                if v_isShared_6560_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6559_, 1, v___x_6561_);
                    v___x_6563_ = v___x_6559_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_array_6549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 1, v___x_6561_);
                    v___x_6563_ = v_reuseFailAlloc_6571_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_6564_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(
                        v_config_6480_,
                        v___x_6563_,
                    );
                crate::leanh::lean_dec_ref(v_config_6480_);
                if crate::leanh::lean_obj_tag(v___x_6564_) == 0 {
                    v_pos_6565_ = crate::leanh::lean_ctor_get(v___x_6564_, 0);
                    crate::leanh::lean_inc(v_pos_6565_);
                    v_res_6566_ = crate::leanh::lean_ctor_get(v___x_6564_, 1);
                    crate::leanh::lean_inc(v_res_6566_);
                    crate::leanh::lean_dec_ref_known(v___x_6564_, 2);
                    v___x_6567_ = l_Std_Http_URI_EncodedFragment_decode(v_res_6566_);
                    crate::leanh::lean_dec(v_res_6566_);
                    if crate::leanh::lean_obj_tag(v___x_6567_) == 1 {
                        crate::leanh::lean_dec(v_idx_6550_);
                        crate::leanh::lean_del_object(v___x_6486_);
                        v___y_6522_ = v___y_6548_;
                        v_pos_6523_ = v_pos_6565_;
                        v_res_6524_ = v___x_6567_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6567_);
                        v___x_6568_ = l_Std_Http_URI_Parser_parseURI___closed__6;
                        v___y_6541_ = v___y_6548_;
                        v_idx_6542_ = v_idx_6550_;
                        v_pos_6543_ = v_pos_6565_;
                        v_err_6544_ = v___x_6568_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_pos_6569_ = crate::leanh::lean_ctor_get(v___x_6564_, 0);
                    crate::leanh::lean_inc(v_pos_6569_);
                    v_err_6570_ = crate::leanh::lean_ctor_get(v___x_6564_, 1);
                    crate::leanh::lean_inc(v_err_6570_);
                    crate::leanh::lean_dec_ref_known(v___x_6564_, 2);
                    v___y_6541_ = v___y_6548_;
                    v_idx_6542_ = v_idx_6550_;
                    v_pos_6543_ = v_pos_6569_;
                    v_err_6544_ = v_err_6570_;
                    state = 12;
                    continue;
                }
            }
            16 => {
                v___x_6581_ = lean_nat_dec_eq(v_idx_6576_, v_idx_6579_);
                crate::leanh::lean_dec(v_idx_6579_);
                crate::leanh::lean_dec(v_idx_6576_);
                if v___x_6581_ == 0 {
                    crate::leanh::lean_dec(v_snd_6517_);
                    crate::leanh::lean_dec(v_fst_6516_);
                    crate::leanh::lean_del_object(v___x_6514_);
                    crate::leanh::lean_del_object(v___x_6486_);
                    crate::leanh::lean_dec(v_res_6484_);
                    crate::leanh::lean_dec_ref(v_config_6480_);
                    if v_isShared_6520_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6519_, 1);
                        crate::leanh::lean_ctor_set(v___x_6519_, 1, v_err_6580_);
                        crate::leanh::lean_ctor_set(v___x_6519_, 0, v_pos_6578_);
                        v___x_6583_ = v___x_6519_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_6584_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_pos_6578_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6584_, 1, v_err_6580_);
                        v___x_6583_ = v_reuseFailAlloc_6584_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_6580_);
                    crate::leanh::lean_del_object(v___x_6519_);
                    v___x_6585_ = l_Std_Http_URI_Query_empty;
                    v___y_6547_ = v_pos_6578_;
                    v___y_6548_ = v___x_6585_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                return v___x_6583_;
            }
            18 => {
                v___x_6596_ = lean_nat_add(v_idx_6576_, v___x_6506_);
                if v_isShared_6595_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6594_, 1, v___x_6596_);
                    v___x_6598_ = v___x_6594_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6605_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6605_, 0, v_array_6575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6605_, 1, v___x_6596_);
                    v___x_6598_ = v_reuseFailAlloc_6605_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_inc_ref(v_config_6480_);
                v___x_6599_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(
                        v_config_6480_,
                        v___x_6598_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6599_) == 0 {
                    crate::leanh::lean_dec(v_idx_6576_);
                    crate::leanh::lean_del_object(v___x_6519_);
                    v_pos_6600_ = crate::leanh::lean_ctor_get(v___x_6599_, 0);
                    crate::leanh::lean_inc(v_pos_6600_);
                    v_res_6601_ = crate::leanh::lean_ctor_get(v___x_6599_, 1);
                    crate::leanh::lean_inc(v_res_6601_);
                    crate::leanh::lean_dec_ref_known(v___x_6599_, 2);
                    v___y_6547_ = v_pos_6600_;
                    v___y_6548_ = v_res_6601_;
                    state = 13;
                    continue;
                } else {
                    v_pos_6602_ = crate::leanh::lean_ctor_get(v___x_6599_, 0);
                    crate::leanh::lean_inc(v_pos_6602_);
                    v_err_6603_ = crate::leanh::lean_ctor_get(v___x_6599_, 1);
                    crate::leanh::lean_inc(v_err_6603_);
                    crate::leanh::lean_dec_ref_known(v___x_6599_, 2);
                    v_idx_6604_ = crate::leanh::lean_ctor_get(v_pos_6602_, 1);
                    crate::leanh::lean_inc(v_idx_6604_);
                    v_pos_6578_ = v_pos_6602_;
                    v_idx_6579_ = v_idx_6604_;
                    v_err_6580_ = v_err_6603_;
                    state = 16;
                    continue;
                }
            }
            20 => {
                if v_isShared_6615_ == 0 {
                    v___x_6617_ = v___x_6614_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6618_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6618_, 0, v_pos_6611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6618_, 1, v_err_6612_);
                    v___x_6617_ = v_reuseFailAlloc_6618_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6617_;
            }
            22 => {
                if v_isShared_6629_ == 0 {
                    v___x_6631_ = v___x_6628_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6632_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_pos_6625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 1, v_err_6626_);
                    v___x_6631_ = v_reuseFailAlloc_6632_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6634_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
    v___x_6635_ = lean_uint8_to_nat(v___x_6634_);
    return v___x_6635_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6636_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
    v___x_6637_ = l_Nat_reprFast(v___x_6636_);
    return v___x_6637_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
    v___x_6639_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2;
    v___x_6640_ = lean_string_append(v___x_6639_, v___x_6638_);
    return v___x_6640_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6641_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6;
    v___x_6642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
    v___x_6643_ = lean_string_append(v___x_6642_, v___x_6641_);
    return v___x_6643_;
}
pub unsafe fn _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
    v___x_6645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6645_, 0, v___x_6644_);
    return v___x_6645_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(
    mut v_a_6646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: u8 = 0;
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: u8 = 0;
    let mut v_got_6654_: u8 = 0;
    let mut v___x_6655_: u8 = 0;
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6660_: u8 = 0;
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6668_: u8 = 0;
    let mut v_unused_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_6647_ = crate::leanh::lean_ctor_get(v_a_6646_, 0);
                v_idx_6648_ = crate::leanh::lean_ctor_get(v_a_6646_, 1);
                v___x_6649_ = lean_byte_array_size(v_array_6647_);
                v___x_6650_ = lean_nat_dec_lt(v_idx_6648_, v___x_6649_);
                if v___x_6650_ == 0 {
                    v___x_6651_ = crate::leanh::lean_box(0);
                    v___x_6652_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6652_, 0, v_a_6646_);
                    crate::leanh::lean_ctor_set(v___x_6652_, 1, v___x_6651_);
                    return v___x_6652_;
                } else {
                    v___x_6653_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
                    v_got_6654_ = lean_byte_array_fget(v_array_6647_, v_idx_6648_);
                    v___x_6655_ = lean_uint8_dec_eq(v_got_6654_, v___x_6653_);
                    if v___x_6655_ == 0 {
                        v___x_6656_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
                        v___x_6657_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6657_, 0, v_a_6646_);
                        crate::leanh::lean_ctor_set(v___x_6657_, 1, v___x_6656_);
                        return v___x_6657_;
                    } else {
                        crate::leanh::lean_inc(v_idx_6648_);
                        crate::leanh::lean_inc_ref(v_array_6647_);
                        v_isSharedCheck_6668_ = (!crate::leanh::lean_is_exclusive(v_a_6646_)) as u8;
                        if v_isSharedCheck_6668_ == 0 {
                            v_unused_6669_ = crate::leanh::lean_ctor_get(v_a_6646_, 1);
                            crate::leanh::lean_dec(v_unused_6669_);
                            v_unused_6670_ = crate::leanh::lean_ctor_get(v_a_6646_, 0);
                            crate::leanh::lean_dec(v_unused_6670_);
                            v___x_6659_ = v_a_6646_;
                            v_isShared_6660_ = v_isSharedCheck_6668_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6646_);
                            v___x_6659_ = crate::leanh::lean_box(0);
                            v_isShared_6660_ = v_isSharedCheck_6668_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6661_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6662_ = lean_nat_add(v_idx_6648_, v___x_6661_);
                crate::leanh::lean_dec(v_idx_6648_);
                if v_isShared_6660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6659_, 1, v___x_6662_);
                    v___x_6664_ = v___x_6659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6667_, 0, v_array_6647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6667_, 1, v___x_6662_);
                    v___x_6664_ = v_reuseFailAlloc_6667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6665_ = crate::leanh::lean_box(3);
                v___x_6666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6666_, 0, v___x_6664_);
                crate::leanh::lean_ctor_set(v___x_6666_, 1, v___x_6665_);
                return v___x_6666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(
    mut v_config_6674_: *mut crate::leanh::LeanObject,
    mut v_a_6675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: u8 = 0;
    let mut v___x_6683_: u8 = 0;
    let mut v___x_6684_: u8 = 0;
    let mut v___x_6685_: u8 = 0;
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v_pos_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: u8 = 0;
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: u8 = 0;
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: u8 = 0;
    let mut v_got_6712_: u8 = 0;
    let mut v___x_6713_: u8 = 0;
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6717_: u8 = 0;
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6730_: u8 = 0;
    let mut v_unused_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_err_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6737_: u8 = 0;
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6741_: u8 = 0;
    let mut v_unused_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_6679_ = crate::leanh::lean_ctor_get(v_a_6675_, 0);
                v_idx_6680_ = crate::leanh::lean_ctor_get(v_a_6675_, 1);
                v___x_6681_ = lean_byte_array_size(v_array_6679_);
                v___x_6682_ = lean_nat_dec_lt(v_idx_6680_, v___x_6681_);
                if v___x_6682_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6674_);
                    state = 1;
                    continue;
                } else {
                    v___x_6683_ = lean_byte_array_fget(v_array_6679_, v_idx_6680_);
                    v___x_6684_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                    v___x_6685_ = lean_uint8_dec_eq(v___x_6683_, v___x_6684_);
                    if v___x_6685_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_6674_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_6685_ == 0 {
                            crate::leanh::lean_dec_ref(v_config_6674_);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_a_6675_);
                            crate::leanh::lean_inc_ref(v_config_6674_);
                            v___x_6686_ = l_Std_Http_URI_Parser_parsePath(
                                v_config_6674_,
                                v___x_6685_,
                                v___x_6685_,
                                v_a_6675_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6686_) == 0 {
                                v_pos_6687_ = crate::leanh::lean_ctor_get(v___x_6686_, 0);
                                v_res_6688_ = crate::leanh::lean_ctor_get(v___x_6686_, 1);
                                v_isSharedCheck_6733_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6686_)) as u8;
                                if v_isSharedCheck_6733_ == 0 {
                                    v___x_6690_ = v___x_6686_;
                                    v_isShared_6691_ = v_isSharedCheck_6733_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_res_6688_);
                                    crate::leanh::lean_inc(v_pos_6687_);
                                    crate::leanh::lean_dec(v___x_6686_);
                                    v___x_6690_ = crate::leanh::lean_box(0);
                                    v_isShared_6691_ = v_isSharedCheck_6733_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_config_6674_);
                                v_err_6734_ = crate::leanh::lean_ctor_get(v___x_6686_, 1);
                                v_isSharedCheck_6741_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6686_)) as u8;
                                if v_isSharedCheck_6741_ == 0 {
                                    v_unused_6742_ = crate::leanh::lean_ctor_get(v___x_6686_, 0);
                                    crate::leanh::lean_dec(v_unused_6742_);
                                    v___x_6736_ = v___x_6686_;
                                    v_isShared_6737_ = v_isSharedCheck_6741_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_err_6734_);
                                    crate::leanh::lean_dec(v___x_6686_);
                                    v___x_6736_ = crate::leanh::lean_box(0);
                                    v_isShared_6737_ = v_isSharedCheck_6741_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6677_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1;
                v___x_6678_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6678_, 0, v_a_6675_);
                crate::leanh::lean_ctor_set(v___x_6678_, 1, v___x_6677_);
                return v___x_6678_;
            }
            2 => {
                v_array_6699_ = crate::leanh::lean_ctor_get(v_pos_6687_, 0);
                v_idx_6700_ = crate::leanh::lean_ctor_get(v_pos_6687_, 1);
                crate::leanh::lean_inc(v_idx_6700_);
                v___x_6708_ = lean_byte_array_size(v_array_6699_);
                v___x_6709_ = lean_nat_dec_lt(v_idx_6700_, v___x_6708_);
                if v___x_6709_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6674_);
                    v___x_6710_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_idx_6700_);
                    v_pos_6702_ = v_pos_6687_;
                    v_idx_6703_ = v_idx_6700_;
                    v_err_6704_ = v___x_6710_;
                    state = 5;
                    continue;
                } else {
                    v___x_6711_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                    v_got_6712_ = lean_byte_array_fget(v_array_6699_, v_idx_6700_);
                    v___x_6713_ = lean_uint8_dec_eq(v_got_6712_, v___x_6711_);
                    if v___x_6713_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_6674_);
                        v___x_6714_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_Parser_parseURI___closed__11_once
                            ),
                            _init_l_Std_Http_URI_Parser_parseURI___closed__11,
                        );
                        crate::leanh::lean_inc(v_idx_6700_);
                        v_pos_6702_ = v_pos_6687_;
                        v_idx_6703_ = v_idx_6700_;
                        v_err_6704_ = v___x_6714_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_array_6699_);
                        v_isSharedCheck_6730_ =
                            (!crate::leanh::lean_is_exclusive(v_pos_6687_)) as u8;
                        if v_isSharedCheck_6730_ == 0 {
                            v_unused_6731_ = crate::leanh::lean_ctor_get(v_pos_6687_, 1);
                            crate::leanh::lean_dec(v_unused_6731_);
                            v_unused_6732_ = crate::leanh::lean_ctor_get(v_pos_6687_, 0);
                            crate::leanh::lean_dec(v_unused_6732_);
                            v___x_6716_ = v_pos_6687_;
                            v_isShared_6717_ = v_isSharedCheck_6730_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_pos_6687_);
                            v___x_6716_ = crate::leanh::lean_box(0);
                            v_isShared_6717_ = v_isSharedCheck_6730_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6695_, 0, v_res_6688_);
                crate::leanh::lean_ctor_set(v___x_6695_, 1, v_res_6694_);
                if v_isShared_6691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6690_, 1, v___x_6695_);
                    crate::leanh::lean_ctor_set(v___x_6690_, 0, v_pos_6693_);
                    v___x_6697_ = v___x_6690_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6698_, 0, v_pos_6693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6698_, 1, v___x_6695_);
                    v___x_6697_ = v_reuseFailAlloc_6698_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6697_;
            }
            5 => {
                v___x_6705_ = lean_nat_dec_eq(v_idx_6700_, v_idx_6703_);
                crate::leanh::lean_dec(v_idx_6703_);
                crate::leanh::lean_dec(v_idx_6700_);
                if v___x_6705_ == 0 {
                    crate::leanh::lean_dec_ref(v_pos_6702_);
                    crate::leanh::lean_del_object(v___x_6690_);
                    crate::leanh::lean_dec(v_res_6688_);
                    v___x_6706_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6706_, 0, v_a_6675_);
                    crate::leanh::lean_ctor_set(v___x_6706_, 1, v_err_6704_);
                    return v___x_6706_;
                } else {
                    crate::leanh::lean_dec(v_err_6704_);
                    crate::leanh::lean_dec_ref(v_a_6675_);
                    v___x_6707_ = crate::leanh::lean_box(0);
                    v_pos_6693_ = v_pos_6702_;
                    v_res_6694_ = v___x_6707_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_6718_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6719_ = lean_nat_add(v_idx_6700_, v___x_6718_);
                if v_isShared_6717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6716_, 1, v___x_6719_);
                    v___x_6721_ = v___x_6716_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6729_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_array_6699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 1, v___x_6719_);
                    v___x_6721_ = v_reuseFailAlloc_6729_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6722_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(
                        v_config_6674_,
                        v___x_6721_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6722_) == 0 {
                    crate::leanh::lean_dec(v_idx_6700_);
                    crate::leanh::lean_dec_ref(v_a_6675_);
                    v_pos_6723_ = crate::leanh::lean_ctor_get(v___x_6722_, 0);
                    crate::leanh::lean_inc(v_pos_6723_);
                    v_res_6724_ = crate::leanh::lean_ctor_get(v___x_6722_, 1);
                    crate::leanh::lean_inc(v_res_6724_);
                    crate::leanh::lean_dec_ref_known(v___x_6722_, 2);
                    v___x_6725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6725_, 0, v_res_6724_);
                    v_pos_6693_ = v_pos_6723_;
                    v_res_6694_ = v___x_6725_;
                    state = 3;
                    continue;
                } else {
                    v_pos_6726_ = crate::leanh::lean_ctor_get(v___x_6722_, 0);
                    crate::leanh::lean_inc(v_pos_6726_);
                    v_err_6727_ = crate::leanh::lean_ctor_get(v___x_6722_, 1);
                    crate::leanh::lean_inc(v_err_6727_);
                    crate::leanh::lean_dec_ref_known(v___x_6722_, 2);
                    v_idx_6728_ = crate::leanh::lean_ctor_get(v_pos_6726_, 1);
                    crate::leanh::lean_inc(v_idx_6728_);
                    v_pos_6702_ = v_pos_6726_;
                    v_idx_6703_ = v_idx_6728_;
                    v_err_6704_ = v_err_6727_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                if v_isShared_6737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6736_, 0, v_a_6675_);
                    v___x_6739_ = v___x_6736_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6740_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6740_, 1, v_err_6734_);
                    v___x_6739_ = v_reuseFailAlloc_6740_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(
    mut v_config_6743_: *mut crate::leanh::LeanObject,
    mut v_scheme_6744_: *mut crate::leanh::LeanObject,
    mut v_a_6745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: u8 = 0;
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v_got_6753_: u8 = 0;
    let mut v___x_6754_: u8 = 0;
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6759_: u8 = 0;
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6769_: u8 = 0;
    let mut v_fst_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6774_: u8 = 0;
    let mut v___y_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: u8 = 0;
    let mut v___x_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: u8 = 0;
    let mut v___x_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: u8 = 0;
    let mut v_got_6799_: u8 = 0;
    let mut v___x_6800_: u8 = 0;
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6804_: u8 = 0;
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6815_: u8 = 0;
    let mut v_unused_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6818_: u8 = 0;
    let mut v_isSharedCheck_6819_: u8 = 0;
    let mut v_pos_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6824_: u8 = 0;
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6828_: u8 = 0;
    let mut v_reuseFailAlloc_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6830_: u8 = 0;
    let mut v_unused_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_6746_ = crate::leanh::lean_ctor_get(v_a_6745_, 0);
                v_idx_6747_ = crate::leanh::lean_ctor_get(v_a_6745_, 1);
                v___x_6748_ = lean_byte_array_size(v_array_6746_);
                v___x_6749_ = lean_nat_dec_lt(v_idx_6747_, v___x_6748_);
                if v___x_6749_ == 0 {
                    crate::leanh::lean_dec_ref(v_scheme_6744_);
                    crate::leanh::lean_dec_ref(v_config_6743_);
                    v___x_6750_ = crate::leanh::lean_box(0);
                    v___x_6751_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6751_, 0, v_a_6745_);
                    crate::leanh::lean_ctor_set(v___x_6751_, 1, v___x_6750_);
                    return v___x_6751_;
                } else {
                    v___x_6752_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v_got_6753_ = lean_byte_array_fget(v_array_6746_, v_idx_6747_);
                    v___x_6754_ = lean_uint8_dec_eq(v_got_6753_, v___x_6752_);
                    if v___x_6754_ == 0 {
                        crate::leanh::lean_dec_ref(v_scheme_6744_);
                        crate::leanh::lean_dec_ref(v_config_6743_);
                        v___x_6755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                        v___x_6756_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6756_, 0, v_a_6745_);
                        crate::leanh::lean_ctor_set(v___x_6756_, 1, v___x_6755_);
                        return v___x_6756_;
                    } else {
                        crate::leanh::lean_inc(v_idx_6747_);
                        crate::leanh::lean_inc_ref(v_array_6746_);
                        v_isSharedCheck_6830_ = (!crate::leanh::lean_is_exclusive(v_a_6745_)) as u8;
                        if v_isSharedCheck_6830_ == 0 {
                            v_unused_6831_ = crate::leanh::lean_ctor_get(v_a_6745_, 1);
                            crate::leanh::lean_dec(v_unused_6831_);
                            v_unused_6832_ = crate::leanh::lean_ctor_get(v_a_6745_, 0);
                            crate::leanh::lean_dec(v_unused_6832_);
                            v___x_6758_ = v_a_6745_;
                            v_isShared_6759_ = v_isSharedCheck_6830_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6745_);
                            v___x_6758_ = crate::leanh::lean_box(0);
                            v_isShared_6759_ = v_isSharedCheck_6830_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6760_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6761_ = lean_nat_add(v_idx_6747_, v___x_6760_);
                crate::leanh::lean_dec(v_idx_6747_);
                if v_isShared_6759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6758_, 1, v___x_6761_);
                    v___x_6763_ = v___x_6758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_array_6746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6829_, 1, v___x_6761_);
                    v___x_6763_ = v_reuseFailAlloc_6829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_config_6743_);
                v___x_6764_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(
                        v_config_6743_,
                        v___x_6763_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6764_) == 0 {
                    v_res_6765_ = crate::leanh::lean_ctor_get(v___x_6764_, 1);
                    v_pos_6766_ = crate::leanh::lean_ctor_get(v___x_6764_, 0);
                    v_isSharedCheck_6819_ = (!crate::leanh::lean_is_exclusive(v___x_6764_)) as u8;
                    if v_isSharedCheck_6819_ == 0 {
                        v___x_6768_ = v___x_6764_;
                        v_isShared_6769_ = v_isSharedCheck_6819_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_6765_);
                        crate::leanh::lean_inc(v_pos_6766_);
                        crate::leanh::lean_dec(v___x_6764_);
                        v___x_6768_ = crate::leanh::lean_box(0);
                        v_isShared_6769_ = v_isSharedCheck_6819_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_scheme_6744_);
                    crate::leanh::lean_dec_ref(v_config_6743_);
                    v_pos_6820_ = crate::leanh::lean_ctor_get(v___x_6764_, 0);
                    v_err_6821_ = crate::leanh::lean_ctor_get(v___x_6764_, 1);
                    v_isSharedCheck_6828_ = (!crate::leanh::lean_is_exclusive(v___x_6764_)) as u8;
                    if v_isSharedCheck_6828_ == 0 {
                        v___x_6823_ = v___x_6764_;
                        v_isShared_6824_ = v_isSharedCheck_6828_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6821_);
                        crate::leanh::lean_inc(v_pos_6820_);
                        crate::leanh::lean_dec(v___x_6764_);
                        v___x_6823_ = crate::leanh::lean_box(0);
                        v_isShared_6824_ = v_isSharedCheck_6828_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6770_ = crate::leanh::lean_ctor_get(v_res_6765_, 0);
                v_snd_6771_ = crate::leanh::lean_ctor_get(v_res_6765_, 1);
                v_isSharedCheck_6818_ = (!crate::leanh::lean_is_exclusive(v_res_6765_)) as u8;
                if v_isSharedCheck_6818_ == 0 {
                    v___x_6773_ = v_res_6765_;
                    v_isShared_6774_ = v_isSharedCheck_6818_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6771_);
                    crate::leanh::lean_inc(v_fst_6770_);
                    crate::leanh::lean_dec(v_res_6765_);
                    v___x_6773_ = crate::leanh::lean_box(0);
                    v_isShared_6774_ = v_isSharedCheck_6818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_array_6784_ = crate::leanh::lean_ctor_get(v_pos_6766_, 0);
                v_idx_6785_ = crate::leanh::lean_ctor_get(v_pos_6766_, 1);
                crate::leanh::lean_inc(v_idx_6785_);
                v___x_6795_ = lean_byte_array_size(v_array_6784_);
                v___x_6796_ = lean_nat_dec_lt(v_idx_6785_, v___x_6795_);
                if v___x_6796_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6743_);
                    v___x_6797_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_idx_6785_);
                    v_pos_6787_ = v_pos_6766_;
                    v_idx_6788_ = v_idx_6785_;
                    v_err_6789_ = v___x_6797_;
                    state = 7;
                    continue;
                } else {
                    v___x_6798_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                    v_got_6799_ = lean_byte_array_fget(v_array_6784_, v_idx_6785_);
                    v___x_6800_ = lean_uint8_dec_eq(v_got_6799_, v___x_6798_);
                    if v___x_6800_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_6743_);
                        v___x_6801_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_Parser_parseURI___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_Parser_parseURI___closed__11_once
                            ),
                            _init_l_Std_Http_URI_Parser_parseURI___closed__11,
                        );
                        crate::leanh::lean_inc(v_idx_6785_);
                        v_pos_6787_ = v_pos_6766_;
                        v_idx_6788_ = v_idx_6785_;
                        v_err_6789_ = v___x_6801_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_array_6784_);
                        v_isSharedCheck_6815_ =
                            (!crate::leanh::lean_is_exclusive(v_pos_6766_)) as u8;
                        if v_isSharedCheck_6815_ == 0 {
                            v_unused_6816_ = crate::leanh::lean_ctor_get(v_pos_6766_, 1);
                            crate::leanh::lean_dec(v_unused_6816_);
                            v_unused_6817_ = crate::leanh::lean_ctor_get(v_pos_6766_, 0);
                            crate::leanh::lean_dec(v_unused_6817_);
                            v___x_6803_ = v_pos_6766_;
                            v_isShared_6804_ = v_isSharedCheck_6815_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_pos_6766_);
                            v___x_6803_ = crate::leanh::lean_box(0);
                            v_isShared_6804_ = v_isSharedCheck_6815_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_6778_ = crate::leanh::lean_box(0);
                v___x_6779_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6779_, 0, v_scheme_6744_);
                crate::leanh::lean_ctor_set(v___x_6779_, 1, v_fst_6770_);
                crate::leanh::lean_ctor_set(v___x_6779_, 2, v_snd_6771_);
                crate::leanh::lean_ctor_set(v___x_6779_, 3, v___y_6777_);
                crate::leanh::lean_ctor_set(v___x_6779_, 4, v___x_6778_);
                v___x_6780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6780_, 0, v___x_6779_);
                if v_isShared_6769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6768_, 1, v___x_6780_);
                    crate::leanh::lean_ctor_set(v___x_6768_, 0, v___y_6776_);
                    v___x_6782_ = v___x_6768_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6783_, 0, v___y_6776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6783_, 1, v___x_6780_);
                    v___x_6782_ = v_reuseFailAlloc_6783_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6782_;
            }
            7 => {
                v___x_6790_ = lean_nat_dec_eq(v_idx_6785_, v_idx_6788_);
                crate::leanh::lean_dec(v_idx_6788_);
                crate::leanh::lean_dec(v_idx_6785_);
                if v___x_6790_ == 0 {
                    crate::leanh::lean_dec(v_snd_6771_);
                    crate::leanh::lean_dec(v_fst_6770_);
                    crate::leanh::lean_del_object(v___x_6768_);
                    crate::leanh::lean_dec_ref(v_scheme_6744_);
                    if v_isShared_6774_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6773_, 1);
                        crate::leanh::lean_ctor_set(v___x_6773_, 1, v_err_6789_);
                        crate::leanh::lean_ctor_set(v___x_6773_, 0, v_pos_6787_);
                        v___x_6792_ = v___x_6773_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6793_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 0, v_pos_6787_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 1, v_err_6789_);
                        v___x_6792_ = v_reuseFailAlloc_6793_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_6789_);
                    crate::leanh::lean_del_object(v___x_6773_);
                    v___x_6794_ = l_Std_Http_URI_Query_empty;
                    v___y_6776_ = v_pos_6787_;
                    v___y_6777_ = v___x_6794_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                return v___x_6792_;
            }
            9 => {
                v___x_6805_ = lean_nat_add(v_idx_6785_, v___x_6760_);
                if v_isShared_6804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6803_, 1, v___x_6805_);
                    v___x_6807_ = v___x_6803_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6814_, 0, v_array_6784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6814_, 1, v___x_6805_);
                    v___x_6807_ = v_reuseFailAlloc_6814_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6808_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(
                        v_config_6743_,
                        v___x_6807_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6808_) == 0 {
                    crate::leanh::lean_dec(v_idx_6785_);
                    crate::leanh::lean_del_object(v___x_6773_);
                    v_pos_6809_ = crate::leanh::lean_ctor_get(v___x_6808_, 0);
                    crate::leanh::lean_inc(v_pos_6809_);
                    v_res_6810_ = crate::leanh::lean_ctor_get(v___x_6808_, 1);
                    crate::leanh::lean_inc(v_res_6810_);
                    crate::leanh::lean_dec_ref_known(v___x_6808_, 2);
                    v___y_6776_ = v_pos_6809_;
                    v___y_6777_ = v_res_6810_;
                    state = 5;
                    continue;
                } else {
                    v_pos_6811_ = crate::leanh::lean_ctor_get(v___x_6808_, 0);
                    crate::leanh::lean_inc(v_pos_6811_);
                    v_err_6812_ = crate::leanh::lean_ctor_get(v___x_6808_, 1);
                    crate::leanh::lean_inc(v_err_6812_);
                    crate::leanh::lean_dec_ref_known(v___x_6808_, 2);
                    v_idx_6813_ = crate::leanh::lean_ctor_get(v_pos_6811_, 1);
                    crate::leanh::lean_inc(v_idx_6813_);
                    v_pos_6787_ = v_pos_6811_;
                    v_idx_6788_ = v_idx_6813_;
                    v_err_6789_ = v_err_6812_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                if v_isShared_6824_ == 0 {
                    v___x_6826_ = v___x_6823_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_pos_6820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6827_, 1, v_err_6821_);
                    v___x_6826_ = v_reuseFailAlloc_6827_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(
    mut v_config_6841_: *mut crate::leanh::LeanObject,
    mut v_a_6842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6851_: u8 = 0;
    let mut v___y_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: u8 = 0;
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: u8 = 0;
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6881_: u8 = 0;
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: u8 = 0;
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: u8 = 0;
    let mut v_got_6887_: u8 = 0;
    let mut v___x_6888_: u8 = 0;
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: u8 = 0;
    let mut v___x_6894_: u8 = 0;
    let mut v___x_6895_: u8 = 0;
    let mut v___x_6896_: u8 = 0;
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: u8 = 0;
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: u8 = 0;
    let mut v_got_6910_: u8 = 0;
    let mut v___x_6911_: u8 = 0;
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6915_: u8 = 0;
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6926_: u8 = 0;
    let mut v_unused_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6936_: u8 = 0;
    let mut v_unused_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6939_: u8 = 0;
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: u8 = 0;
    let mut v___x_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: u8 = 0;
    let mut v_isSharedCheck_6944_: u8 = 0;
    let mut v_err_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6948_: u8 = 0;
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6952_: u8 = 0;
    let mut v_unused_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_6842_);
                v___x_6846_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(
                        v_config_6841_,
                        v_a_6842_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6846_) == 0 {
                    v_pos_6847_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                    v_res_6848_ = crate::leanh::lean_ctor_get(v___x_6846_, 1);
                    v_isSharedCheck_6944_ = (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                    if v_isSharedCheck_6944_ == 0 {
                        v___x_6850_ = v___x_6846_;
                        v_isShared_6851_ = v_isSharedCheck_6944_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_6848_);
                        crate::leanh::lean_inc(v_pos_6847_);
                        crate::leanh::lean_dec(v___x_6846_);
                        v___x_6850_ = crate::leanh::lean_box(0);
                        v_isShared_6851_ = v_isSharedCheck_6944_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_6841_);
                    v_err_6945_ = crate::leanh::lean_ctor_get(v___x_6846_, 1);
                    v_isSharedCheck_6952_ = (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                    if v_isSharedCheck_6952_ == 0 {
                        v_unused_6953_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                        crate::leanh::lean_dec(v_unused_6953_);
                        v___x_6947_ = v___x_6846_;
                        v_isShared_6948_ = v_isSharedCheck_6952_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6945_);
                        crate::leanh::lean_dec(v___x_6846_);
                        v___x_6947_ = crate::leanh::lean_box(0);
                        v_isShared_6948_ = v_isSharedCheck_6952_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6844_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1;
                v___x_6845_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6845_, 0, v_a_6842_);
                crate::leanh::lean_ctor_set(v___x_6845_, 1, v___x_6844_);
                return v___x_6845_;
            }
            2 => {
                v___x_6940_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4;
                v___x_6941_ = lean_string_dec_eq(v_res_6848_, v___x_6940_);
                if v___x_6941_ == 0 {
                    v___x_6942_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5;
                    v___x_6943_ = lean_string_dec_eq(v_res_6848_, v___x_6942_);
                    v___y_6874_ = v___x_6943_;
                    state = 6;
                    continue;
                } else {
                    v___y_6874_ = v___x_6941_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v___x_6857_ = crate::leanh::lean_box(0);
                v___x_6858_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6858_, 0, v_res_6848_);
                crate::leanh::lean_ctor_set(v___x_6858_, 1, v___y_6855_);
                crate::leanh::lean_ctor_set(v___x_6858_, 2, v___y_6854_);
                crate::leanh::lean_ctor_set(v___x_6858_, 3, v___y_6856_);
                crate::leanh::lean_ctor_set(v___x_6858_, 4, v___x_6857_);
                v___x_6859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6859_, 0, v___x_6858_);
                if v_isShared_6851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6850_, 1, v___x_6859_);
                    crate::leanh::lean_ctor_set(v___x_6850_, 0, v___y_6853_);
                    v___x_6861_ = v___x_6850_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6862_, 0, v___y_6853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6862_, 1, v___x_6859_);
                    v___x_6861_ = v_reuseFailAlloc_6862_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6861_;
            }
            5 => {
                v___x_6870_ = lean_nat_dec_eq(v_idx_6866_, v_idx_6868_);
                crate::leanh::lean_dec(v_idx_6868_);
                crate::leanh::lean_dec(v_idx_6866_);
                if v___x_6870_ == 0 {
                    crate::leanh::lean_dec_ref(v_pos_6867_);
                    crate::leanh::lean_dec(v___y_6865_);
                    crate::leanh::lean_dec_ref(v___y_6864_);
                    crate::leanh::lean_del_object(v___x_6850_);
                    crate::leanh::lean_dec(v_res_6848_);
                    v___x_6871_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6871_, 0, v_a_6842_);
                    crate::leanh::lean_ctor_set(v___x_6871_, 1, v_err_6869_);
                    return v___x_6871_;
                } else {
                    crate::leanh::lean_dec(v_err_6869_);
                    crate::leanh::lean_dec_ref(v_a_6842_);
                    v___x_6872_ = l_Std_Http_URI_Query_empty;
                    v___y_6853_ = v_pos_6867_;
                    v___y_6854_ = v___y_6864_;
                    v___y_6855_ = v___y_6865_;
                    v___y_6856_ = v___x_6872_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                if v___y_6874_ == 0 {
                    crate::leanh::lean_del_object(v___x_6850_);
                    crate::leanh::lean_dec(v_res_6848_);
                    crate::leanh::lean_dec(v_pos_6847_);
                    crate::leanh::lean_dec_ref(v_config_6841_);
                    v___x_6875_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3;
                    v___x_6876_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6876_, 0, v_a_6842_);
                    crate::leanh::lean_ctor_set(v___x_6876_, 1, v___x_6875_);
                    return v___x_6876_;
                } else {
                    v_array_6877_ = crate::leanh::lean_ctor_get(v_pos_6847_, 0);
                    v_idx_6878_ = crate::leanh::lean_ctor_get(v_pos_6847_, 1);
                    v_isSharedCheck_6939_ = (!crate::leanh::lean_is_exclusive(v_pos_6847_)) as u8;
                    if v_isSharedCheck_6939_ == 0 {
                        v___x_6880_ = v_pos_6847_;
                        v_isShared_6881_ = v_isSharedCheck_6939_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_6878_);
                        crate::leanh::lean_inc(v_array_6877_);
                        crate::leanh::lean_dec(v_pos_6847_);
                        v___x_6880_ = crate::leanh::lean_box(0);
                        v_isShared_6881_ = v_isSharedCheck_6939_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6882_ = lean_byte_array_size(v_array_6877_);
                v___x_6883_ = lean_nat_dec_lt(v_idx_6878_, v___x_6882_);
                if v___x_6883_ == 0 {
                    crate::leanh::lean_del_object(v___x_6880_);
                    crate::leanh::lean_dec(v_idx_6878_);
                    crate::leanh::lean_dec_ref(v_array_6877_);
                    crate::leanh::lean_del_object(v___x_6850_);
                    crate::leanh::lean_dec(v_res_6848_);
                    crate::leanh::lean_dec_ref(v_config_6841_);
                    v___x_6884_ = crate::leanh::lean_box(0);
                    v___x_6885_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6885_, 0, v_a_6842_);
                    crate::leanh::lean_ctor_set(v___x_6885_, 1, v___x_6884_);
                    return v___x_6885_;
                } else {
                    v___x_6886_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v_got_6887_ = lean_byte_array_fget(v_array_6877_, v_idx_6878_);
                    v___x_6888_ = lean_uint8_dec_eq(v_got_6887_, v___x_6886_);
                    if v___x_6888_ == 0 {
                        crate::leanh::lean_del_object(v___x_6880_);
                        crate::leanh::lean_dec(v_idx_6878_);
                        crate::leanh::lean_dec_ref(v_array_6877_);
                        crate::leanh::lean_del_object(v___x_6850_);
                        crate::leanh::lean_dec(v_res_6848_);
                        crate::leanh::lean_dec_ref(v_config_6841_);
                        v___x_6889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                        v___x_6890_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6890_, 0, v_a_6842_);
                        crate::leanh::lean_ctor_set(v___x_6890_, 1, v___x_6889_);
                        return v___x_6890_;
                    } else {
                        v___x_6891_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6892_ = lean_nat_add(v_idx_6878_, v___x_6891_);
                        crate::leanh::lean_dec(v_idx_6878_);
                        v___x_6893_ = lean_nat_dec_lt(v___x_6892_, v___x_6882_);
                        if v___x_6893_ == 0 {
                            crate::leanh::lean_dec(v___x_6892_);
                            crate::leanh::lean_del_object(v___x_6880_);
                            crate::leanh::lean_dec_ref(v_array_6877_);
                            crate::leanh::lean_del_object(v___x_6850_);
                            crate::leanh::lean_dec(v_res_6848_);
                            crate::leanh::lean_dec_ref(v_config_6841_);
                            state = 1;
                            continue;
                        } else {
                            v___x_6894_ = lean_byte_array_fget(v_array_6877_, v___x_6892_);
                            v___x_6895_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
                            v___x_6896_ = lean_uint8_dec_eq(v___x_6894_, v___x_6895_);
                            if v___x_6896_ == 0 {
                                crate::leanh::lean_dec(v___x_6892_);
                                crate::leanh::lean_del_object(v___x_6880_);
                                crate::leanh::lean_dec_ref(v_array_6877_);
                                crate::leanh::lean_del_object(v___x_6850_);
                                crate::leanh::lean_dec(v_res_6848_);
                                crate::leanh::lean_dec_ref(v_config_6841_);
                                state = 1;
                                continue;
                            } else {
                                if v___x_6896_ == 0 {
                                    crate::leanh::lean_dec(v___x_6892_);
                                    crate::leanh::lean_del_object(v___x_6880_);
                                    crate::leanh::lean_dec_ref(v_array_6877_);
                                    crate::leanh::lean_del_object(v___x_6850_);
                                    crate::leanh::lean_dec(v_res_6848_);
                                    crate::leanh::lean_dec_ref(v_config_6841_);
                                    state = 1;
                                    continue;
                                } else {
                                    if v_isShared_6881_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_6880_, 1, v___x_6892_);
                                        v___x_6898_ = v___x_6880_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6938_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6938_,
                                            0,
                                            v_array_6877_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6938_,
                                            1,
                                            v___x_6892_,
                                        );
                                        v___x_6898_ = v_reuseFailAlloc_6938_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v_config_6841_);
                v___x_6899_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(
                        v_config_6841_,
                        v___x_6898_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6899_) == 0 {
                    v_res_6900_ = crate::leanh::lean_ctor_get(v___x_6899_, 1);
                    crate::leanh::lean_inc(v_res_6900_);
                    v_pos_6901_ = crate::leanh::lean_ctor_get(v___x_6899_, 0);
                    crate::leanh::lean_inc(v_pos_6901_);
                    crate::leanh::lean_dec_ref_known(v___x_6899_, 2);
                    v_fst_6902_ = crate::leanh::lean_ctor_get(v_res_6900_, 0);
                    crate::leanh::lean_inc(v_fst_6902_);
                    v_snd_6903_ = crate::leanh::lean_ctor_get(v_res_6900_, 1);
                    crate::leanh::lean_inc(v_snd_6903_);
                    crate::leanh::lean_dec(v_res_6900_);
                    v_array_6904_ = crate::leanh::lean_ctor_get(v_pos_6901_, 0);
                    v_idx_6905_ = crate::leanh::lean_ctor_get(v_pos_6901_, 1);
                    crate::leanh::lean_inc(v_idx_6905_);
                    v___x_6906_ = lean_byte_array_size(v_array_6904_);
                    v___x_6907_ = lean_nat_dec_lt(v_idx_6905_, v___x_6906_);
                    if v___x_6907_ == 0 {
                        crate::leanh::lean_dec_ref(v_config_6841_);
                        v___x_6908_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_idx_6905_);
                        v___y_6864_ = v_snd_6903_;
                        v___y_6865_ = v_fst_6902_;
                        v_idx_6866_ = v_idx_6905_;
                        v_pos_6867_ = v_pos_6901_;
                        v_idx_6868_ = v_idx_6905_;
                        v_err_6869_ = v___x_6908_;
                        state = 5;
                        continue;
                    } else {
                        v___x_6909_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
                        v_got_6910_ = lean_byte_array_fget(v_array_6904_, v_idx_6905_);
                        v___x_6911_ = lean_uint8_dec_eq(v_got_6910_, v___x_6909_);
                        if v___x_6911_ == 0 {
                            crate::leanh::lean_dec_ref(v_config_6841_);
                            v___x_6912_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_Parser_parseURI___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_Parser_parseURI___closed__11_once
                                ),
                                _init_l_Std_Http_URI_Parser_parseURI___closed__11,
                            );
                            crate::leanh::lean_inc(v_idx_6905_);
                            v___y_6864_ = v_snd_6903_;
                            v___y_6865_ = v_fst_6902_;
                            v_idx_6866_ = v_idx_6905_;
                            v_pos_6867_ = v_pos_6901_;
                            v_idx_6868_ = v_idx_6905_;
                            v_err_6869_ = v___x_6912_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_array_6904_);
                            v_isSharedCheck_6926_ =
                                (!crate::leanh::lean_is_exclusive(v_pos_6901_)) as u8;
                            if v_isSharedCheck_6926_ == 0 {
                                v_unused_6927_ = crate::leanh::lean_ctor_get(v_pos_6901_, 1);
                                crate::leanh::lean_dec(v_unused_6927_);
                                v_unused_6928_ = crate::leanh::lean_ctor_get(v_pos_6901_, 0);
                                crate::leanh::lean_dec(v_unused_6928_);
                                v___x_6914_ = v_pos_6901_;
                                v_isShared_6915_ = v_isSharedCheck_6926_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_pos_6901_);
                                v___x_6914_ = crate::leanh::lean_box(0);
                                v_isShared_6915_ = v_isSharedCheck_6926_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6850_);
                    crate::leanh::lean_dec(v_res_6848_);
                    crate::leanh::lean_dec_ref(v_config_6841_);
                    v_err_6929_ = crate::leanh::lean_ctor_get(v___x_6899_, 1);
                    v_isSharedCheck_6936_ = (!crate::leanh::lean_is_exclusive(v___x_6899_)) as u8;
                    if v_isSharedCheck_6936_ == 0 {
                        v_unused_6937_ = crate::leanh::lean_ctor_get(v___x_6899_, 0);
                        crate::leanh::lean_dec(v_unused_6937_);
                        v___x_6931_ = v___x_6899_;
                        v_isShared_6932_ = v_isSharedCheck_6936_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6929_);
                        crate::leanh::lean_dec(v___x_6899_);
                        v___x_6931_ = crate::leanh::lean_box(0);
                        v_isShared_6932_ = v_isSharedCheck_6936_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6916_ = lean_nat_add(v_idx_6905_, v___x_6891_);
                if v_isShared_6915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6914_, 1, v___x_6916_);
                    v___x_6918_ = v___x_6914_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6925_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 0, v_array_6904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 1, v___x_6916_);
                    v___x_6918_ = v_reuseFailAlloc_6925_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6919_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(
                        v_config_6841_,
                        v___x_6918_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6919_) == 0 {
                    crate::leanh::lean_dec(v_idx_6905_);
                    crate::leanh::lean_dec_ref(v_a_6842_);
                    v_pos_6920_ = crate::leanh::lean_ctor_get(v___x_6919_, 0);
                    crate::leanh::lean_inc(v_pos_6920_);
                    v_res_6921_ = crate::leanh::lean_ctor_get(v___x_6919_, 1);
                    crate::leanh::lean_inc(v_res_6921_);
                    crate::leanh::lean_dec_ref_known(v___x_6919_, 2);
                    v___y_6853_ = v_pos_6920_;
                    v___y_6854_ = v_snd_6903_;
                    v___y_6855_ = v_fst_6902_;
                    v___y_6856_ = v_res_6921_;
                    state = 3;
                    continue;
                } else {
                    v_pos_6922_ = crate::leanh::lean_ctor_get(v___x_6919_, 0);
                    crate::leanh::lean_inc(v_pos_6922_);
                    v_err_6923_ = crate::leanh::lean_ctor_get(v___x_6919_, 1);
                    crate::leanh::lean_inc(v_err_6923_);
                    crate::leanh::lean_dec_ref_known(v___x_6919_, 2);
                    v_idx_6924_ = crate::leanh::lean_ctor_get(v_pos_6922_, 1);
                    crate::leanh::lean_inc(v_idx_6924_);
                    v___y_6864_ = v_snd_6903_;
                    v___y_6865_ = v_fst_6902_;
                    v_idx_6866_ = v_idx_6905_;
                    v_pos_6867_ = v_pos_6922_;
                    v_idx_6868_ = v_idx_6924_;
                    v_err_6869_ = v_err_6923_;
                    state = 5;
                    continue;
                }
            }
            11 => {
                if v_isShared_6932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6931_, 0, v_a_6842_);
                    v___x_6934_ = v___x_6931_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6935_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_a_6842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6935_, 1, v_err_6929_);
                    v___x_6934_ = v_reuseFailAlloc_6935_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6934_;
            }
            13 => {
                if v_isShared_6948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6947_, 0, v_a_6842_);
                    v___x_6950_ = v___x_6947_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6951_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6951_, 0, v_a_6842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6951_, 1, v_err_6945_);
                    v___x_6950_ = v_reuseFailAlloc_6951_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(
    mut v_config_6954_: *mut crate::leanh::LeanObject,
    mut v_a_6955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6963_: u8 = 0;
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6967_: u8 = 0;
    let mut v_unused_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6972_: u8 = 0;
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6976_: u8 = 0;
    let mut v_unused_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_6955_);
                v___x_6956_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(
                        v_config_6954_,
                        v_a_6955_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6956_) == 0 {
                    v_pos_6957_ = crate::leanh::lean_ctor_get(v___x_6956_, 0);
                    crate::leanh::lean_inc(v_pos_6957_);
                    v_res_6958_ = crate::leanh::lean_ctor_get(v___x_6956_, 1);
                    crate::leanh::lean_inc(v_res_6958_);
                    crate::leanh::lean_dec_ref_known(v___x_6956_, 2);
                    v___x_6959_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_6954_, v_res_6958_, v_pos_6957_);
                    if crate::leanh::lean_obj_tag(v___x_6959_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_6955_);
                        return v___x_6959_;
                    } else {
                        v_err_6960_ = crate::leanh::lean_ctor_get(v___x_6959_, 1);
                        v_isSharedCheck_6967_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6959_)) as u8;
                        if v_isSharedCheck_6967_ == 0 {
                            v_unused_6968_ = crate::leanh::lean_ctor_get(v___x_6959_, 0);
                            crate::leanh::lean_dec(v_unused_6968_);
                            v___x_6962_ = v___x_6959_;
                            v_isShared_6963_ = v_isSharedCheck_6967_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_6960_);
                            crate::leanh::lean_dec(v___x_6959_);
                            v___x_6962_ = crate::leanh::lean_box(0);
                            v_isShared_6963_ = v_isSharedCheck_6967_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_6954_);
                    v_err_6969_ = crate::leanh::lean_ctor_get(v___x_6956_, 1);
                    v_isSharedCheck_6976_ = (!crate::leanh::lean_is_exclusive(v___x_6956_)) as u8;
                    if v_isSharedCheck_6976_ == 0 {
                        v_unused_6977_ = crate::leanh::lean_ctor_get(v___x_6956_, 0);
                        crate::leanh::lean_dec(v_unused_6977_);
                        v___x_6971_ = v___x_6956_;
                        v_isShared_6972_ = v_isSharedCheck_6976_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_6969_);
                        crate::leanh::lean_dec(v___x_6956_);
                        v___x_6971_ = crate::leanh::lean_box(0);
                        v_isShared_6972_ = v_isSharedCheck_6976_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6962_, 0, v_a_6955_);
                    v___x_6965_ = v___x_6962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6966_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 0, v_a_6955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 1, v_err_6960_);
                    v___x_6965_ = v_reuseFailAlloc_6966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6965_;
            }
            3 => {
                if v_isShared_6972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6971_, 0, v_a_6955_);
                    v___x_6974_ = v___x_6971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6975_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6975_, 0, v_a_6955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6975_, 1, v_err_6969_);
                    v___x_6974_ = v_reuseFailAlloc_6975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(
    mut v_config_6978_: *mut crate::leanh::LeanObject,
    mut v_a_6979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6985_: u8 = 0;
    let mut v_array_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6990_: u8 = 0;
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: u8 = 0;
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: u8 = 0;
    let mut v_got_6998_: u8 = 0;
    let mut v___x_6999_: u8 = 0;
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7013_: u8 = 0;
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: u16 = 0;
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7022_: u8 = 0;
    let mut v_err_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7026_: u8 = 0;
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7030_: u8 = 0;
    let mut v_unused_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7033_: u8 = 0;
    let mut v_isSharedCheck_7034_: u8 = 0;
    let mut v_err_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7038_: u8 = 0;
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7042_: u8 = 0;
    let mut v_unused_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_6979_);
                v___x_6980_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(
                    v_config_6978_,
                    v_a_6979_,
                );
                if crate::leanh::lean_obj_tag(v___x_6980_) == 0 {
                    v_pos_6981_ = crate::leanh::lean_ctor_get(v___x_6980_, 0);
                    v_res_6982_ = crate::leanh::lean_ctor_get(v___x_6980_, 1);
                    v_isSharedCheck_7034_ = (!crate::leanh::lean_is_exclusive(v___x_6980_)) as u8;
                    if v_isSharedCheck_7034_ == 0 {
                        v___x_6984_ = v___x_6980_;
                        v_isShared_6985_ = v_isSharedCheck_7034_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_6982_);
                        crate::leanh::lean_inc(v_pos_6981_);
                        crate::leanh::lean_dec(v___x_6980_);
                        v___x_6984_ = crate::leanh::lean_box(0);
                        v_isShared_6985_ = v_isSharedCheck_7034_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_err_7035_ = crate::leanh::lean_ctor_get(v___x_6980_, 1);
                    v_isSharedCheck_7042_ = (!crate::leanh::lean_is_exclusive(v___x_6980_)) as u8;
                    if v_isSharedCheck_7042_ == 0 {
                        v_unused_7043_ = crate::leanh::lean_ctor_get(v___x_6980_, 0);
                        crate::leanh::lean_dec(v_unused_7043_);
                        v___x_7037_ = v___x_6980_;
                        v_isShared_7038_ = v_isSharedCheck_7042_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_7035_);
                        crate::leanh::lean_dec(v___x_6980_);
                        v___x_7037_ = crate::leanh::lean_box(0);
                        v_isShared_7038_ = v_isSharedCheck_7042_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_array_6986_ = crate::leanh::lean_ctor_get(v_pos_6981_, 0);
                v_idx_6987_ = crate::leanh::lean_ctor_get(v_pos_6981_, 1);
                v_isSharedCheck_7033_ = (!crate::leanh::lean_is_exclusive(v_pos_6981_)) as u8;
                if v_isSharedCheck_7033_ == 0 {
                    v___x_6989_ = v_pos_6981_;
                    v_isShared_6990_ = v_isSharedCheck_7033_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_6987_);
                    crate::leanh::lean_inc(v_array_6986_);
                    crate::leanh::lean_dec(v_pos_6981_);
                    v___x_6989_ = crate::leanh::lean_box(0);
                    v_isShared_6990_ = v_isSharedCheck_7033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6991_ = lean_byte_array_size(v_array_6986_);
                v___x_6992_ = lean_nat_dec_lt(v_idx_6987_, v___x_6991_);
                if v___x_6992_ == 0 {
                    crate::leanh::lean_del_object(v___x_6989_);
                    crate::leanh::lean_dec(v_idx_6987_);
                    crate::leanh::lean_dec_ref(v_array_6986_);
                    crate::leanh::lean_dec(v_res_6982_);
                    v___x_6993_ = crate::leanh::lean_box(0);
                    if v_isShared_6985_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6984_, 1);
                        crate::leanh::lean_ctor_set(v___x_6984_, 1, v___x_6993_);
                        crate::leanh::lean_ctor_set(v___x_6984_, 0, v_a_6979_);
                        v___x_6995_ = v___x_6984_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6996_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6996_, 0, v_a_6979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6996_, 1, v___x_6993_);
                        v___x_6995_ = v_reuseFailAlloc_6996_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6997_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v_got_6998_ = lean_byte_array_fget(v_array_6986_, v_idx_6987_);
                    v___x_6999_ = lean_uint8_dec_eq(v_got_6998_, v___x_6997_);
                    if v___x_6999_ == 0 {
                        crate::leanh::lean_del_object(v___x_6989_);
                        crate::leanh::lean_dec(v_idx_6987_);
                        crate::leanh::lean_dec_ref(v_array_6986_);
                        crate::leanh::lean_dec(v_res_6982_);
                        v___x_7000_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                        if v_isShared_6985_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6984_, 1);
                            crate::leanh::lean_ctor_set(v___x_6984_, 1, v___x_7000_);
                            crate::leanh::lean_ctor_set(v___x_6984_, 0, v_a_6979_);
                            v___x_7002_ = v___x_6984_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7003_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7003_, 0, v_a_6979_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7003_, 1, v___x_7000_);
                            v___x_7002_ = v_reuseFailAlloc_7003_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6984_);
                        v___x_7004_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7005_ = lean_nat_add(v_idx_6987_, v___x_7004_);
                        crate::leanh::lean_dec(v_idx_6987_);
                        if v_isShared_6990_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6989_, 1, v___x_7005_);
                            v___x_7007_ = v___x_6989_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_7032_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7032_, 0, v_array_6986_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7032_, 1, v___x_7005_);
                            v___x_7007_ = v_reuseFailAlloc_7032_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6995_;
            }
            4 => {
                return v___x_7002_;
            }
            5 => {
                v___x_7008_ =
                    l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(
                        v___x_7007_,
                    );
                if crate::leanh::lean_obj_tag(v___x_7008_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_6979_);
                    v_pos_7009_ = crate::leanh::lean_ctor_get(v___x_7008_, 0);
                    v_res_7010_ = crate::leanh::lean_ctor_get(v___x_7008_, 1);
                    v_isSharedCheck_7022_ = (!crate::leanh::lean_is_exclusive(v___x_7008_)) as u8;
                    if v_isSharedCheck_7022_ == 0 {
                        v___x_7012_ = v___x_7008_;
                        v_isShared_7013_ = v_isSharedCheck_7022_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_7010_);
                        crate::leanh::lean_inc(v_pos_7009_);
                        crate::leanh::lean_dec(v___x_7008_);
                        v___x_7012_ = crate::leanh::lean_box(0);
                        v_isShared_7013_ = v_isSharedCheck_7022_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_res_6982_);
                    v_err_7023_ = crate::leanh::lean_ctor_get(v___x_7008_, 1);
                    v_isSharedCheck_7030_ = (!crate::leanh::lean_is_exclusive(v___x_7008_)) as u8;
                    if v_isSharedCheck_7030_ == 0 {
                        v_unused_7031_ = crate::leanh::lean_ctor_get(v___x_7008_, 0);
                        crate::leanh::lean_dec(v_unused_7031_);
                        v___x_7025_ = v___x_7008_;
                        v_isShared_7026_ = v_isSharedCheck_7030_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_7023_);
                        crate::leanh::lean_dec(v___x_7008_);
                        v___x_7025_ = crate::leanh::lean_box(0);
                        v_isShared_7026_ = v_isSharedCheck_7030_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_7014_ = crate::leanh::lean_box(0);
                v___x_7015_ = crate::leanh::lean_alloc_ctor(2, 0, (2) as u32);
                v___x_7016_ = (crate::leanh::lean_unbox(v_res_7010_) as u16);
                crate::leanh::lean_dec(v_res_7010_);
                crate::leanh::lean_ctor_set_uint16(v___x_7015_, 0 as u32, v___x_7016_);
                v___x_7017_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7017_, 0, v___x_7014_);
                crate::leanh::lean_ctor_set(v___x_7017_, 1, v_res_6982_);
                crate::leanh::lean_ctor_set(v___x_7017_, 2, v___x_7015_);
                v___x_7018_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7018_, 0, v___x_7017_);
                if v_isShared_7013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7012_, 1, v___x_7018_);
                    v___x_7020_ = v___x_7012_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7021_, 0, v_pos_7009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7021_, 1, v___x_7018_);
                    v___x_7020_ = v_reuseFailAlloc_7021_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7020_;
            }
            8 => {
                if v_isShared_7026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7025_, 0, v_a_6979_);
                    v___x_7028_ = v___x_7025_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7029_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 0, v_a_6979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 1, v_err_7023_);
                    v___x_7028_ = v_reuseFailAlloc_7029_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7028_;
            }
            10 => {
                if v_isShared_7038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7037_, 0, v_a_6979_);
                    v___x_7040_ = v___x_7037_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7041_, 0, v_a_6979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7041_, 1, v_err_7035_);
                    v___x_7040_ = v_reuseFailAlloc_7041_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(
    mut v_config_7044_: *mut crate::leanh::LeanObject,
    mut v_a_7045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7046_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(
            v_config_7044_,
            v_a_7045_,
        );
    crate::leanh::lean_dec_ref(v_config_7044_);
    return v_res_7046_;
}
pub unsafe fn l_Std_Http_URI_Parser_parseRequestTarget(
    mut v_config_7047_: *mut crate::leanh::LeanObject,
    mut v_a_7048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_7048_);
    v___x_7049_ =
        l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(
            v_a_7048_,
        );
    if crate::leanh::lean_obj_tag(v___x_7049_) == 0 {
        crate::leanh::lean_dec_ref(v_a_7048_);
        crate::leanh::lean_dec_ref(v_config_7047_);
        return v___x_7049_;
    } else {
        let mut v_pos_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7053_: u8 = 0;
        v_pos_7050_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
        crate::leanh::lean_inc(v_pos_7050_);
        v_idx_7051_ = crate::leanh::lean_ctor_get(v_a_7048_, 1);
        crate::leanh::lean_inc(v_idx_7051_);
        crate::leanh::lean_dec_ref(v_a_7048_);
        v_idx_7052_ = crate::leanh::lean_ctor_get(v_pos_7050_, 1);
        crate::leanh::lean_inc(v_idx_7052_);
        v___x_7053_ = lean_nat_dec_eq(v_idx_7051_, v_idx_7052_);
        crate::leanh::lean_dec(v_idx_7051_);
        if v___x_7053_ == 0 {
            crate::leanh::lean_dec(v_idx_7052_);
            crate::leanh::lean_dec(v_pos_7050_);
            crate::leanh::lean_dec_ref(v_config_7047_);
            return v___x_7049_;
        } else {
            let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_7049_, 2);
            crate::leanh::lean_inc_ref(v_config_7047_);
            v___x_7054_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_7047_, v_pos_7050_);
            if crate::leanh::lean_obj_tag(v___x_7054_) == 0 {
                crate::leanh::lean_dec(v_idx_7052_);
                crate::leanh::lean_dec_ref(v_config_7047_);
                return v___x_7054_;
            } else {
                let mut v_pos_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_idx_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7057_: u8 = 0;
                v_pos_7055_ = crate::leanh::lean_ctor_get(v___x_7054_, 0);
                crate::leanh::lean_inc(v_pos_7055_);
                v_idx_7056_ = crate::leanh::lean_ctor_get(v_pos_7055_, 1);
                crate::leanh::lean_inc(v_idx_7056_);
                v___x_7057_ = lean_nat_dec_eq(v_idx_7052_, v_idx_7056_);
                crate::leanh::lean_dec(v_idx_7052_);
                if v___x_7057_ == 0 {
                    crate::leanh::lean_dec(v_idx_7056_);
                    crate::leanh::lean_dec(v_pos_7055_);
                    crate::leanh::lean_dec_ref(v_config_7047_);
                    return v___x_7054_;
                } else {
                    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_7054_, 2);
                    crate::leanh::lean_inc_ref(v_config_7047_);
                    v___x_7058_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_7047_, v_pos_7055_);
                    if crate::leanh::lean_obj_tag(v___x_7058_) == 0 {
                        crate::leanh::lean_dec(v_idx_7056_);
                        crate::leanh::lean_dec_ref(v_config_7047_);
                        return v___x_7058_;
                    } else {
                        let mut v_pos_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_idx_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_7061_: u8 = 0;
                        v_pos_7059_ = crate::leanh::lean_ctor_get(v___x_7058_, 0);
                        crate::leanh::lean_inc(v_pos_7059_);
                        v_idx_7060_ = crate::leanh::lean_ctor_get(v_pos_7059_, 1);
                        crate::leanh::lean_inc(v_idx_7060_);
                        v___x_7061_ = lean_nat_dec_eq(v_idx_7056_, v_idx_7060_);
                        crate::leanh::lean_dec(v_idx_7056_);
                        if v___x_7061_ == 0 {
                            crate::leanh::lean_dec(v_idx_7060_);
                            crate::leanh::lean_dec(v_pos_7059_);
                            crate::leanh::lean_dec_ref(v_config_7047_);
                            return v___x_7058_;
                        } else {
                            let mut v___x_7062_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_7058_, 2);
                            v___x_7062_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_7047_, v_pos_7059_);
                            if crate::leanh::lean_obj_tag(v___x_7062_) == 0 {
                                crate::leanh::lean_dec(v_idx_7060_);
                                crate::leanh::lean_dec_ref(v_config_7047_);
                                return v___x_7062_;
                            } else {
                                let mut v_pos_7063_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_idx_7064_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_7065_: u8 = 0;
                                v_pos_7063_ = crate::leanh::lean_ctor_get(v___x_7062_, 0);
                                crate::leanh::lean_inc(v_pos_7063_);
                                v_idx_7064_ = crate::leanh::lean_ctor_get(v_pos_7063_, 1);
                                v___x_7065_ = lean_nat_dec_eq(v_idx_7060_, v_idx_7064_);
                                crate::leanh::lean_dec(v_idx_7060_);
                                if v___x_7065_ == 0 {
                                    crate::leanh::lean_dec(v_pos_7063_);
                                    crate::leanh::lean_dec_ref(v_config_7047_);
                                    return v___x_7062_;
                                } else {
                                    let mut v___x_7066_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec_ref_known(v___x_7062_, 2);
                                    v___x_7066_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_7047_, v_pos_7063_);
                                    return v___x_7066_;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_Parser_parseHostHeader(
    mut v_config_7073_: *mut crate::leanh::LeanObject,
    mut v_a_7074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v_port_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: u8 = 0;
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: u8 = 0;
    let mut v___y_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: u8 = 0;
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: u8 = 0;
    let mut v___x_7115_: u8 = 0;
    let mut v___x_7116_: u8 = 0;
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7129_: u8 = 0;
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: u16 = 0;
    let mut v_pos_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7139_: u8 = 0;
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7143_: u8 = 0;
    let mut v___x_7144_: u8 = 0;
    let mut v___x_7145_: u8 = 0;
    let mut v___x_7146_: u8 = 0;
    let mut v___x_7147_: u8 = 0;
    let mut v___x_7148_: u8 = 0;
    let mut v___x_7149_: u8 = 0;
    let mut v_reuseFailAlloc_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7151_: u8 = 0;
    let mut v_unused_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7154_: u8 = 0;
    let mut v_pos_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7079_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(
                    v_config_7073_,
                    v_a_7074_,
                );
                if crate::leanh::lean_obj_tag(v___x_7079_) == 0 {
                    v_pos_7080_ = crate::leanh::lean_ctor_get(v___x_7079_, 0);
                    v_res_7081_ = crate::leanh::lean_ctor_get(v___x_7079_, 1);
                    v_isSharedCheck_7154_ = (!crate::leanh::lean_is_exclusive(v___x_7079_)) as u8;
                    if v_isSharedCheck_7154_ == 0 {
                        v___x_7083_ = v___x_7079_;
                        v_isShared_7084_ = v_isSharedCheck_7154_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_7081_);
                        crate::leanh::lean_inc(v_pos_7080_);
                        crate::leanh::lean_dec(v___x_7079_);
                        v___x_7083_ = crate::leanh::lean_box(0);
                        v_isShared_7084_ = v_isSharedCheck_7154_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_pos_7155_ = crate::leanh::lean_ctor_get(v___x_7079_, 0);
                    v_err_7156_ = crate::leanh::lean_ctor_get(v___x_7079_, 1);
                    v_isSharedCheck_7163_ = (!crate::leanh::lean_is_exclusive(v___x_7079_)) as u8;
                    if v_isSharedCheck_7163_ == 0 {
                        v___x_7158_ = v___x_7079_;
                        v_isShared_7159_ = v_isSharedCheck_7163_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_7156_);
                        crate::leanh::lean_inc(v_pos_7155_);
                        crate::leanh::lean_dec(v___x_7079_);
                        v___x_7158_ = crate::leanh::lean_box(0);
                        v_isShared_7159_ = v_isSharedCheck_7163_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7077_ = l_Std_Http_URI_Parser_parseHostHeader___closed__1;
                v___x_7078_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7078_, 0, v___y_7076_);
                crate::leanh::lean_ctor_set(v___x_7078_, 1, v___x_7077_);
                return v___x_7078_;
            }
            2 => {
                v_array_7103_ = crate::leanh::lean_ctor_get(v_pos_7080_, 0);
                v_idx_7104_ = crate::leanh::lean_ctor_get(v_pos_7080_, 1);
                v___x_7105_ = lean_byte_array_size(v_array_7103_);
                v___x_7106_ = lean_nat_dec_lt(v_idx_7104_, v___x_7105_);
                if v___x_7106_ == 0 {
                    v_pos_7101_ = v_pos_7080_;
                    state = 6;
                    continue;
                } else {
                    v___x_7114_ = lean_byte_array_fget(v_array_7103_, v_idx_7104_);
                    v___x_7115_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
                    v___x_7116_ = lean_uint8_dec_eq(v___x_7114_, v___x_7115_);
                    if v___x_7116_ == 0 {
                        v_pos_7101_ = v_pos_7080_;
                        state = 6;
                        continue;
                    } else {
                        if v___x_7116_ == 0 {
                            v_pos_7101_ = v_pos_7080_;
                            state = 6;
                            continue;
                        } else {
                            if v___x_7106_ == 0 {
                                crate::leanh::lean_del_object(v___x_7083_);
                                crate::leanh::lean_dec(v_res_7081_);
                                v___x_7117_ = crate::leanh::lean_box(0);
                                v___x_7118_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7118_, 0, v_pos_7080_);
                                crate::leanh::lean_ctor_set(v___x_7118_, 1, v___x_7117_);
                                return v___x_7118_;
                            } else {
                                if v___x_7116_ == 0 {
                                    crate::leanh::lean_del_object(v___x_7083_);
                                    crate::leanh::lean_dec(v_res_7081_);
                                    v___x_7119_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
                                    v___x_7120_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v_pos_7080_);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v___x_7119_);
                                    return v___x_7120_;
                                } else {
                                    crate::leanh::lean_inc(v_idx_7104_);
                                    crate::leanh::lean_inc_ref(v_array_7103_);
                                    v_isSharedCheck_7151_ =
                                        (!crate::leanh::lean_is_exclusive(v_pos_7080_)) as u8;
                                    if v_isSharedCheck_7151_ == 0 {
                                        v_unused_7152_ =
                                            crate::leanh::lean_ctor_get(v_pos_7080_, 1);
                                        crate::leanh::lean_dec(v_unused_7152_);
                                        v_unused_7153_ =
                                            crate::leanh::lean_ctor_get(v_pos_7080_, 0);
                                        crate::leanh::lean_dec(v_unused_7153_);
                                        v___x_7122_ = v_pos_7080_;
                                        v_isShared_7123_ = v_isSharedCheck_7151_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pos_7080_);
                                        v___x_7122_ = crate::leanh::lean_box(0);
                                        v_isShared_7123_ = v_isSharedCheck_7151_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v_array_7088_ = crate::leanh::lean_ctor_get(v___y_7087_, 0);
                v_idx_7089_ = crate::leanh::lean_ctor_get(v___y_7087_, 1);
                v___x_7090_ = lean_byte_array_size(v_array_7088_);
                v___x_7091_ = lean_nat_dec_lt(v_idx_7089_, v___x_7090_);
                if v___x_7091_ == 0 {
                    v___x_7092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7092_, 0, v_res_7081_);
                    crate::leanh::lean_ctor_set(v___x_7092_, 1, v_port_7086_);
                    if v_isShared_7084_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7083_, 1, v___x_7092_);
                        crate::leanh::lean_ctor_set(v___x_7083_, 0, v___y_7087_);
                        v___x_7094_ = v___x_7083_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 0, v___y_7087_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 1, v___x_7092_);
                        v___x_7094_ = v_reuseFailAlloc_7095_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_port_7086_);
                    crate::leanh::lean_dec(v_res_7081_);
                    v___x_7096_ = l_Std_Http_URI_Parser_parseHostHeader___closed__3;
                    if v_isShared_7084_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7083_, 1);
                        crate::leanh::lean_ctor_set(v___x_7083_, 1, v___x_7096_);
                        crate::leanh::lean_ctor_set(v___x_7083_, 0, v___y_7087_);
                        v___x_7098_ = v___x_7083_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7099_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7099_, 0, v___y_7087_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7099_, 1, v___x_7096_);
                        v___x_7098_ = v_reuseFailAlloc_7099_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7094_;
            }
            5 => {
                return v___x_7098_;
            }
            6 => {
                v___x_7102_ = crate::leanh::lean_box(0);
                v_port_7086_ = v___x_7102_;
                v___y_7087_ = v_pos_7101_;
                state = 3;
                continue;
            }
            7 => {
                v___x_7111_ = lean_byte_array_size(v_array_7109_);
                crate::leanh::lean_dec_ref(v_array_7109_);
                v___x_7112_ = lean_nat_dec_lt(v_idx_7110_, v___x_7111_);
                crate::leanh::lean_dec(v_idx_7110_);
                if v___x_7112_ == 0 {
                    if v___x_7106_ == 0 {
                        crate::leanh::lean_del_object(v___x_7083_);
                        crate::leanh::lean_dec(v_res_7081_);
                        v___y_7076_ = v___y_7108_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7113_ = crate::leanh::lean_box(1);
                        v_port_7086_ = v___x_7113_;
                        v___y_7087_ = v___y_7108_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7083_);
                    crate::leanh::lean_dec(v_res_7081_);
                    v___y_7076_ = v___y_7108_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_7124_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7125_ = lean_nat_add(v_idx_7104_, v___x_7124_);
                crate::leanh::lean_dec(v_idx_7104_);
                crate::leanh::lean_inc(v___x_7125_);
                crate::leanh::lean_inc_ref(v_array_7103_);
                if v_isShared_7123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7122_, 1, v___x_7125_);
                    v___x_7127_ = v___x_7122_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7150_, 0, v_array_7103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7150_, 1, v___x_7125_);
                    v___x_7127_ = v_reuseFailAlloc_7150_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7144_ = lean_nat_dec_lt(v___x_7125_, v___x_7105_);
                if v___x_7144_ == 0 {
                    v___y_7108_ = v___x_7127_;
                    v_array_7109_ = v_array_7103_;
                    v_idx_7110_ = v___x_7125_;
                    state = 7;
                    continue;
                } else {
                    v___x_7145_ = lean_byte_array_fget(v_array_7103_, v___x_7125_);
                    v___x_7146_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
                    v___x_7147_ = lean_uint8_dec_le(v___x_7146_, v___x_7145_);
                    if v___x_7147_ == 0 {
                        v___y_7129_ = v___x_7147_;
                        state = 10;
                        continue;
                    } else {
                        v___x_7148_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once), _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
                        v___x_7149_ = lean_uint8_dec_le(v___x_7145_, v___x_7148_);
                        v___y_7129_ = v___x_7149_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v___y_7129_ == 0 {
                    v___y_7108_ = v___x_7127_;
                    v_array_7109_ = v_array_7103_;
                    v_idx_7110_ = v___x_7125_;
                    state = 7;
                    continue;
                } else {
                    if v___x_7106_ == 0 {
                        v___y_7108_ = v___x_7127_;
                        v_array_7109_ = v_array_7103_;
                        v_idx_7110_ = v___x_7125_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7125_);
                        crate::leanh::lean_dec_ref(v_array_7103_);
                        v___x_7130_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_7127_);
                        if crate::leanh::lean_obj_tag(v___x_7130_) == 0 {
                            v_pos_7131_ = crate::leanh::lean_ctor_get(v___x_7130_, 0);
                            crate::leanh::lean_inc(v_pos_7131_);
                            v_res_7132_ = crate::leanh::lean_ctor_get(v___x_7130_, 1);
                            crate::leanh::lean_inc(v_res_7132_);
                            crate::leanh::lean_dec_ref_known(v___x_7130_, 2);
                            v___x_7133_ = crate::leanh::lean_alloc_ctor(2, 0, (2) as u32);
                            v___x_7134_ = (crate::leanh::lean_unbox(v_res_7132_) as u16);
                            crate::leanh::lean_dec(v_res_7132_);
                            crate::leanh::lean_ctor_set_uint16(v___x_7133_, 0 as u32, v___x_7134_);
                            v_port_7086_ = v___x_7133_;
                            v___y_7087_ = v_pos_7131_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_7083_);
                            crate::leanh::lean_dec(v_res_7081_);
                            v_pos_7135_ = crate::leanh::lean_ctor_get(v___x_7130_, 0);
                            v_err_7136_ = crate::leanh::lean_ctor_get(v___x_7130_, 1);
                            v_isSharedCheck_7143_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7130_)) as u8;
                            if v_isSharedCheck_7143_ == 0 {
                                v___x_7138_ = v___x_7130_;
                                v_isShared_7139_ = v_isSharedCheck_7143_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_7136_);
                                crate::leanh::lean_inc(v_pos_7135_);
                                crate::leanh::lean_dec(v___x_7130_);
                                v___x_7138_ = crate::leanh::lean_box(0);
                                v_isShared_7139_ = v_isSharedCheck_7143_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            11 => {
                if v_isShared_7139_ == 0 {
                    v___x_7141_ = v___x_7138_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7142_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7142_, 0, v_pos_7135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7142_, 1, v_err_7136_);
                    v___x_7141_ = v_reuseFailAlloc_7142_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7141_;
            }
            13 => {
                if v_isShared_7159_ == 0 {
                    v___x_7161_ = v___x_7158_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7162_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_pos_7155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 1, v_err_7156_);
                    v___x_7161_ = v_reuseFailAlloc_7162_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Parser_parseHostHeader___boxed(
    mut v_config_7164_: *mut crate::leanh::LeanObject,
    mut v_a_7165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7166_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_7164_, v_a_7165_);
    crate::leanh::lean_dec_ref(v_config_7164_);
    return v_res_7166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_URI_Parser(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_URI_Parser(
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
pub unsafe fn initialize_Std_Http_Data_URI_Parser(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_URI_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_URI_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_URI_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_URI_Parser(builtin);
}
