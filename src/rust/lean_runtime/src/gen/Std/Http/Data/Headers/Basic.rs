// Lean compiler output
// Module: Std.Http.Data.Headers.Basic
// Imports: Std.Http.Data.URI Std.Http.Data.Headers.Name Std.Http.Data.Headers.Value Std.Internal.Parsec.Basic Init.Data.String.Search
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_splitToSubslice___redArg, l_String_Slice_toNat_x3f, l_String_Slice_toString,
    l_String_Slice_trimAscii,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::l_Char_utf8Size;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Http::Data::Headers::Name::{
    initialize_Std_Http_Data_Headers_Name, l_Std_Http_Header_Name_connection,
    l_Std_Http_Header_Name_contentLength, l_Std_Http_Header_Name_expect,
    l_Std_Http_Header_Name_transferEncoding, runtime_initialize_Std_Http_Data_Headers_Name,
};
use crate::r#gen::Std::Http::Data::Headers::Value::{
    initialize_Std_Http_Data_Headers_Value, l_Std_Http_Header_Value_ofString_x21,
    runtime_initialize_Std_Http_Data_Headers_Value,
};
use crate::r#gen::Std::Http::Data::URI::Basic::{
    l_Std_Http_URI_instBEqHost_beq, l_Std_Http_URI_instDecidableEqPort_decEq,
    l_Std_Http_URI_instReprPort_repr,
};
use crate::r#gen::Std::Http::Data::URI::Parser::l_Std_Http_URI_Parser_parseHostHeader;
use crate::r#gen::Std::Http::Data::URI::{
    initialize_Std_Http_Data_URI, runtime_initialize_Std_Http_Data_URI,
};
use crate::r#gen::Std::Http::Internal::String::l_Std_Http_Internal_isToken;
use crate::r#gen::Std::Internal::Parsec::Basic::{
    initialize_Std_Internal_Parsec_Basic, runtime_initialize_Std_Internal_Parsec_Basic,
};
use crate::r#gen::Std::Internal::Parsec::ByteArray::l_Std_Internal_Parsec_ByteArray_Parser_run___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint16_to_nat, lean_uint32_add, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Std::Net::Addr::{lean_uv_ntop_v4, lean_uv_ntop_v6};
pub static l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value:
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
    m_data: [58, 32, 0],
};
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value:
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
    m_data: [13, 10, 0],
};
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3_value:
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
    m_data: [45, 0],
};
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5_value:
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
static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instBEqContentLength___closed__0_value:
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
    m_fun: l_Std_Http_Header_instBEqContentLength_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instBEqContentLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqContentLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instBEqContentLength: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqContentLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 101, 110, 103, 116, 104, 0],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprContentLength___closed__0_value:
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
    m_fun: l_Std_Http_Header_instReprContentLength_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instReprContentLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprContentLength: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_ContentLength_inst___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Header_ContentLength_parse as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_ContentLength_inst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_ContentLength_inst___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Header_ContentLength_serialize as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_ContentLength_inst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_ContentLength_inst___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_ContentLength_inst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_ContentLength_inst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_ContentLength_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 104, 117, 110, 107, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_TransferEncoding_Validate___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Http_Header_TransferEncoding_Validate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_Validate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_TransferEncoding_Validate___closed__1_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_Header_TransferEncoding_Validate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_Validate___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 100, 105, 110, 103, 115, 0],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 115, 86, 97, 108, 105, 100, 0],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value:
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
    m_data: [95, 0],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprTransferEncoding___closed__0_value:
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
    m_fun: l_Std_Http_Header_instReprTransferEncoding_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instReprTransferEncoding___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprTransferEncoding: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprTransferEncoding___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_TransferEncoding_inst___closed__0_value:
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
    m_fun: l_Std_Http_Header_TransferEncoding_parse as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_TransferEncoding_inst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_TransferEncoding_inst___closed__1_value:
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
    m_fun: l_Std_Http_Header_TransferEncoding_serialize as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_TransferEncoding_inst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_TransferEncoding_inst___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_TransferEncoding_inst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_TransferEncoding_inst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_TransferEncoding_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 111, 107, 101, 110, 115, 0],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value:
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
    m_data: [118, 97, 108, 105, 100, 0],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Header_instReprConnection_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprConnection___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Header_instReprConnection_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instReprConnection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprConnection: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprConnection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Connection_shouldClose___closed__0_value:
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
    m_data: [99, 108, 111, 115, 101, 0],
};
static mut l_Std_Http_Header_Connection_shouldClose___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Connection_shouldClose___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Connection_inst___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Connection_parse as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Connection_inst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Connection_inst___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Connection_serialize as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Connection_inst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Connection_inst___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_Connection_inst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_Connection_inst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Connection_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value:
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
    m_data: [104, 111, 115, 116, 0],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 72, 111, 115, 116, 46, 0,
    ],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value:
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
    m_data: [112, 111, 114, 116, 0],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__9_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__10_value:
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
    m_data: [105, 112, 118, 52, 0],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost_repr___redArg___closed__11_value:
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
    m_data: [105, 112, 118, 54, 0],
};
static mut l_Std_Http_Header_instReprHost_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprHost___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_instReprHost_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instReprHost___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprHost: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprHost___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instBEqHost___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_instBEqHost_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instBEqHost___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqHost___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instBEqHost: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqHost___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_parse___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105, 110, 112,
        117, 116, 0,
    ],
};
static mut l_Std_Http_Header_Host_parse___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_parse___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_parse___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Http_Header_Host_parse___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Host_parse___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_parse___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_parse___closed__0_value: crate::leanh::LeanCtorObject<9> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9
                + 0) as u16,
            other: 9,
            tag: 0,
        },
        m_objs: [
            (((13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((253 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((256 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((128 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_Host_parse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_parse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_parse___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Host_parse___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_Host_parse___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_Host_parse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_parse___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_serialize___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Std_Http_Header_Host_serialize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_serialize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_serialize___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Std_Http_Header_Host_serialize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_serialize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_inst___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Host_parse___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Host_inst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_inst___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Host_serialize as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Host_inst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Host_inst___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_Host_inst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_Host_inst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Host_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprExpect_repr___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprExpect_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprExpect_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprExpect_repr___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Header_instReprExpect_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprExpect_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprExpect_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprExpect_repr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_instReprExpect_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_instReprExpect_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_instReprExpect_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_instReprExpect___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_instReprExpect_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instReprExpect___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprExpect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprExpect: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprExpect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instBEqExpect___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_instBEqExpect_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instBEqExpect___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqExpect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instBEqExpect: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqExpect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Expect_parse___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [49, 48, 48, 45, 99, 111, 110, 116, 105, 110, 117, 101, 0],
    };
static mut l_Std_Http_Header_Expect_parse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_parse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Expect_parse___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Header_Expect_parse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_parse___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_Expect_serialize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Expect_serialize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Expect_serialize___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Expect_serialize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_Expect_inst___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Expect_parse as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Expect_inst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Expect_inst___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Header_Expect_serialize as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Expect_inst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Expect_inst___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Header_Expect_inst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_Expect_inst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Expect_inst___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(
    mut v___x_1315_: *mut crate::leanh::LeanObject,
    mut v___x_1316_: *mut crate::leanh::LeanObject,
    mut v___x_1317_: *mut crate::leanh::LeanObject,
    mut v_fst_1318_: *mut crate::leanh::LeanObject,
    mut v___x_1319_: *mut crate::leanh::LeanObject,
    mut v___x_1320_: u32,
    mut v___x_1321_: *mut crate::leanh::LeanObject,
    mut v_it_1322_: *mut crate::leanh::LeanObject,
    mut v_acc_1323_: *mut crate::leanh::LeanObject,
    mut v_hP_1324_: *mut crate::leanh::LeanObject,
    mut v_recur_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut v_it_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: u32 = 0;
    let mut v___x_1349_: u32 = 0;
    let mut v___x_1350_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: u32 = 0;
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u32 = 0;
    let mut v___x_1356_: u32 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: u32 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_1322_) == 0 {
                    v_currPos_1358_ = crate::leanh::lean_ctor_get(v_it_1322_, 0);
                    v_searcher_1359_ = crate::leanh::lean_ctor_get(v_it_1322_, 1);
                    v_isSharedCheck_1381_ = (!crate::leanh::lean_is_exclusive(v_it_1322_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1361_ = v_it_1322_;
                        v_isShared_1362_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1359_);
                        crate::leanh::lean_inc(v_currPos_1358_);
                        crate::leanh::lean_dec(v_it_1322_);
                        v___x_1361_ = crate::leanh::lean_box(0);
                        v_isShared_1362_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recur_1325_);
                    crate::leanh::lean_dec(v___x_1319_);
                    return v_acc_1323_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_acc_1323_) == 0 {
                    v___x_1329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1329_, 0, v_out_1328_);
                    v___x_1330_ = crate::leanh::lean_apply_4(
                        v_recur_1325_,
                        v_it_1327_,
                        v___x_1329_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1330_;
                } else {
                    v_val_1331_ = crate::leanh::lean_ctor_get(v_acc_1323_, 0);
                    v_isSharedCheck_1342_ = (!crate::leanh::lean_is_exclusive(v_acc_1323_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1333_ = v_acc_1323_;
                        v_isShared_1334_ = v_isSharedCheck_1342_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1331_);
                        crate::leanh::lean_dec(v_acc_1323_);
                        v___x_1333_ = crate::leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1342_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1335_ = lean_string_utf8_extract(v___x_1315_, v___x_1316_, v___x_1317_);
                v___x_1336_ = lean_string_append(v_val_1331_, v___x_1335_);
                crate::leanh::lean_dec_ref(v___x_1335_);
                v___x_1337_ = lean_string_append(v___x_1336_, v_out_1328_);
                crate::leanh::lean_dec_ref(v_out_1328_);
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1333_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1337_);
                    v___x_1339_ = v_reuseFailAlloc_1341_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1340_ = crate::leanh::lean_apply_4(
                    v_recur_1325_,
                    v_it_1327_,
                    v___x_1339_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1340_;
            }
            4 => {
                v___x_1347_ = lean_string_utf8_extract(
                    v_fst_1318_,
                    v_startInclusive_1345_,
                    v_endExclusive_1346_,
                );
                crate::leanh::lean_dec(v_endExclusive_1346_);
                crate::leanh::lean_dec(v_startInclusive_1345_);
                v___x_1348_ = lean_string_utf8_get(v___x_1347_, v___x_1316_);
                v___x_1349_ = 97;
                v___x_1350_ = lean_uint32_dec_le(v___x_1349_, v___x_1348_);
                if v___x_1350_ == 0 {
                    v___x_1351_ = lean_string_utf8_set(v___x_1347_, v___x_1316_, v___x_1348_);
                    v_it_1327_ = v_it_1344_;
                    v_out_1328_ = v___x_1351_;
                    state = 1;
                    continue;
                } else {
                    v___x_1352_ = 122;
                    v___x_1353_ = lean_uint32_dec_le(v___x_1348_, v___x_1352_);
                    if v___x_1353_ == 0 {
                        v___x_1354_ = lean_string_utf8_set(v___x_1347_, v___x_1316_, v___x_1348_);
                        v_it_1327_ = v_it_1344_;
                        v_out_1328_ = v___x_1354_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1355_ = 4294967264;
                        v___x_1356_ = lean_uint32_add(v___x_1348_, v___x_1355_);
                        v___x_1357_ = lean_string_utf8_set(v___x_1347_, v___x_1316_, v___x_1356_);
                        v_it_1327_ = v_it_1344_;
                        v_out_1328_ = v___x_1357_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1363_ = lean_nat_dec_eq(v_searcher_1359_, v___x_1319_);
                if v___x_1363_ == 0 {
                    crate::leanh::lean_dec(v___x_1319_);
                    v___x_1364_ = lean_string_utf8_get_fast(v_fst_1318_, v_searcher_1359_);
                    v___x_1365_ = lean_uint32_dec_eq(v___x_1364_, v___x_1320_);
                    if v___x_1365_ == 0 {
                        v___x_1366_ = lean_string_utf8_next_fast(v_fst_1318_, v_searcher_1359_);
                        crate::leanh::lean_dec(v_searcher_1359_);
                        if v_isShared_1362_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1361_, 1, v___x_1366_);
                            v___x_1368_ = v___x_1361_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1370_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_currPos_1358_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1366_);
                            v___x_1368_ = v_reuseFailAlloc_1370_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1371_ = lean_string_utf8_next_fast(v_fst_1318_, v_searcher_1359_);
                        v___x_1372_ = lean_nat_sub(v___x_1371_, v_searcher_1359_);
                        v___x_1373_ = lean_nat_add(v_searcher_1359_, v___x_1372_);
                        crate::leanh::lean_dec(v___x_1372_);
                        v_slice_1374_ = l_String_Slice_subslice_x21(
                            v___x_1321_,
                            v_currPos_1358_,
                            v_searcher_1359_,
                        );
                        crate::leanh::lean_inc(v___x_1373_);
                        if v_isShared_1362_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1361_, 1, v___x_1373_);
                            crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1373_);
                            v_nextIt_1376_ = v___x_1361_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1379_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1373_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1373_);
                            v_nextIt_1376_ = v_reuseFailAlloc_1379_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1361_);
                    crate::leanh::lean_dec(v_searcher_1359_);
                    v___x_1380_ = crate::leanh::lean_box(1);
                    v_it_1344_ = v___x_1380_;
                    v_startInclusive_1345_ = v_currPos_1358_;
                    v_endExclusive_1346_ = v___x_1319_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1369_ = crate::leanh::lean_apply_4(
                    v_recur_1325_,
                    v___x_1368_,
                    v_acc_1323_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1369_;
            }
            7 => {
                v_startInclusive_1377_ = crate::leanh::lean_ctor_get(v_slice_1374_, 0);
                crate::leanh::lean_inc(v_startInclusive_1377_);
                v_endExclusive_1378_ = crate::leanh::lean_ctor_get(v_slice_1374_, 1);
                crate::leanh::lean_inc(v_endExclusive_1378_);
                crate::leanh::lean_dec_ref(v_slice_1374_);
                v_it_1344_ = v_nextIt_1376_;
                v_startInclusive_1345_ = v_startInclusive_1377_;
                v_endExclusive_1346_ = v_endExclusive_1378_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(
    mut v___x_1382_: *mut crate::leanh::LeanObject,
    mut v___x_1383_: *mut crate::leanh::LeanObject,
    mut v___x_1384_: *mut crate::leanh::LeanObject,
    mut v_fst_1385_: *mut crate::leanh::LeanObject,
    mut v___x_1386_: *mut crate::leanh::LeanObject,
    mut v___x_1387_: *mut crate::leanh::LeanObject,
    mut v___x_1388_: *mut crate::leanh::LeanObject,
    mut v_it_1389_: *mut crate::leanh::LeanObject,
    mut v_acc_1390_: *mut crate::leanh::LeanObject,
    mut v_hP_1391_: *mut crate::leanh::LeanObject,
    mut v_recur_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1336__boxed_1393_: u32 = 0;
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1336__boxed_1393_ = crate::leanh::lean_unbox_uint32(v___x_1387_);
    crate::leanh::lean_dec(v___x_1387_);
    v_res_1394_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(
        v___x_1382_,
        v___x_1383_,
        v___x_1384_,
        v_fst_1385_,
        v___x_1386_,
        v___x_1336__boxed_1393_,
        v___x_1388_,
        v_it_1389_,
        v_acc_1390_,
        v_hP_1391_,
        v_recur_1392_,
    );
    crate::leanh::lean_dec_ref(v___x_1388_);
    crate::leanh::lean_dec_ref(v_fst_1385_);
    crate::leanh::lean_dec(v___x_1384_);
    crate::leanh::lean_dec(v___x_1383_);
    crate::leanh::lean_dec_ref(v___x_1382_);
    return v_res_1394_;
}
pub unsafe fn _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3;
    v___x_1400_ = lean_string_utf8_byte_size(v___x_1399_);
    return v___x_1400_;
}
pub unsafe fn _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: u32 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = 45;
    v___x_1403_ = crate::leanh::lean_box_uint32(v___x_1402_);
    return v___x_1403_;
}
pub unsafe fn l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(
    mut v_h_1404_: *mut crate::leanh::LeanObject,
    mut v_buffer_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serialize_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut v___f_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_serialize_1407_ = crate::leanh::lean_ctor_get(v_h_1404_, 1);
                crate::leanh::lean_inc_ref(v_serialize_1407_);
                crate::leanh::lean_dec_ref(v_h_1404_);
                v___x_1408_ = crate::leanh::lean_apply_1(v_serialize_1407_, v_a_1406_);
                v_fst_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                crate::leanh::lean_inc_n(v_fst_1409_, 2);
                v_snd_1410_ = crate::leanh::lean_ctor_get(v___x_1408_, 1);
                crate::leanh::lean_inc(v_snd_1410_);
                crate::leanh::lean_dec_ref(v___x_1408_);
                v___f_1431_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2;
                v___x_1432_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1433_ = lean_string_utf8_byte_size(v_fst_1409_);
                v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1434_, 0, v_fst_1409_);
                crate::leanh::lean_ctor_set(v___x_1434_, 1, v___x_1432_);
                crate::leanh::lean_ctor_set(v___x_1434_, 2, v___x_1433_);
                crate::leanh::lean_inc_ref(v___x_1434_);
                v_it_1435_ = l_String_Slice_splitToSubslice___redArg(v___x_1434_, v___f_1431_);
                v___x_1436_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3;
                v___x_1437_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_once
                    ),
                    _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4,
                );
                v___x_1438_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
                v___f_1439_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_1439_, 0, v___x_1436_);
                crate::leanh::lean_closure_set(v___f_1439_, 1, v___x_1432_);
                crate::leanh::lean_closure_set(v___f_1439_, 2, v___x_1437_);
                crate::leanh::lean_closure_set(v___f_1439_, 3, v_fst_1409_);
                crate::leanh::lean_closure_set(v___f_1439_, 4, v___x_1433_);
                crate::leanh::lean_closure_set(v___f_1439_, 5, v___x_1438_);
                crate::leanh::lean_closure_set(v___f_1439_, 6, v___x_1434_);
                v___x_1440_ = crate::leanh::lean_box(0);
                v___x_1441_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1439_,
                    v_it_1435_,
                    v___x_1440_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1441_) == 0 {
                    v___x_1442_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5;
                    v___y_1412_ = v___x_1442_;
                    state = 1;
                    continue;
                } else {
                    v_val_1443_ = crate::leanh::lean_ctor_get(v___x_1441_, 0);
                    crate::leanh::lean_inc(v_val_1443_);
                    crate::leanh::lean_dec_ref_known(v___x_1441_, 1);
                    v___y_1412_ = v_val_1443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_1413_ = crate::leanh::lean_ctor_get(v_buffer_1405_, 0);
                v_size_1414_ = crate::leanh::lean_ctor_get(v_buffer_1405_, 1);
                v_isSharedCheck_1430_ = (!crate::leanh::lean_is_exclusive(v_buffer_1405_)) as u8;
                if v_isSharedCheck_1430_ == 0 {
                    v___x_1416_ = v_buffer_1405_;
                    v_isShared_1417_ = v_isSharedCheck_1430_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_1414_);
                    crate::leanh::lean_inc(v_data_1413_);
                    crate::leanh::lean_dec(v_buffer_1405_);
                    v___x_1416_ = crate::leanh::lean_box(0);
                    v_isShared_1417_ = v_isSharedCheck_1430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1418_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0;
                v___x_1419_ = lean_string_append(v___y_1412_, v___x_1418_);
                v___x_1420_ = lean_string_append(v___x_1419_, v_snd_1410_);
                crate::leanh::lean_dec(v_snd_1410_);
                v___x_1421_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1;
                v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
                v___x_1423_ = lean_string_to_utf8(v___x_1422_);
                crate::leanh::lean_dec_ref(v___x_1422_);
                crate::leanh::lean_inc_ref(v___x_1423_);
                v___x_1424_ = lean_array_push(v_data_1413_, v___x_1423_);
                v___x_1425_ = lean_byte_array_size(v___x_1423_);
                crate::leanh::lean_dec_ref(v___x_1423_);
                v___x_1426_ = lean_nat_add(v_size_1414_, v___x_1425_);
                crate::leanh::lean_dec(v_size_1414_);
                if v_isShared_1417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1416_, 1, v___x_1426_);
                    crate::leanh::lean_ctor_set(v___x_1416_, 0, v___x_1424_);
                    v___x_1428_ = v___x_1416_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
                    v___x_1428_ = v_reuseFailAlloc_1429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instEncodeV11OfHeader___redArg(
    mut v_h_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1445_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_instEncodeV11OfHeader___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1445_, 0, v_h_1444_);
    return v___f_1445_;
}
pub unsafe fn l_Std_Http_instEncodeV11OfHeader(
    mut v_00_u03b1_1446_: *mut crate::leanh::LeanObject,
    mut v_h_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1448_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_instEncodeV11OfHeader___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1448_, 0, v_h_1447_);
    return v___f_1448_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(
    mut v_s_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0;
    return v___x_1452_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(
    mut v_s_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_1453_);
    crate::leanh::lean_dec_ref(v_s_1453_);
    return v_res_1454_;
}
pub unsafe fn l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(
    mut v_s_1455_: *mut crate::leanh::LeanObject,
    mut v_p_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1458_: u32 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: u32 = 0;
    let mut v___x_1466_: u32 = 0;
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: u32 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: u32 = 0;
    let mut v___x_1471_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1463_ = lean_string_utf8_byte_size(v_s_1455_);
                v___x_1464_ = lean_nat_dec_eq(v_p_1456_, v___x_1463_);
                if v___x_1464_ == 0 {
                    v___x_1465_ = lean_string_utf8_get_fast(v_s_1455_, v_p_1456_);
                    v___x_1466_ = 65;
                    v___x_1467_ = lean_uint32_dec_le(v___x_1466_, v___x_1465_);
                    if v___x_1467_ == 0 {
                        v___y_1458_ = v___x_1465_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1468_ = 90;
                        v___x_1469_ = lean_uint32_dec_le(v___x_1465_, v___x_1468_);
                        if v___x_1469_ == 0 {
                            v___y_1458_ = v___x_1465_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1470_ = 32;
                            v___x_1471_ = lean_uint32_add(v___x_1465_, v___x_1470_);
                            v___y_1458_ = v___x_1471_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_1456_);
                    return v_s_1455_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_1456_);
                v___x_1459_ = lean_string_utf8_set(v_s_1455_, v_p_1456_, v___y_1458_);
                v___x_1460_ = l_Char_utf8Size(v___y_1458_);
                v___x_1461_ = lean_nat_add(v_p_1456_, v___x_1460_);
                crate::leanh::lean_dec(v___x_1460_);
                crate::leanh::lean_dec(v_p_1456_);
                v_s_1455_ = v___x_1459_;
                v_p_1456_ = v___x_1461_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(
    mut v_sz_1472_: usize,
    mut v_i_1473_: usize,
    mut v_bs_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1475_: u8 = 0;
    let mut v_v_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: usize = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1475_ = lean_usize_dec_lt(v_i_1473_, v_sz_1472_);
                if v___x_1475_ == 0 {
                    return v_bs_1474_;
                } else {
                    v_v_1476_ = lean_array_uget(v_bs_1474_, v_i_1473_);
                    v___x_1477_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1478_ = lean_array_uset(v_bs_1474_, v_i_1473_, v___x_1477_);
                    v___x_1479_ = l_String_Slice_toString(v_v_1476_);
                    crate::leanh::lean_dec(v_v_1476_);
                    v___x_1480_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1479_, v___x_1477_);
                    v___x_1481_ = 1usize;
                    v___x_1482_ = lean_usize_add(v_i_1473_, v___x_1481_);
                    v___x_1483_ = lean_array_uset(v_bs_x27_1478_, v_i_1473_, v___x_1480_);
                    v_i_1473_ = v___x_1482_;
                    v_bs_1474_ = v___x_1483_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(
    mut v_sz_1485_: *mut crate::leanh::LeanObject,
    mut v_i_1486_: *mut crate::leanh::LeanObject,
    mut v_bs_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1488_: usize = 0;
    let mut v_i_boxed_1489_: usize = 0;
    let mut v_res_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1488_ = crate::leanh::lean_unbox_usize(v_sz_1485_);
    crate::leanh::lean_dec(v_sz_1485_);
    v_i_boxed_1489_ = crate::leanh::lean_unbox_usize(v_i_1486_);
    crate::leanh::lean_dec(v_i_1486_);
    v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_1488_, v_i_boxed_1489_, v_bs_1487_);
    return v_res_1490_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(
    mut v___x_1491_: *mut crate::leanh::LeanObject,
    mut v___x_1492_: *mut crate::leanh::LeanObject,
    mut v___x_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
    mut v_b_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v_str_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: u32 = 0;
    let mut v___x_1516_: u32 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1494_) == 0 {
                    v_currPos_1504_ = crate::leanh::lean_ctor_get(v_a_1494_, 0);
                    v_searcher_1505_ = crate::leanh::lean_ctor_get(v_a_1494_, 1);
                    v_isSharedCheck_1534_ = (!crate::leanh::lean_is_exclusive(v_a_1494_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v___x_1507_ = v_a_1494_;
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1505_);
                        crate::leanh::lean_inc(v_currPos_1504_);
                        crate::leanh::lean_dec(v_a_1494_);
                        v___x_1507_ = crate::leanh::lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1493_);
                    crate::leanh::lean_dec_ref(v___x_1491_);
                    return v_b_1495_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_1491_);
                v___x_1500_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1491_);
                crate::leanh::lean_ctor_set(v___x_1500_, 1, v_startInclusive_1498_);
                crate::leanh::lean_ctor_set(v___x_1500_, 2, v_endExclusive_1499_);
                v___x_1501_ = l_String_Slice_trimAscii(v___x_1500_);
                v___x_1502_ = lean_array_push(v_b_1495_, v___x_1501_);
                v_a_1494_ = v_it_1497_;
                v_b_1495_ = v___x_1502_;
                state = 0;
                continue;
            }
            2 => {
                v_str_1509_ = crate::leanh::lean_ctor_get(v___x_1492_, 0);
                v_startInclusive_1510_ = crate::leanh::lean_ctor_get(v___x_1492_, 1);
                v_endExclusive_1511_ = crate::leanh::lean_ctor_get(v___x_1492_, 2);
                v___x_1512_ = lean_nat_sub(v_endExclusive_1511_, v_startInclusive_1510_);
                v___x_1513_ = lean_nat_dec_eq(v_searcher_1505_, v___x_1512_);
                crate::leanh::lean_dec(v___x_1512_);
                if v___x_1513_ == 0 {
                    v___x_1514_ = lean_nat_add(v_startInclusive_1510_, v_searcher_1505_);
                    v___x_1515_ = lean_string_utf8_get_fast(v_str_1509_, v___x_1514_);
                    v___x_1516_ = 44;
                    v___x_1517_ = lean_uint32_dec_eq(v___x_1515_, v___x_1516_);
                    if v___x_1517_ == 0 {
                        crate::leanh::lean_dec(v_searcher_1505_);
                        v___x_1518_ = lean_string_utf8_next_fast(v_str_1509_, v___x_1514_);
                        crate::leanh::lean_dec(v___x_1514_);
                        v___x_1519_ = lean_nat_sub(v___x_1518_, v_startInclusive_1510_);
                        if v_isShared_1508_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1519_);
                            v___x_1521_ = v___x_1507_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1523_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_currPos_1504_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1519_);
                            v___x_1521_ = v_reuseFailAlloc_1523_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1524_ = lean_string_utf8_next_fast(v_str_1509_, v___x_1514_);
                        v___x_1525_ = lean_nat_sub(v___x_1524_, v___x_1514_);
                        crate::leanh::lean_dec(v___x_1514_);
                        v___x_1526_ = lean_nat_add(v_searcher_1505_, v___x_1525_);
                        crate::leanh::lean_dec(v___x_1525_);
                        v_slice_1527_ = l_String_Slice_subslice_x21(
                            v___x_1492_,
                            v_currPos_1504_,
                            v_searcher_1505_,
                        );
                        crate::leanh::lean_inc(v___x_1526_);
                        if v_isShared_1508_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1526_);
                            crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1526_);
                            v_nextIt_1529_ = v___x_1507_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1532_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1526_);
                            v_nextIt_1529_ = v_reuseFailAlloc_1532_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1507_);
                    crate::leanh::lean_dec(v_searcher_1505_);
                    v___x_1533_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1493_);
                    v_it_1497_ = v___x_1533_;
                    v_startInclusive_1498_ = v_currPos_1504_;
                    v_endExclusive_1499_ = v___x_1493_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1494_ = v___x_1521_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1530_ = crate::leanh::lean_ctor_get(v_slice_1527_, 0);
                crate::leanh::lean_inc(v_startInclusive_1530_);
                v_endExclusive_1531_ = crate::leanh::lean_ctor_get(v_slice_1527_, 1);
                crate::leanh::lean_inc(v_endExclusive_1531_);
                crate::leanh::lean_dec_ref(v_slice_1527_);
                v_it_1497_ = v_nextIt_1529_;
                v_startInclusive_1498_ = v_startInclusive_1530_;
                v_endExclusive_1499_ = v_endExclusive_1531_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(
    mut v___x_1535_: *mut crate::leanh::LeanObject,
    mut v___x_1536_: *mut crate::leanh::LeanObject,
    mut v___x_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_b_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_1535_, v___x_1536_, v___x_1537_, v_a_1538_, v_b_1539_);
    crate::leanh::lean_dec_ref(v___x_1536_);
    return v_res_1540_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(
    mut v___x_1541_: *mut crate::leanh::LeanObject,
    mut v___x_1542_: *mut crate::leanh::LeanObject,
    mut v___x_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_b_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v_str_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u32 = 0;
    let mut v___x_1566_: u32 = 0;
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1544_) == 0 {
                    v_currPos_1554_ = crate::leanh::lean_ctor_get(v_a_1544_, 0);
                    v_searcher_1555_ = crate::leanh::lean_ctor_get(v_a_1544_, 1);
                    v_isSharedCheck_1584_ = (!crate::leanh::lean_is_exclusive(v_a_1544_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v___x_1557_ = v_a_1544_;
                        v_isShared_1558_ = v_isSharedCheck_1584_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1555_);
                        crate::leanh::lean_inc(v_currPos_1554_);
                        crate::leanh::lean_dec(v_a_1544_);
                        v___x_1557_ = crate::leanh::lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1584_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1543_);
                    crate::leanh::lean_dec_ref(v___x_1541_);
                    return v_b_1545_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_1541_);
                v___x_1550_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1550_, 0, v___x_1541_);
                crate::leanh::lean_ctor_set(v___x_1550_, 1, v_startInclusive_1548_);
                crate::leanh::lean_ctor_set(v___x_1550_, 2, v_endExclusive_1549_);
                v___x_1551_ = l_String_Slice_trimAscii(v___x_1550_);
                v___x_1552_ = lean_array_push(v_b_1545_, v___x_1551_);
                v___x_1553_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_1541_, v___x_1542_, v___x_1543_, v_it_1547_, v___x_1552_);
                return v___x_1553_;
            }
            2 => {
                v_str_1559_ = crate::leanh::lean_ctor_get(v___x_1542_, 0);
                v_startInclusive_1560_ = crate::leanh::lean_ctor_get(v___x_1542_, 1);
                v_endExclusive_1561_ = crate::leanh::lean_ctor_get(v___x_1542_, 2);
                v___x_1562_ = lean_nat_sub(v_endExclusive_1561_, v_startInclusive_1560_);
                v___x_1563_ = lean_nat_dec_eq(v_searcher_1555_, v___x_1562_);
                crate::leanh::lean_dec(v___x_1562_);
                if v___x_1563_ == 0 {
                    v___x_1564_ = lean_nat_add(v_startInclusive_1560_, v_searcher_1555_);
                    v___x_1565_ = lean_string_utf8_get_fast(v_str_1559_, v___x_1564_);
                    v___x_1566_ = 44;
                    v___x_1567_ = lean_uint32_dec_eq(v___x_1565_, v___x_1566_);
                    if v___x_1567_ == 0 {
                        crate::leanh::lean_dec(v_searcher_1555_);
                        v___x_1568_ = lean_string_utf8_next_fast(v_str_1559_, v___x_1564_);
                        crate::leanh::lean_dec(v___x_1564_);
                        v___x_1569_ = lean_nat_sub(v___x_1568_, v_startInclusive_1560_);
                        if v_isShared_1558_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1569_);
                            v___x_1571_ = v___x_1557_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1573_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_currPos_1554_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1569_);
                            v___x_1571_ = v_reuseFailAlloc_1573_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1574_ = lean_string_utf8_next_fast(v_str_1559_, v___x_1564_);
                        v___x_1575_ = lean_nat_sub(v___x_1574_, v___x_1564_);
                        crate::leanh::lean_dec(v___x_1564_);
                        v___x_1576_ = lean_nat_add(v_searcher_1555_, v___x_1575_);
                        crate::leanh::lean_dec(v___x_1575_);
                        v_slice_1577_ = l_String_Slice_subslice_x21(
                            v___x_1542_,
                            v_currPos_1554_,
                            v_searcher_1555_,
                        );
                        crate::leanh::lean_inc(v___x_1576_);
                        if v_isShared_1558_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1576_);
                            crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1576_);
                            v_nextIt_1579_ = v___x_1557_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1582_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1576_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1576_);
                            v_nextIt_1579_ = v_reuseFailAlloc_1582_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1557_);
                    crate::leanh::lean_dec(v_searcher_1555_);
                    v___x_1583_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1543_);
                    v_it_1547_ = v___x_1583_;
                    v_startInclusive_1548_ = v_currPos_1554_;
                    v_endExclusive_1549_ = v___x_1543_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1572_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_1541_, v___x_1542_, v___x_1543_, v___x_1571_, v_b_1545_);
                return v___x_1572_;
            }
            4 => {
                v_startInclusive_1580_ = crate::leanh::lean_ctor_get(v_slice_1577_, 0);
                crate::leanh::lean_inc(v_startInclusive_1580_);
                v_endExclusive_1581_ = crate::leanh::lean_ctor_get(v_slice_1577_, 1);
                crate::leanh::lean_inc(v_endExclusive_1581_);
                crate::leanh::lean_dec_ref(v_slice_1577_);
                v_it_1547_ = v_nextIt_1579_;
                v_startInclusive_1548_ = v_startInclusive_1580_;
                v_endExclusive_1549_ = v_endExclusive_1581_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(
    mut v___x_1585_: *mut crate::leanh::LeanObject,
    mut v___x_1586_: *mut crate::leanh::LeanObject,
    mut v___x_1587_: *mut crate::leanh::LeanObject,
    mut v_a_1588_: *mut crate::leanh::LeanObject,
    mut v_b_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_1585_, v___x_1586_, v___x_1587_, v_a_1588_, v_b_1589_);
    crate::leanh::lean_dec_ref(v___x_1586_);
    return v_res_1590_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(
    mut v___x_1591_: *mut crate::leanh::LeanObject,
    mut v___x_1592_: *mut crate::leanh::LeanObject,
    mut v___x_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_b_1595_: u8,
) -> u8 {
    let mut v_currPos_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v_str_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    let mut v_it_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u32 = 0;
    let mut v___x_1622_: u32 = 0;
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1594_) == 0 {
                    v_currPos_1596_ = crate::leanh::lean_ctor_get(v_a_1594_, 0);
                    v_searcher_1597_ = crate::leanh::lean_ctor_get(v_a_1594_, 1);
                    v_isSharedCheck_1640_ = (!crate::leanh::lean_is_exclusive(v_a_1594_)) as u8;
                    if v_isSharedCheck_1640_ == 0 {
                        v___x_1599_ = v_a_1594_;
                        v_isShared_1600_ = v_isSharedCheck_1640_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1597_);
                        crate::leanh::lean_inc(v_currPos_1596_);
                        crate::leanh::lean_dec(v_a_1594_);
                        v___x_1599_ = crate::leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1640_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1593_);
                    crate::leanh::lean_dec_ref(v___x_1591_);
                    return v_b_1595_;
                }
            }
            1 => {
                v_str_1601_ = crate::leanh::lean_ctor_get(v___x_1592_, 0);
                v_startInclusive_1602_ = crate::leanh::lean_ctor_get(v___x_1592_, 1);
                v_endExclusive_1603_ = crate::leanh::lean_ctor_get(v___x_1592_, 2);
                v___x_1604_ = 1;
                v___x_1618_ = lean_nat_sub(v_endExclusive_1603_, v_startInclusive_1602_);
                v___x_1619_ = lean_nat_dec_eq(v_searcher_1597_, v___x_1618_);
                crate::leanh::lean_dec(v___x_1618_);
                if v___x_1619_ == 0 {
                    v___x_1620_ = lean_nat_add(v_startInclusive_1602_, v_searcher_1597_);
                    v___x_1621_ = lean_string_utf8_get_fast(v_str_1601_, v___x_1620_);
                    v___x_1622_ = 44;
                    v___x_1623_ = lean_uint32_dec_eq(v___x_1621_, v___x_1622_);
                    if v___x_1623_ == 0 {
                        crate::leanh::lean_dec(v_searcher_1597_);
                        v___x_1624_ = lean_string_utf8_next_fast(v_str_1601_, v___x_1620_);
                        crate::leanh::lean_dec(v___x_1620_);
                        v___x_1625_ = lean_nat_sub(v___x_1624_, v_startInclusive_1602_);
                        if v_isShared_1600_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1599_, 1, v___x_1625_);
                            v___x_1627_ = v___x_1599_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1629_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_currPos_1596_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1625_);
                            v___x_1627_ = v_reuseFailAlloc_1629_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1630_ = lean_string_utf8_next_fast(v_str_1601_, v___x_1620_);
                        v___x_1631_ = lean_nat_sub(v___x_1630_, v___x_1620_);
                        crate::leanh::lean_dec(v___x_1620_);
                        v___x_1632_ = lean_nat_add(v_searcher_1597_, v___x_1631_);
                        crate::leanh::lean_dec(v___x_1631_);
                        v_slice_1633_ = l_String_Slice_subslice_x21(
                            v___x_1592_,
                            v_currPos_1596_,
                            v_searcher_1597_,
                        );
                        crate::leanh::lean_inc(v___x_1632_);
                        if v_isShared_1600_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1599_, 1, v___x_1632_);
                            crate::leanh::lean_ctor_set(v___x_1599_, 0, v___x_1632_);
                            v_nextIt_1635_ = v___x_1599_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1638_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1632_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1632_);
                            v_nextIt_1635_ = v_reuseFailAlloc_1638_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1599_);
                    crate::leanh::lean_dec(v_searcher_1597_);
                    v___x_1639_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1593_);
                    v_it_1606_ = v___x_1639_;
                    v_startInclusive_1607_ = v_currPos_1596_;
                    v_endExclusive_1608_ = v___x_1593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_1591_);
                v___x_1609_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1591_);
                crate::leanh::lean_ctor_set(v___x_1609_, 1, v_startInclusive_1607_);
                crate::leanh::lean_ctor_set(v___x_1609_, 2, v_endExclusive_1608_);
                v___x_1610_ = l_String_Slice_trimAscii(v___x_1609_);
                v_startInclusive_1611_ = crate::leanh::lean_ctor_get(v___x_1610_, 1);
                crate::leanh::lean_inc(v_startInclusive_1611_);
                v_endExclusive_1612_ = crate::leanh::lean_ctor_get(v___x_1610_, 2);
                crate::leanh::lean_inc(v_endExclusive_1612_);
                crate::leanh::lean_dec_ref(v___x_1610_);
                v___x_1613_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
                crate::leanh::lean_dec(v_startInclusive_1611_);
                crate::leanh::lean_dec(v_endExclusive_1612_);
                v___x_1614_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1615_ = lean_nat_dec_eq(v___x_1613_, v___x_1614_);
                crate::leanh::lean_dec(v___x_1613_);
                if v___x_1615_ == 0 {
                    v_a_1594_ = v_it_1606_;
                    v_b_1595_ = v___x_1604_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_it_1606_);
                    crate::leanh::lean_dec(v___x_1593_);
                    crate::leanh::lean_dec_ref(v___x_1591_);
                    v___x_1617_ = 0;
                    return v___x_1617_;
                }
            }
            3 => {
                v_a_1594_ = v___x_1627_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1636_ = crate::leanh::lean_ctor_get(v_slice_1633_, 0);
                crate::leanh::lean_inc(v_startInclusive_1636_);
                v_endExclusive_1637_ = crate::leanh::lean_ctor_get(v_slice_1633_, 1);
                crate::leanh::lean_inc(v_endExclusive_1637_);
                crate::leanh::lean_dec_ref(v_slice_1633_);
                v_it_1606_ = v_nextIt_1635_;
                v_startInclusive_1607_ = v_startInclusive_1636_;
                v_endExclusive_1608_ = v_endExclusive_1637_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(
    mut v___x_1641_: *mut crate::leanh::LeanObject,
    mut v___x_1642_: *mut crate::leanh::LeanObject,
    mut v___x_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_b_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1646_: u8 = 0;
    let mut v_res_1647_: u8 = 0;
    let mut v_r_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1646_ = (crate::leanh::lean_unbox(v_b_1645_) as u8);
    v_res_1647_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_1641_, v___x_1642_, v___x_1643_, v_a_1644_, v_b_boxed_1646_);
    crate::leanh::lean_dec_ref(v___x_1642_);
    v_r_1648_ = crate::leanh::lean_box((v_res_1647_) as usize);
    return v_r_1648_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(
    mut v___x_1649_: *mut crate::leanh::LeanObject,
    mut v___x_1650_: *mut crate::leanh::LeanObject,
    mut v___x_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_b_1653_: u8,
) -> u8 {
    let mut v_currPos_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v_str_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v_it_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u32 = 0;
    let mut v___x_1680_: u32 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v_reuseFailAlloc_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1652_) == 0 {
                    v_currPos_1654_ = crate::leanh::lean_ctor_get(v_a_1652_, 0);
                    v_searcher_1655_ = crate::leanh::lean_ctor_get(v_a_1652_, 1);
                    v_isSharedCheck_1698_ = (!crate::leanh::lean_is_exclusive(v_a_1652_)) as u8;
                    if v_isSharedCheck_1698_ == 0 {
                        v___x_1657_ = v_a_1652_;
                        v_isShared_1658_ = v_isSharedCheck_1698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1655_);
                        crate::leanh::lean_inc(v_currPos_1654_);
                        crate::leanh::lean_dec(v_a_1652_);
                        v___x_1657_ = crate::leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1698_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1651_);
                    crate::leanh::lean_dec_ref(v___x_1649_);
                    return v_b_1653_;
                }
            }
            1 => {
                v_str_1659_ = crate::leanh::lean_ctor_get(v___x_1650_, 0);
                v_startInclusive_1660_ = crate::leanh::lean_ctor_get(v___x_1650_, 1);
                v_endExclusive_1661_ = crate::leanh::lean_ctor_get(v___x_1650_, 2);
                v___x_1662_ = 1;
                v___x_1676_ = lean_nat_sub(v_endExclusive_1661_, v_startInclusive_1660_);
                v___x_1677_ = lean_nat_dec_eq(v_searcher_1655_, v___x_1676_);
                crate::leanh::lean_dec(v___x_1676_);
                if v___x_1677_ == 0 {
                    v___x_1678_ = lean_nat_add(v_startInclusive_1660_, v_searcher_1655_);
                    v___x_1679_ = lean_string_utf8_get_fast(v_str_1659_, v___x_1678_);
                    v___x_1680_ = 44;
                    v___x_1681_ = lean_uint32_dec_eq(v___x_1679_, v___x_1680_);
                    if v___x_1681_ == 0 {
                        crate::leanh::lean_dec(v_searcher_1655_);
                        v___x_1682_ = lean_string_utf8_next_fast(v_str_1659_, v___x_1678_);
                        crate::leanh::lean_dec(v___x_1678_);
                        v___x_1683_ = lean_nat_sub(v___x_1682_, v_startInclusive_1660_);
                        if v_isShared_1658_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1683_);
                            v___x_1685_ = v___x_1657_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1687_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_currPos_1654_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1683_);
                            v___x_1685_ = v_reuseFailAlloc_1687_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1688_ = lean_string_utf8_next_fast(v_str_1659_, v___x_1678_);
                        v___x_1689_ = lean_nat_sub(v___x_1688_, v___x_1678_);
                        crate::leanh::lean_dec(v___x_1678_);
                        v___x_1690_ = lean_nat_add(v_searcher_1655_, v___x_1689_);
                        crate::leanh::lean_dec(v___x_1689_);
                        v_slice_1691_ = l_String_Slice_subslice_x21(
                            v___x_1650_,
                            v_currPos_1654_,
                            v_searcher_1655_,
                        );
                        crate::leanh::lean_inc(v___x_1690_);
                        if v_isShared_1658_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1690_);
                            crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1690_);
                            v_nextIt_1693_ = v___x_1657_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1696_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1690_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1690_);
                            v_nextIt_1693_ = v_reuseFailAlloc_1696_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1657_);
                    crate::leanh::lean_dec(v_searcher_1655_);
                    v___x_1697_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1651_);
                    v_it_1664_ = v___x_1697_;
                    v_startInclusive_1665_ = v_currPos_1654_;
                    v_endExclusive_1666_ = v___x_1651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_1649_);
                v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1649_);
                crate::leanh::lean_ctor_set(v___x_1667_, 1, v_startInclusive_1665_);
                crate::leanh::lean_ctor_set(v___x_1667_, 2, v_endExclusive_1666_);
                v___x_1668_ = l_String_Slice_trimAscii(v___x_1667_);
                v_startInclusive_1669_ = crate::leanh::lean_ctor_get(v___x_1668_, 1);
                crate::leanh::lean_inc(v_startInclusive_1669_);
                v_endExclusive_1670_ = crate::leanh::lean_ctor_get(v___x_1668_, 2);
                crate::leanh::lean_inc(v_endExclusive_1670_);
                crate::leanh::lean_dec_ref(v___x_1668_);
                v___x_1671_ = lean_nat_sub(v_endExclusive_1670_, v_startInclusive_1669_);
                crate::leanh::lean_dec(v_startInclusive_1669_);
                crate::leanh::lean_dec(v_endExclusive_1670_);
                v___x_1672_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1673_ = lean_nat_dec_eq(v___x_1671_, v___x_1672_);
                crate::leanh::lean_dec(v___x_1671_);
                if v___x_1673_ == 0 {
                    v___x_1674_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_1649_, v___x_1650_, v___x_1651_, v_it_1664_, v___x_1662_);
                    return v___x_1674_;
                } else {
                    crate::leanh::lean_dec(v_it_1664_);
                    crate::leanh::lean_dec(v___x_1651_);
                    crate::leanh::lean_dec_ref(v___x_1649_);
                    v___x_1675_ = 0;
                    return v___x_1675_;
                }
            }
            3 => {
                v___x_1686_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_1649_, v___x_1650_, v___x_1651_, v___x_1685_, v_b_1653_);
                return v___x_1686_;
            }
            4 => {
                v_startInclusive_1694_ = crate::leanh::lean_ctor_get(v_slice_1691_, 0);
                crate::leanh::lean_inc(v_startInclusive_1694_);
                v_endExclusive_1695_ = crate::leanh::lean_ctor_get(v_slice_1691_, 1);
                crate::leanh::lean_inc(v_endExclusive_1695_);
                crate::leanh::lean_dec_ref(v_slice_1691_);
                v_it_1664_ = v_nextIt_1693_;
                v_startInclusive_1665_ = v_startInclusive_1694_;
                v_endExclusive_1666_ = v_endExclusive_1695_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(
    mut v___x_1699_: *mut crate::leanh::LeanObject,
    mut v___x_1700_: *mut crate::leanh::LeanObject,
    mut v___x_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_b_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1704_: u8 = 0;
    let mut v_res_1705_: u8 = 0;
    let mut v_r_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1704_ = (crate::leanh::lean_unbox(v_b_1703_) as u8);
    v_res_1705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_1699_, v___x_1700_, v___x_1701_, v_a_1702_, v_b_boxed_1704_);
    crate::leanh::lean_dec_ref(v___x_1700_);
    v_r_1706_ = crate::leanh::lean_box((v_res_1705_) as usize);
    return v_r_1706_;
}
pub unsafe fn l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(
    mut v_v_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parts_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: u8 = 0;
    v___x_1710_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1711_ = lean_string_utf8_byte_size(v_v_1709_);
    crate::leanh::lean_inc_ref_n(v_v_1709_, 2);
    v___x_1712_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1712_, 0, v_v_1709_);
    crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1710_);
    crate::leanh::lean_ctor_set(v___x_1712_, 2, v___x_1711_);
    v_parts_1713_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v___x_1712_);
    v___x_1714_ = 1;
    crate::leanh::lean_inc(v_parts_1713_);
    v___x_1715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_1709_, v___x_1712_, v___x_1711_, v_parts_1713_, v___x_1714_);
    if v___x_1715_ == 0 {
        let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_parts_1713_);
        crate::leanh::lean_dec_ref_known(v___x_1712_, 3);
        crate::leanh::lean_dec_ref(v_v_1709_);
        v___x_1716_ = crate::leanh::lean_box(0);
        return v___x_1716_;
    } else {
        let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1719_: usize = 0;
        let mut v___x_1720_: usize = 0;
        let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1717_ =
            l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0;
        v___x_1718_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_1709_, v___x_1712_, v___x_1711_, v_parts_1713_, v___x_1717_);
        crate::leanh::lean_dec_ref_known(v___x_1712_, 3);
        v_sz_1719_ = lean_array_size(v___x_1718_);
        v___x_1720_ = 0usize;
        v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_1719_, v___x_1720_, v___x_1718_);
        v___x_1722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1722_, 0, v___x_1721_);
        return v___x_1722_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(
    mut v___x_1723_: *mut crate::leanh::LeanObject,
    mut v___x_1724_: *mut crate::leanh::LeanObject,
    mut v___x_1725_: *mut crate::leanh::LeanObject,
    mut v_inst_1726_: *mut crate::leanh::LeanObject,
    mut v_R_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
    mut v_b_1729_: u8,
    mut v_c_1730_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1731_: u8 = 0;
    v___x_1731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_1723_, v___x_1724_, v___x_1725_, v_a_1728_, v_b_1729_);
    return v___x_1731_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(
    mut v___x_1732_: *mut crate::leanh::LeanObject,
    mut v___x_1733_: *mut crate::leanh::LeanObject,
    mut v___x_1734_: *mut crate::leanh::LeanObject,
    mut v_inst_1735_: *mut crate::leanh::LeanObject,
    mut v_R_1736_: *mut crate::leanh::LeanObject,
    mut v_a_1737_: *mut crate::leanh::LeanObject,
    mut v_b_1738_: *mut crate::leanh::LeanObject,
    mut v_c_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1740_: u8 = 0;
    let mut v_res_1741_: u8 = 0;
    let mut v_r_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1740_ = (crate::leanh::lean_unbox(v_b_1738_) as u8);
    v_res_1741_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_1732_, v___x_1733_, v___x_1734_, v_inst_1735_, v_R_1736_, v_a_1737_, v_b_boxed_1740_, v_c_1739_);
    crate::leanh::lean_dec_ref(v___x_1733_);
    v_r_1742_ = crate::leanh::lean_box((v_res_1741_) as usize);
    return v_r_1742_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(
    mut v___x_1743_: *mut crate::leanh::LeanObject,
    mut v___x_1744_: *mut crate::leanh::LeanObject,
    mut v___x_1745_: *mut crate::leanh::LeanObject,
    mut v_inst_1746_: *mut crate::leanh::LeanObject,
    mut v_R_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_b_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_1743_, v___x_1744_, v___x_1745_, v_a_1748_, v_b_1749_);
    return v___x_1750_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(
    mut v___x_1751_: *mut crate::leanh::LeanObject,
    mut v___x_1752_: *mut crate::leanh::LeanObject,
    mut v___x_1753_: *mut crate::leanh::LeanObject,
    mut v_inst_1754_: *mut crate::leanh::LeanObject,
    mut v_R_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_b_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_1751_, v___x_1752_, v___x_1753_, v_inst_1754_, v_R_1755_, v_a_1756_, v_b_1757_);
    crate::leanh::lean_dec_ref(v___x_1752_);
    return v_res_1758_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(
    mut v___x_1759_: *mut crate::leanh::LeanObject,
    mut v___x_1760_: *mut crate::leanh::LeanObject,
    mut v___x_1761_: *mut crate::leanh::LeanObject,
    mut v_inst_1762_: *mut crate::leanh::LeanObject,
    mut v_R_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_b_1765_: u8,
    mut v_c_1766_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1767_: u8 = 0;
    v___x_1767_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_1759_, v___x_1760_, v___x_1761_, v_a_1764_, v_b_1765_);
    return v___x_1767_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(
    mut v___x_1768_: *mut crate::leanh::LeanObject,
    mut v___x_1769_: *mut crate::leanh::LeanObject,
    mut v___x_1770_: *mut crate::leanh::LeanObject,
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_R_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_b_1774_: *mut crate::leanh::LeanObject,
    mut v_c_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1776_: u8 = 0;
    let mut v_res_1777_: u8 = 0;
    let mut v_r_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1776_ = (crate::leanh::lean_unbox(v_b_1774_) as u8);
    v_res_1777_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_1768_, v___x_1769_, v___x_1770_, v_inst_1771_, v_R_1772_, v_a_1773_, v_b_boxed_1776_, v_c_1775_);
    crate::leanh::lean_dec_ref(v___x_1769_);
    v_r_1778_ = crate::leanh::lean_box((v_res_1777_) as usize);
    return v_r_1778_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(
    mut v___x_1779_: *mut crate::leanh::LeanObject,
    mut v___x_1780_: *mut crate::leanh::LeanObject,
    mut v___x_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_R_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_b_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_1779_, v___x_1780_, v___x_1781_, v_a_1784_, v_b_1785_);
    return v___x_1786_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(
    mut v___x_1787_: *mut crate::leanh::LeanObject,
    mut v___x_1788_: *mut crate::leanh::LeanObject,
    mut v___x_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_R_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_b_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_1787_, v___x_1788_, v___x_1789_, v_inst_1790_, v_R_1791_, v_a_1792_, v_b_1793_);
    crate::leanh::lean_dec_ref(v___x_1788_);
    return v_res_1794_;
}
pub unsafe fn l_Std_Http_Header_instBEqContentLength_beq(
    mut v_x_1795_: *mut crate::leanh::LeanObject,
    mut v_x_1796_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1797_: u8 = 0;
    v___x_1797_ = lean_nat_dec_eq(v_x_1795_, v_x_1796_);
    return v___x_1797_;
}
pub unsafe fn l_Std_Http_Header_instBEqContentLength_beq___boxed(
    mut v_x_1798_: *mut crate::leanh::LeanObject,
    mut v_x_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1800_: u8 = 0;
    let mut v_r_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_1798_, v_x_1799_);
    crate::leanh::lean_dec(v_x_1799_);
    crate::leanh::lean_dec(v_x_1798_);
    v_r_1801_ = crate::leanh::lean_box((v_res_1800_) as usize);
    return v_r_1801_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(
    mut v_a_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = lean_nat_to_int(v_a_1804_);
    return v___x_1805_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1820_ = lean_nat_to_int(v___x_1819_);
    return v___x_1820_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0;
    v___x_1823_ = lean_string_length(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9,
    );
    v___x_1825_ = lean_nat_to_int(v___x_1824_);
    return v___x_1825_;
}
pub unsafe fn l_Std_Http_Header_instReprContentLength_repr___redArg(
    mut v_x_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6;
    v___x_1832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7,
    );
    v___x_1833_ = l_Nat_reprFast(v_x_1830_);
    v___x_1834_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1833_);
    v___x_1835_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1835_, 0, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1835_, 1, v___x_1834_);
    v___x_1836_ = 0;
    v___x_1837_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1835_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1837_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1836_,
    );
    v___x_1838_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1838_, 0, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
    v___x_1839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10,
    );
    v___x_1840_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11;
    v___x_1841_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1841_, 0, v___x_1840_);
    crate::leanh::lean_ctor_set(v___x_1841_, 1, v___x_1838_);
    v___x_1842_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12;
    v___x_1843_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1841_);
    crate::leanh::lean_ctor_set(v___x_1843_, 1, v___x_1842_);
    v___x_1844_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1844_, 0, v___x_1839_);
    crate::leanh::lean_ctor_set(v___x_1844_, 1, v___x_1843_);
    v___x_1845_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1845_, 0, v___x_1844_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1845_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1836_,
    );
    return v___x_1845_;
}
pub unsafe fn l_Std_Http_Header_instReprContentLength_repr(
    mut v_x_1846_: *mut crate::leanh::LeanObject,
    mut v_prec_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_1846_);
    return v___x_1848_;
}
pub unsafe fn l_Std_Http_Header_instReprContentLength_repr___boxed(
    mut v_x_1849_: *mut crate::leanh::LeanObject,
    mut v_prec_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Std_Http_Header_instReprContentLength_repr(v_x_1849_, v_prec_1850_);
    crate::leanh::lean_dec(v_prec_1850_);
    return v_res_1851_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(
    mut v_s_1854_: *mut crate::leanh::LeanObject,
    mut v_pos_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: u32 = 0;
    let mut v___x_1871_: u32 = 0;
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1873_: u32 = 0;
    let mut v___x_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1856_ = crate::leanh::lean_ctor_get(v_s_1854_, 0);
                v_startInclusive_1857_ = crate::leanh::lean_ctor_get(v_s_1854_, 1);
                v_endExclusive_1858_ = crate::leanh::lean_ctor_get(v_s_1854_, 2);
                v___x_1859_ = lean_nat_add(v_startInclusive_1857_, v_pos_1855_);
                v___x_1867_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1868_ = lean_nat_sub(v_endExclusive_1858_, v___x_1859_);
                v___x_1869_ = lean_nat_dec_eq(v___x_1867_, v___x_1868_);
                crate::leanh::lean_dec(v___x_1868_);
                if v___x_1869_ == 0 {
                    v___x_1870_ = lean_string_utf8_get_fast(v_str_1856_, v___x_1859_);
                    v___x_1871_ = 48;
                    v___x_1872_ = lean_uint32_dec_le(v___x_1871_, v___x_1870_);
                    if v___x_1872_ == 0 {
                        v___y_1861_ = v___x_1872_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1873_ = 57;
                        v___x_1874_ = lean_uint32_dec_le(v___x_1870_, v___x_1873_);
                        v___y_1861_ = v___x_1874_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1859_);
                    return v_pos_1855_;
                }
            }
            1 => {
                if v___y_1861_ == 0 {
                    crate::leanh::lean_dec(v___x_1859_);
                    return v_pos_1855_;
                } else {
                    v___x_1862_ = lean_string_utf8_next_fast(v_str_1856_, v___x_1859_);
                    v___x_1863_ = lean_nat_sub(v___x_1862_, v___x_1859_);
                    crate::leanh::lean_dec(v___x_1859_);
                    v___x_1864_ = lean_nat_add(v_pos_1855_, v___x_1863_);
                    crate::leanh::lean_dec(v___x_1863_);
                    v___x_1865_ = lean_nat_dec_lt(v_pos_1855_, v___x_1864_);
                    if v___x_1865_ == 0 {
                        crate::leanh::lean_dec(v___x_1864_);
                        return v_pos_1855_;
                    } else {
                        crate::leanh::lean_dec(v_pos_1855_);
                        v_pos_1855_ = v___x_1864_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(
    mut v_s_1875_: *mut crate::leanh::LeanObject,
    mut v_pos_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(
        v_s_1875_,
        v_pos_1876_,
    );
    crate::leanh::lean_dec_ref(v_s_1875_);
    return v_res_1877_;
}
pub unsafe fn l_Std_Http_Header_ContentLength_parse(
    mut v_v_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1880_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1895_ = lean_string_utf8_byte_size(v_v_1878_);
                v___x_1896_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1897_ = lean_nat_dec_eq(v___x_1895_, v___x_1896_);
                if v___x_1897_ == 0 {
                    crate::leanh::lean_inc_ref(v_v_1878_);
                    v___x_1898_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1898_, 0, v_v_1878_);
                    crate::leanh::lean_ctor_set(v___x_1898_, 1, v___x_1896_);
                    crate::leanh::lean_ctor_set(v___x_1898_, 2, v___x_1895_);
                    v___x_1899_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_1898_, v___x_1896_);
                    crate::leanh::lean_dec_ref_known(v___x_1898_, 3);
                    v___x_1900_ = lean_nat_dec_eq(v___x_1899_, v___x_1895_);
                    crate::leanh::lean_dec(v___x_1899_);
                    if v___x_1900_ == 0 {
                        crate::leanh::lean_dec_ref(v_v_1878_);
                        v___x_1901_ = crate::leanh::lean_box(0);
                        return v___x_1901_;
                    } else {
                        v___y_1880_ = v___x_1897_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_1880_ = v___x_1897_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1880_ == 0 {
                    v___x_1881_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1882_ = lean_string_utf8_byte_size(v_v_1878_);
                    v___x_1883_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1883_, 0, v_v_1878_);
                    crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1881_);
                    crate::leanh::lean_ctor_set(v___x_1883_, 2, v___x_1882_);
                    v___x_1884_ = l_String_Slice_toNat_x3f(v___x_1883_);
                    crate::leanh::lean_dec_ref_known(v___x_1883_, 3);
                    if crate::leanh::lean_obj_tag(v___x_1884_) == 0 {
                        v___x_1885_ = crate::leanh::lean_box(0);
                        return v___x_1885_;
                    } else {
                        v_val_1886_ = crate::leanh::lean_ctor_get(v___x_1884_, 0);
                        v_isSharedCheck_1893_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1884_)) as u8;
                        if v_isSharedCheck_1893_ == 0 {
                            v___x_1888_ = v___x_1884_;
                            v_isShared_1889_ = v_isSharedCheck_1893_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1886_);
                            crate::leanh::lean_dec(v___x_1884_);
                            v___x_1888_ = crate::leanh::lean_box(0);
                            v_isShared_1889_ = v_isSharedCheck_1893_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_v_1878_);
                    v___x_1894_ = crate::leanh::lean_box(0);
                    return v___x_1894_;
                }
            }
            2 => {
                if v_isShared_1889_ == 0 {
                    v___x_1891_ = v___x_1888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_val_1886_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_ContentLength_serialize(
    mut v_h_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1903_ = l_Std_Http_Header_Name_contentLength;
    v___x_1904_ = l_Nat_reprFast(v_h_1902_);
    v___x_1905_ = l_Std_Http_Header_Value_ofString_x21(v___x_1904_);
    v___x_1906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1903_);
    crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(
    mut v_x_1913_: *mut crate::leanh::LeanObject,
    mut v_x_1914_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1913_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1914_) == 0 {
            let mut v___x_1915_: u8 = 0;
            v___x_1915_ = 1;
            return v___x_1915_;
        } else {
            let mut v___x_1916_: u8 = 0;
            v___x_1916_ = 0;
            return v___x_1916_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1914_) == 0 {
            let mut v___x_1917_: u8 = 0;
            v___x_1917_ = 0;
            return v___x_1917_;
        } else {
            let mut v_val_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1920_: u8 = 0;
            v_val_1918_ = crate::leanh::lean_ctor_get(v_x_1913_, 0);
            v_val_1919_ = crate::leanh::lean_ctor_get(v_x_1914_, 0);
            v___x_1920_ = lean_string_dec_eq(v_val_1918_, v_val_1919_);
            return v___x_1920_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1923_: u8 = 0;
    let mut v_r_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(
        v_x_1921_, v_x_1922_,
    );
    crate::leanh::lean_dec(v_x_1922_);
    crate::leanh::lean_dec(v_x_1921_);
    v_r_1924_ = crate::leanh::lean_box((v_res_1923_) as usize);
    return v_r_1924_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(
    mut v_as_1926_: *mut crate::leanh::LeanObject,
    mut v_i_1927_: usize,
    mut v_stop_1928_: usize,
    mut v_b_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: usize = 0;
    let mut v___x_1933_: usize = 0;
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1935_ = lean_usize_dec_eq(v_i_1927_, v_stop_1928_);
                if v___x_1935_ == 0 {
                    v___x_1936_ = lean_array_uget_borrowed(v_as_1926_, v_i_1927_);
                    v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0;
                    v___x_1938_ = lean_string_dec_eq(v___x_1936_, v___x_1937_);
                    if v___x_1938_ == 0 {
                        v___y_1931_ = v_b_1929_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_1936_);
                        v___x_1939_ = lean_array_push(v_b_1929_, v___x_1936_);
                        v___y_1931_ = v___x_1939_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1929_;
                }
            }
            1 => {
                v___x_1932_ = 1usize;
                v___x_1933_ = lean_usize_add(v_i_1927_, v___x_1932_);
                v_i_1927_ = v___x_1933_;
                v_b_1929_ = v___y_1931_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(
    mut v_as_1940_: *mut crate::leanh::LeanObject,
    mut v_i_1941_: *mut crate::leanh::LeanObject,
    mut v_stop_1942_: *mut crate::leanh::LeanObject,
    mut v_b_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1944_: usize = 0;
    let mut v_stop_boxed_1945_: usize = 0;
    let mut v_res_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1944_ = crate::leanh::lean_unbox_usize(v_i_1941_);
    crate::leanh::lean_dec(v_i_1941_);
    v_stop_boxed_1945_ = crate::leanh::lean_unbox_usize(v_stop_1942_);
    crate::leanh::lean_dec(v_stop_1942_);
    v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_1940_, v_i_boxed_1944_, v_stop_boxed_1945_, v_b_1943_);
    crate::leanh::lean_dec_ref(v_as_1940_);
    return v_res_1946_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(
    mut v___x_1947_: *mut crate::leanh::LeanObject,
    mut v_as_1948_: *mut crate::leanh::LeanObject,
    mut v_i_1949_: usize,
    mut v_stop_1950_: usize,
) -> u8 {
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: usize = 0;
    let mut v___x_1958_: usize = 0;
    let mut v___x_1960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1951_ = lean_usize_dec_eq(v_i_1949_, v_stop_1950_);
                if v___x_1951_ == 0 {
                    v___x_1952_ = 1;
                    v___x_1953_ = lean_array_uget_borrowed(v_as_1948_, v_i_1949_);
                    crate::leanh::lean_inc(v___x_1953_);
                    v___x_1954_ = l_Std_Http_Internal_isToken(v___x_1953_);
                    if v___x_1954_ == 0 {
                        return v___x_1952_;
                    } else {
                        v___x_1955_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1956_ = lean_nat_dec_eq(v___x_1947_, v___x_1955_);
                        if v___x_1956_ == 0 {
                            v___x_1957_ = 1usize;
                            v___x_1958_ = lean_usize_add(v_i_1949_, v___x_1957_);
                            v_i_1949_ = v___x_1958_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1952_;
                        }
                    }
                } else {
                    v___x_1960_ = 0;
                    return v___x_1960_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(
    mut v___x_1961_: *mut crate::leanh::LeanObject,
    mut v_as_1962_: *mut crate::leanh::LeanObject,
    mut v_i_1963_: *mut crate::leanh::LeanObject,
    mut v_stop_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1965_: usize = 0;
    let mut v_stop_boxed_1966_: usize = 0;
    let mut v_res_1967_: u8 = 0;
    let mut v_r_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1965_ = crate::leanh::lean_unbox_usize(v_i_1963_);
    crate::leanh::lean_dec(v_i_1963_);
    v_stop_boxed_1966_ = crate::leanh::lean_unbox_usize(v_stop_1964_);
    crate::leanh::lean_dec(v_stop_1964_);
    v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_1961_, v_as_1962_, v_i_boxed_1965_, v_stop_boxed_1966_);
    crate::leanh::lean_dec_ref(v_as_1962_);
    crate::leanh::lean_dec(v___x_1961_);
    v_r_1968_ = crate::leanh::lean_box((v_res_1967_) as usize);
    return v_r_1968_;
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_Validate(
    mut v_codings_1973_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_1975_: u8 = 0;
    let mut v___y_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: u8 = 0;
    let mut v___y_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastIsChunked_1983_: u8 = 0;
    let mut v___y_1985_: u8 = 0;
    let mut v___y_1986_: u8 = 0;
    let mut v___y_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_chunkedCount_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: u8 = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: usize = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: usize = 0;
    let mut v___x_2008_: usize = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: usize = 0;
    let mut v___x_2016_: usize = 0;
    let mut v___x_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = lean_array_get_size(v_codings_1973_);
                v___x_2012_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2013_ = lean_nat_dec_eq(v___x_2011_, v___x_2012_);
                if v___x_2013_ == 0 {
                    v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_2011_);
                    if v___x_2014_ == 0 {
                        v___y_1997_ = v___x_2013_;
                        state = 3;
                        continue;
                    } else {
                        if v___x_2014_ == 0 {
                            v___y_1997_ = v___x_2013_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2015_ = 0usize;
                            v___x_2016_ = lean_usize_of_nat(v___x_2011_);
                            v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_2011_, v_codings_1973_, v___x_2015_, v___x_2016_);
                            v___y_1997_ = v___x_2017_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___y_1997_ = v___x_2013_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1979_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1980_ = lean_nat_dec_lt(v___x_1979_, v___y_1976_);
                if v___x_1980_ == 0 {
                    v___x_1981_ = lean_nat_dec_eq(v___y_1976_, v___x_1979_);
                    crate::leanh::lean_dec(v___y_1976_);
                    if v___x_1981_ == 0 {
                        crate::leanh::lean_dec(v___y_1978_);
                        if v___x_1981_ == 0 {
                            return v___y_1977_;
                        } else {
                            return v___y_1975_;
                        }
                    } else {
                        v___x_1982_ = l_Std_Http_Header_TransferEncoding_Validate___closed__0;
                        v_lastIsChunked_1983_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_1978_, v___x_1982_);
                        crate::leanh::lean_dec(v___y_1978_);
                        if v_lastIsChunked_1983_ == 0 {
                            if v___x_1981_ == 0 {
                                return v___y_1977_;
                            } else {
                                return v___y_1975_;
                            }
                        } else {
                            return v___y_1977_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1978_);
                    crate::leanh::lean_dec(v___y_1976_);
                    return v___y_1975_;
                }
            }
            2 => {
                v_chunkedCount_1988_ = lean_array_get_size(v___y_1987_);
                crate::leanh::lean_dec_ref(v___y_1987_);
                v___x_1989_ = lean_array_get_size(v_codings_1973_);
                v___x_1990_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1991_ = lean_nat_sub(v___x_1989_, v___x_1990_);
                v___x_1992_ = lean_nat_dec_lt(v___x_1991_, v___x_1989_);
                if v___x_1992_ == 0 {
                    crate::leanh::lean_dec(v___x_1991_);
                    v___x_1993_ = crate::leanh::lean_box(0);
                    v___y_1975_ = v___y_1985_;
                    v___y_1976_ = v_chunkedCount_1988_;
                    v___y_1977_ = v___y_1986_;
                    v___y_1978_ = v___x_1993_;
                    state = 1;
                    continue;
                } else {
                    v___x_1994_ = lean_array_fget_borrowed(v_codings_1973_, v___x_1991_);
                    crate::leanh::lean_dec(v___x_1991_);
                    crate::leanh::lean_inc(v___x_1994_);
                    v___x_1995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_1994_);
                    v___y_1975_ = v___y_1985_;
                    v___y_1976_ = v_chunkedCount_1988_;
                    v___y_1977_ = v___y_1986_;
                    v___y_1978_ = v___x_1995_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1997_ == 0 {
                    v___x_1998_ = 1;
                    v___x_1999_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2000_ = lean_array_get_size(v_codings_1973_);
                    v___x_2001_ = l_Std_Http_Header_TransferEncoding_Validate___closed__1;
                    v___x_2002_ = lean_nat_dec_lt(v___x_1999_, v___x_2000_);
                    if v___x_2002_ == 0 {
                        v___y_1985_ = v___y_1997_;
                        v___y_1986_ = v___x_1998_;
                        v___y_1987_ = v___x_2001_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2003_ = lean_nat_dec_le(v___x_2000_, v___x_2000_);
                        if v___x_2003_ == 0 {
                            if v___x_2002_ == 0 {
                                v___y_1985_ = v___y_1997_;
                                v___y_1986_ = v___x_1998_;
                                v___y_1987_ = v___x_2001_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2004_ = 0usize;
                                v___x_2005_ = lean_usize_of_nat(v___x_2000_);
                                v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_1973_, v___x_2004_, v___x_2005_, v___x_2001_);
                                v___y_1985_ = v___y_1997_;
                                v___y_1986_ = v___x_1998_;
                                v___y_1987_ = v___x_2006_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_2007_ = 0usize;
                            v___x_2008_ = lean_usize_of_nat(v___x_2000_);
                            v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_1973_, v___x_2007_, v___x_2008_, v___x_2001_);
                            v___y_1985_ = v___y_1997_;
                            v___y_1986_ = v___x_1998_;
                            v___y_1987_ = v___x_2009_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2010_ = 0;
                    return v___x_2010_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_Validate___boxed(
    mut v_codings_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2019_: u8 = 0;
    let mut v_r_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_2018_);
    crate::leanh::lean_dec_ref(v_codings_2018_);
    v_r_2020_ = crate::leanh::lean_box((v_res_2019_) as usize);
    return v_r_2020_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(
    mut v___y_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = l_String_quote(v___y_2021_);
    v___x_2023_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_2024_: *mut crate::leanh::LeanObject,
    mut v_x_2025_: *mut crate::leanh::LeanObject,
    mut v_x_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2026_) == 0 {
                    crate::leanh::lean_dec(v_x_2024_);
                    return v_x_2025_;
                } else {
                    v_head_2027_ = crate::leanh::lean_ctor_get(v_x_2026_, 0);
                    v_tail_2028_ = crate::leanh::lean_ctor_get(v_x_2026_, 1);
                    v_isSharedCheck_2039_ = (!crate::leanh::lean_is_exclusive(v_x_2026_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_2030_ = v_x_2026_;
                        v_isShared_2031_ = v_isSharedCheck_2039_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2028_);
                        crate::leanh::lean_inc(v_head_2027_);
                        crate::leanh::lean_dec(v_x_2026_);
                        v___x_2030_ = crate::leanh::lean_box(0);
                        v_isShared_2031_ = v_isSharedCheck_2039_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2024_);
                if v_isShared_2031_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2030_, 5);
                    crate::leanh::lean_ctor_set(v___x_2030_, 1, v_x_2024_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 0, v_x_2025_);
                    v___x_2033_ = v___x_2030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_x_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_x_2024_);
                    v___x_2033_ = v_reuseFailAlloc_2038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2034_ = l_String_quote(v_head_2027_);
                v___x_2035_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2034_);
                v___x_2036_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2036_, 0, v___x_2033_);
                crate::leanh::lean_ctor_set(v___x_2036_, 1, v___x_2035_);
                v_x_2025_ = v___x_2036_;
                v_x_2026_ = v_tail_2028_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(
    mut v_x_2040_: *mut crate::leanh::LeanObject,
    mut v_x_2041_: *mut crate::leanh::LeanObject,
    mut v_x_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2042_) == 0 {
                    crate::leanh::lean_dec(v_x_2040_);
                    return v_x_2041_;
                } else {
                    v_head_2043_ = crate::leanh::lean_ctor_get(v_x_2042_, 0);
                    v_tail_2044_ = crate::leanh::lean_ctor_get(v_x_2042_, 1);
                    v_isSharedCheck_2055_ = (!crate::leanh::lean_is_exclusive(v_x_2042_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2046_ = v_x_2042_;
                        v_isShared_2047_ = v_isSharedCheck_2055_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2044_);
                        crate::leanh::lean_inc(v_head_2043_);
                        crate::leanh::lean_dec(v_x_2042_);
                        v___x_2046_ = crate::leanh::lean_box(0);
                        v_isShared_2047_ = v_isSharedCheck_2055_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2040_);
                if v_isShared_2047_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2046_, 5);
                    crate::leanh::lean_ctor_set(v___x_2046_, 1, v_x_2040_);
                    crate::leanh::lean_ctor_set(v___x_2046_, 0, v_x_2041_);
                    v___x_2049_ = v___x_2046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_x_2041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_x_2040_);
                    v___x_2049_ = v_reuseFailAlloc_2054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2050_ = l_String_quote(v_head_2043_);
                v___x_2051_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2051_, 0, v___x_2050_);
                v___x_2052_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2049_);
                crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2051_);
                v___x_2053_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_2040_, v___x_2052_, v_tail_2044_);
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(
    mut v_x_2056_: *mut crate::leanh::LeanObject,
    mut v_x_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2056_) == 0 {
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2057_);
        v___x_2058_ = crate::leanh::lean_box(0);
        return v___x_2058_;
    } else {
        let mut v_tail_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2059_ = crate::leanh::lean_ctor_get(v_x_2056_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2059_) == 0 {
            let mut v_head_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2057_);
            v_head_2060_ = crate::leanh::lean_ctor_get(v_x_2056_, 0);
            crate::leanh::lean_inc(v_head_2060_);
            crate::leanh::lean_dec_ref_known(v_x_2056_, 2);
            v___x_2061_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_2060_);
            return v___x_2061_;
        } else {
            let mut v_head_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2059_);
            v_head_2062_ = crate::leanh::lean_ctor_get(v_x_2056_, 0);
            crate::leanh::lean_inc(v_head_2062_);
            crate::leanh::lean_dec_ref_known(v_x_2056_, 2);
            v___x_2063_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_2062_);
            v___x_2064_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_2057_, v___x_2063_, v_tail_2059_);
            return v___x_2064_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2073_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0;
    v___x_2074_ = lean_string_length(v___x_2073_);
    return v___x_2074_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once), _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
    v___x_2076_ = lean_nat_to_int(v___x_2075_);
    return v___x_2076_;
}
pub unsafe fn l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(
    mut v_xs_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    v___x_2085_ = lean_array_get_size(v_xs_2084_);
    v___x_2086_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2087_ = lean_nat_dec_eq(v___x_2085_, v___x_2086_);
    if v___x_2087_ == 0 {
        let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2088_ = lean_array_to_list(v_xs_2084_);
        v___x_2089_ =
            l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3;
        v___x_2090_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_2088_, v___x_2089_);
        v___x_2091_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
        v___x_2092_ =
            l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7;
        v___x_2093_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2093_, 0, v___x_2092_);
        crate::leanh::lean_ctor_set(v___x_2093_, 1, v___x_2090_);
        v___x_2094_ =
            l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8;
        v___x_2095_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2093_);
        crate::leanh::lean_ctor_set(v___x_2095_, 1, v___x_2094_);
        v___x_2096_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2096_, 0, v___x_2091_);
        crate::leanh::lean_ctor_set(v___x_2096_, 1, v___x_2095_);
        v___x_2097_ = l_Std_Format_fill(v___x_2096_);
        return v___x_2097_;
    } else {
        let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2084_);
        v___x_2098_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10;
        return v___x_2098_;
    }
}
pub unsafe fn _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2109_ = lean_nat_to_int(v___x_2108_);
    return v___x_2109_;
}
pub unsafe fn l_Std_Http_Header_instReprTransferEncoding_repr___redArg(
    mut v_x_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5;
    v___x_2118_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3;
    v___x_2119_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once
        ),
        _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4,
    );
    v___x_2120_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_2116_);
    v___x_2121_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2119_);
    crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2120_);
    v___x_2122_ = 0;
    v___x_2123_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2121_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2123_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2122_,
    );
    v___x_2124_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2124_, 0, v___x_2118_);
    crate::leanh::lean_ctor_set(v___x_2124_, 1, v___x_2123_);
    v___x_2125_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2;
    v___x_2126_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2126_, 0, v___x_2124_);
    crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2125_);
    v___x_2127_ = crate::leanh::lean_box(1);
    v___x_2128_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
    v___x_2129_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6;
    v___x_2130_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2128_);
    crate::leanh::lean_ctor_set(v___x_2130_, 1, v___x_2129_);
    v___x_2131_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2131_, 0, v___x_2130_);
    crate::leanh::lean_ctor_set(v___x_2131_, 1, v___x_2117_);
    v___x_2132_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8;
    v___x_2133_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2131_);
    crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
    v___x_2134_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10,
    );
    v___x_2135_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11;
    v___x_2136_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
    crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2133_);
    v___x_2137_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12;
    v___x_2138_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
    crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
    v___x_2139_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2139_, 0, v___x_2134_);
    crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2138_);
    v___x_2140_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2140_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2122_,
    );
    return v___x_2140_;
}
pub unsafe fn l_Std_Http_Header_instReprTransferEncoding_repr(
    mut v_x_2141_: *mut crate::leanh::LeanObject,
    mut v_prec_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_2141_);
    return v___x_2143_;
}
pub unsafe fn l_Std_Http_Header_instReprTransferEncoding_repr___boxed(
    mut v_x_2144_: *mut crate::leanh::LeanObject,
    mut v_prec_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2146_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_2144_, v_prec_2145_);
    crate::leanh::lean_dec(v_prec_2145_);
    return v_res_2146_;
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_isChunked(
    mut v_te_2149_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2154_ = lean_array_get_size(v_te_2149_);
                v___x_2155_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2156_ = lean_nat_sub(v___x_2154_, v___x_2155_);
                v___x_2157_ = lean_nat_dec_lt(v___x_2156_, v___x_2154_);
                if v___x_2157_ == 0 {
                    crate::leanh::lean_dec(v___x_2156_);
                    v___x_2158_ = crate::leanh::lean_box(0);
                    v___y_2151_ = v___x_2158_;
                    state = 1;
                    continue;
                } else {
                    v___x_2159_ = lean_array_fget_borrowed(v_te_2149_, v___x_2156_);
                    crate::leanh::lean_dec(v___x_2156_);
                    crate::leanh::lean_inc(v___x_2159_);
                    v___x_2160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2160_, 0, v___x_2159_);
                    v___y_2151_ = v___x_2160_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2152_ = l_Std_Http_Header_TransferEncoding_Validate___closed__0;
                v___x_2153_ =
                    l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(
                        v___y_2151_,
                        v___x_2152_,
                    );
                crate::leanh::lean_dec(v___y_2151_);
                return v___x_2153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_isChunked___boxed(
    mut v_te_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2162_: u8 = 0;
    let mut v_r_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2162_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_2161_);
    crate::leanh::lean_dec_ref(v_te_2161_);
    v_r_2163_ = crate::leanh::lean_box((v_res_2162_) as usize);
    return v_r_2163_;
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_parse(
    mut v_v_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2165_ =
                    l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(
                        v_v_2164_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2165_) == 0 {
                    v___x_2166_ = crate::leanh::lean_box(0);
                    return v___x_2166_;
                } else {
                    v_val_2167_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
                    v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v___x_2165_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2169_ = v___x_2165_;
                        v_isShared_2170_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2167_);
                        crate::leanh::lean_dec(v___x_2165_);
                        v___x_2169_ = crate::leanh::lean_box(0);
                        v_isShared_2170_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2171_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_2167_);
                if v___x_2171_ == 0 {
                    crate::leanh::lean_del_object(v___x_2169_);
                    crate::leanh::lean_dec(v_val_2167_);
                    v___x_2172_ = crate::leanh::lean_box(0);
                    return v___x_2172_;
                } else {
                    if v_isShared_2170_ == 0 {
                        v___x_2174_ = v___x_2169_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_val_2167_);
                        v___x_2174_ = v_reuseFailAlloc_2175_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_TransferEncoding_serialize(
    mut v_te_2177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1;
    v___x_2179_ = lean_array_to_list(v_te_2177_);
    v_value_2180_ = l_String_intercalate(v___x_2178_, v___x_2179_);
    v___x_2181_ = l_Std_Http_Header_Name_transferEncoding;
    v___x_2182_ = l_Std_Http_Header_Value_ofString_x21(v_value_2180_);
    v___x_2183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2181_);
    crate::leanh::lean_ctor_set(v___x_2183_, 1, v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Std_Http_Header_instReprConnection_repr___redArg(
    mut v_x_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5;
    v___x_2204_ = l_Std_Http_Header_instReprConnection_repr___redArg___closed__3;
    v___x_2205_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7,
    );
    v___x_2206_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_2202_);
    v___x_2207_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2205_);
    crate::leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
    v___x_2208_ = 0;
    v___x_2209_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2209_, 0, v___x_2207_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2209_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2208_,
    );
    v___x_2210_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2210_, 0, v___x_2204_);
    crate::leanh::lean_ctor_set(v___x_2210_, 1, v___x_2209_);
    v___x_2211_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2;
    v___x_2212_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2212_, 0, v___x_2210_);
    crate::leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
    v___x_2213_ = crate::leanh::lean_box(1);
    v___x_2214_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2214_, 0, v___x_2212_);
    crate::leanh::lean_ctor_set(v___x_2214_, 1, v___x_2213_);
    v___x_2215_ = l_Std_Http_Header_instReprConnection_repr___redArg___closed__5;
    v___x_2216_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2214_);
    crate::leanh::lean_ctor_set(v___x_2216_, 1, v___x_2215_);
    v___x_2217_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    crate::leanh::lean_ctor_set(v___x_2217_, 1, v___x_2203_);
    v___x_2218_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8;
    v___x_2219_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2219_, 0, v___x_2217_);
    crate::leanh::lean_ctor_set(v___x_2219_, 1, v___x_2218_);
    v___x_2220_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10,
    );
    v___x_2221_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11;
    v___x_2222_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2221_);
    crate::leanh::lean_ctor_set(v___x_2222_, 1, v___x_2219_);
    v___x_2223_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12;
    v___x_2224_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2222_);
    crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
    v___x_2225_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2225_, 0, v___x_2220_);
    crate::leanh::lean_ctor_set(v___x_2225_, 1, v___x_2224_);
    v___x_2226_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2226_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2208_,
    );
    return v___x_2226_;
}
pub unsafe fn l_Std_Http_Header_instReprConnection_repr(
    mut v_x_2227_: *mut crate::leanh::LeanObject,
    mut v_prec_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2229_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_2227_);
    return v___x_2229_;
}
pub unsafe fn l_Std_Http_Header_instReprConnection_repr___boxed(
    mut v_x_2230_: *mut crate::leanh::LeanObject,
    mut v_prec_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ = l_Std_Http_Header_instReprConnection_repr(v_x_2230_, v_prec_2231_);
    crate::leanh::lean_dec(v_prec_2231_);
    return v_res_2232_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(
    mut v_token_2235_: *mut crate::leanh::LeanObject,
    mut v_as_2236_: *mut crate::leanh::LeanObject,
    mut v_i_2237_: usize,
    mut v_stop_2238_: usize,
) -> u8 {
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2239_ = lean_usize_dec_eq(v_i_2237_, v_stop_2238_);
                if v___x_2239_ == 0 {
                    v___x_2240_ = lean_array_uget_borrowed(v_as_2236_, v_i_2237_);
                    v___x_2241_ = lean_string_dec_eq(v___x_2240_, v_token_2235_);
                    if v___x_2241_ == 0 {
                        v___x_2242_ = 1usize;
                        v___x_2243_ = lean_usize_add(v_i_2237_, v___x_2242_);
                        v_i_2237_ = v___x_2243_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2241_;
                    }
                } else {
                    v___x_2245_ = 0;
                    return v___x_2245_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(
    mut v_token_2246_: *mut crate::leanh::LeanObject,
    mut v_as_2247_: *mut crate::leanh::LeanObject,
    mut v_i_2248_: *mut crate::leanh::LeanObject,
    mut v_stop_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2250_: usize = 0;
    let mut v_stop_boxed_2251_: usize = 0;
    let mut v_res_2252_: u8 = 0;
    let mut v_r_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2250_ = crate::leanh::lean_unbox_usize(v_i_2248_);
    crate::leanh::lean_dec(v_i_2248_);
    v_stop_boxed_2251_ = crate::leanh::lean_unbox_usize(v_stop_2249_);
    crate::leanh::lean_dec(v_stop_2249_);
    v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_2246_, v_as_2247_, v_i_boxed_2250_, v_stop_boxed_2251_);
    crate::leanh::lean_dec_ref(v_as_2247_);
    crate::leanh::lean_dec_ref(v_token_2246_);
    v_r_2253_ = crate::leanh::lean_box((v_res_2252_) as usize);
    return v_r_2253_;
}
pub unsafe fn l_Std_Http_Header_Connection_containsToken(
    mut v_connection_2254_: *mut crate::leanh::LeanObject,
    mut v_token_2255_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: u8 = 0;
    v___x_2256_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2257_ = lean_array_get_size(v_connection_2254_);
    v___x_2258_ = lean_nat_dec_lt(v___x_2256_, v___x_2257_);
    if v___x_2258_ == 0 {
        crate::leanh::lean_dec_ref(v_token_2255_);
        return v___x_2258_;
    } else {
        let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2259_ = lean_string_utf8_byte_size(v_token_2255_);
        if v___x_2258_ == 0 {
            crate::leanh::lean_dec_ref(v_token_2255_);
            return v___x_2258_;
        } else {
            let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_token_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2264_: usize = 0;
            let mut v___x_2265_: usize = 0;
            let mut v___x_2266_: u8 = 0;
            v___x_2260_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2260_, 0, v_token_2255_);
            crate::leanh::lean_ctor_set(v___x_2260_, 1, v___x_2256_);
            crate::leanh::lean_ctor_set(v___x_2260_, 2, v___x_2259_);
            v___x_2261_ = l_String_Slice_trimAscii(v___x_2260_);
            v___x_2262_ = l_String_Slice_toString(v___x_2261_);
            crate::leanh::lean_dec_ref(v___x_2261_);
            v_token_2263_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_2262_, v___x_2256_);
            v___x_2264_ = 0usize;
            v___x_2265_ = lean_usize_of_nat(v___x_2257_);
            v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_2263_, v_connection_2254_, v___x_2264_, v___x_2265_);
            crate::leanh::lean_dec_ref(v_token_2263_);
            return v___x_2266_;
        }
    }
}
pub unsafe fn l_Std_Http_Header_Connection_containsToken___boxed(
    mut v_connection_2267_: *mut crate::leanh::LeanObject,
    mut v_token_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2269_: u8 = 0;
    let mut v_r_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Std_Http_Header_Connection_containsToken(v_connection_2267_, v_token_2268_);
    crate::leanh::lean_dec_ref(v_connection_2267_);
    v_r_2270_ = crate::leanh::lean_box((v_res_2269_) as usize);
    return v_r_2270_;
}
pub unsafe fn l_Std_Http_Header_Connection_shouldClose(
    mut v_connection_2272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    v___x_2273_ = l_Std_Http_Header_Connection_shouldClose___closed__0;
    v___x_2274_ = l_Std_Http_Header_Connection_containsToken(v_connection_2272_, v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Std_Http_Header_Connection_shouldClose___boxed(
    mut v_connection_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: u8 = 0;
    let mut v_r_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Http_Header_Connection_shouldClose(v_connection_2275_);
    crate::leanh::lean_dec_ref(v_connection_2275_);
    v_r_2277_ = crate::leanh::lean_box((v_res_2276_) as usize);
    return v_r_2277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(
    mut v_as_2278_: *mut crate::leanh::LeanObject,
    mut v_i_2279_: usize,
    mut v_stop_2280_: usize,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: usize = 0;
    let mut v___x_2286_: usize = 0;
    let mut v___x_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2281_ = lean_usize_dec_eq(v_i_2279_, v_stop_2280_);
                if v___x_2281_ == 0 {
                    v___x_2282_ = 1;
                    v___x_2283_ = lean_array_uget_borrowed(v_as_2278_, v_i_2279_);
                    crate::leanh::lean_inc(v___x_2283_);
                    v___x_2284_ = l_Std_Http_Internal_isToken(v___x_2283_);
                    if v___x_2284_ == 0 {
                        return v___x_2282_;
                    } else {
                        if v___x_2281_ == 0 {
                            v___x_2285_ = 1usize;
                            v___x_2286_ = lean_usize_add(v_i_2279_, v___x_2285_);
                            v_i_2279_ = v___x_2286_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2282_;
                        }
                    }
                } else {
                    v___x_2288_ = 0;
                    return v___x_2288_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(
    mut v_as_2289_: *mut crate::leanh::LeanObject,
    mut v_i_2290_: *mut crate::leanh::LeanObject,
    mut v_stop_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_stop_boxed_2293_: usize = 0;
    let mut v_res_2294_: u8 = 0;
    let mut v_r_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2292_ = crate::leanh::lean_unbox_usize(v_i_2290_);
    crate::leanh::lean_dec(v_i_2290_);
    v_stop_boxed_2293_ = crate::leanh::lean_unbox_usize(v_stop_2291_);
    crate::leanh::lean_dec(v_stop_2291_);
    v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_2289_, v_i_boxed_2292_, v_stop_boxed_2293_);
    crate::leanh::lean_dec_ref(v_as_2289_);
    v_r_2295_ = crate::leanh::lean_box((v_res_2294_) as usize);
    return v_r_2295_;
}
pub unsafe fn l_Std_Http_Header_Connection_parse(
    mut v_v_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2302_: u8 = 0;
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: usize = 0;
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2297_ =
                    l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(
                        v_v_2296_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2297_) == 0 {
                    v___x_2298_ = crate::leanh::lean_box(0);
                    return v___x_2298_;
                } else {
                    v_val_2299_ = crate::leanh::lean_ctor_get(v___x_2297_, 0);
                    v_isSharedCheck_2319_ = (!crate::leanh::lean_is_exclusive(v___x_2297_)) as u8;
                    if v_isSharedCheck_2319_ == 0 {
                        v___x_2301_ = v___x_2297_;
                        v_isShared_2302_ = v_isSharedCheck_2319_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2299_);
                        crate::leanh::lean_dec(v___x_2297_);
                        v___x_2301_ = crate::leanh::lean_box(0);
                        v_isShared_2302_ = v_isSharedCheck_2319_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2303_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2304_ = lean_array_get_size(v_val_2299_);
                v___x_2305_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
                if v___x_2305_ == 0 {
                    if v_isShared_2302_ == 0 {
                        v___x_2307_ = v___x_2301_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_val_2299_);
                        v___x_2307_ = v_reuseFailAlloc_2308_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_2305_ == 0 {
                        if v_isShared_2302_ == 0 {
                            v___x_2310_ = v___x_2301_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2311_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_val_2299_);
                            v___x_2310_ = v_reuseFailAlloc_2311_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2312_ = 0usize;
                        v___x_2313_ = lean_usize_of_nat(v___x_2304_);
                        v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_2299_, v___x_2312_, v___x_2313_);
                        if v___x_2314_ == 0 {
                            if v_isShared_2302_ == 0 {
                                v___x_2316_ = v___x_2301_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2317_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_val_2299_);
                                v___x_2316_ = v_reuseFailAlloc_2317_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2301_);
                            crate::leanh::lean_dec(v_val_2299_);
                            v___x_2318_ = crate::leanh::lean_box(0);
                            return v___x_2318_;
                        }
                    }
                }
            }
            2 => {
                return v___x_2307_;
            }
            3 => {
                return v___x_2310_;
            }
            4 => {
                return v___x_2316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Connection_serialize(
    mut v_connection_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ =
        l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1;
    v___x_2322_ = lean_array_to_list(v_connection_2320_);
    v_value_2323_ = l_String_intercalate(v___x_2321_, v___x_2322_);
    v___x_2324_ = l_Std_Http_Header_Name_connection;
    v___x_2325_ = l_Std_Http_Header_Value_ofString_x21(v_value_2323_);
    v___x_2326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2324_);
    crate::leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
    return v___x_2326_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2343_ = lean_nat_to_int(v___x_2342_);
    return v___x_2343_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2345_ = lean_nat_to_int(v___x_2344_);
    return v___x_2345_;
}
pub unsafe fn l_Std_Http_Header_instReprHost_repr___redArg(
    mut v_x_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_host_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctr_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_ipv4_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v_ipv6_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_host_2354_ = crate::leanh::lean_ctor_get(v_x_2353_, 0);
                v_port_2355_ = crate::leanh::lean_ctor_get(v_x_2353_, 1);
                v_isSharedCheck_2429_ = (!crate::leanh::lean_is_exclusive(v_x_2353_)) as u8;
                if v_isSharedCheck_2429_ == 0 {
                    v___x_2357_ = v_x_2353_;
                    v_isShared_2358_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_port_2355_);
                    crate::leanh::lean_inc(v_host_2354_);
                    crate::leanh::lean_dec(v_x_2353_);
                    v___x_2357_ = crate::leanh::lean_box(0);
                    v_isShared_2358_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2359_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5;
                v___x_2360_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__3;
                v___x_2361_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprHost_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4,
                );
                v___x_2362_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2363_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprHost_repr___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once
                    ),
                    _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5,
                );
                match crate::leanh::lean_obj_tag(v_host_2354_) {
                    0 => {
                        v_name_2399_ = crate::leanh::lean_ctor_get(v_host_2354_, 0);
                        v_isSharedCheck_2408_ =
                            (!crate::leanh::lean_is_exclusive(v_host_2354_)) as u8;
                        if v_isSharedCheck_2408_ == 0 {
                            v___x_2401_ = v_host_2354_;
                            v_isShared_2402_ = v_isSharedCheck_2408_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_name_2399_);
                            crate::leanh::lean_dec(v_host_2354_);
                            v___x_2401_ = crate::leanh::lean_box(0);
                            v_isShared_2402_ = v_isSharedCheck_2408_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_ipv4_2409_ = crate::leanh::lean_ctor_get(v_host_2354_, 0);
                        v_isSharedCheck_2418_ =
                            (!crate::leanh::lean_is_exclusive(v_host_2354_)) as u8;
                        if v_isSharedCheck_2418_ == 0 {
                            v___x_2411_ = v_host_2354_;
                            v_isShared_2412_ = v_isSharedCheck_2418_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ipv4_2409_);
                            crate::leanh::lean_dec(v_host_2354_);
                            v___x_2411_ = crate::leanh::lean_box(0);
                            v_isShared_2412_ = v_isSharedCheck_2418_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v_ipv6_2419_ = crate::leanh::lean_ctor_get(v_host_2354_, 0);
                        v_isSharedCheck_2428_ =
                            (!crate::leanh::lean_is_exclusive(v_host_2354_)) as u8;
                        if v_isSharedCheck_2428_ == 0 {
                            v___x_2421_ = v_host_2354_;
                            v_isShared_2422_ = v_isSharedCheck_2428_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ipv6_2419_);
                            crate::leanh::lean_dec(v_host_2354_);
                            v___x_2421_ = crate::leanh::lean_box(0);
                            v_isShared_2422_ = v_isSharedCheck_2428_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2367_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__6;
                v___x_2368_ = lean_string_append(v___x_2367_, v_ctr_2365_);
                v___x_2369_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                v___x_2370_ = crate::leanh::lean_box(1);
                if v_isShared_2358_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2357_, 5);
                    crate::leanh::lean_ctor_set(v___x_2357_, 1, v___x_2370_);
                    crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2369_);
                    v___x_2372_ = v___x_2357_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2370_);
                    v___x_2372_ = v_reuseFailAlloc_2398_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2373_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2373_, 0, v___x_2372_);
                crate::leanh::lean_ctor_set(v___x_2373_, 1, v_a_2366_);
                v___x_2374_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2363_);
                crate::leanh::lean_ctor_set(v___x_2374_, 1, v___x_2373_);
                v___x_2375_ = 0;
                v___x_2376_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2376_, 0, v___x_2374_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2376_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2375_,
                );
                v___x_2377_ = l_Repr_addAppParen(v___x_2376_, v___x_2362_);
                v___x_2378_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2378_, 0, v___x_2361_);
                crate::leanh::lean_ctor_set(v___x_2378_, 1, v___x_2377_);
                v___x_2379_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2379_, 0, v___x_2378_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2379_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2375_,
                );
                v___x_2380_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2380_, 0, v___x_2360_);
                crate::leanh::lean_ctor_set(v___x_2380_, 1, v___x_2379_);
                v___x_2381_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2;
                v___x_2382_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2382_, 0, v___x_2380_);
                crate::leanh::lean_ctor_set(v___x_2382_, 1, v___x_2381_);
                v___x_2383_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
                crate::leanh::lean_ctor_set(v___x_2383_, 1, v___x_2370_);
                v___x_2384_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__8;
                v___x_2385_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2385_, 0, v___x_2383_);
                crate::leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                v___x_2386_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2386_, 0, v___x_2385_);
                crate::leanh::lean_ctor_set(v___x_2386_, 1, v___x_2359_);
                v___x_2387_ = l_Std_Http_URI_instReprPort_repr(v_port_2355_, v___x_2362_);
                crate::leanh::lean_dec(v_port_2355_);
                v___x_2388_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2388_, 0, v___x_2361_);
                crate::leanh::lean_ctor_set(v___x_2388_, 1, v___x_2387_);
                v___x_2389_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2389_, 0, v___x_2388_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2389_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2375_,
                );
                v___x_2390_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2390_, 0, v___x_2386_);
                crate::leanh::lean_ctor_set(v___x_2390_, 1, v___x_2389_);
                v___x_2391_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once
                    ),
                    _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10,
                );
                v___x_2392_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11;
                v___x_2393_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                crate::leanh::lean_ctor_set(v___x_2393_, 1, v___x_2390_);
                v___x_2394_ = l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12;
                v___x_2395_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2395_, 0, v___x_2393_);
                crate::leanh::lean_ctor_set(v___x_2395_, 1, v___x_2394_);
                v___x_2396_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2391_);
                crate::leanh::lean_ctor_set(v___x_2396_, 1, v___x_2395_);
                v___x_2397_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2397_, 0, v___x_2396_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2397_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2375_,
                );
                return v___x_2397_;
            }
            4 => {
                v___x_2403_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__9;
                v___x_2404_ = l_String_quote(v_name_2399_);
                if v_isShared_2402_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2401_, 3);
                    crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2404_);
                    v___x_2406_ = v___x_2401_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2407_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
                    v___x_2406_ = v_reuseFailAlloc_2407_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_ctr_2365_ = v___x_2403_;
                v_a_2366_ = v___x_2406_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2413_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__10;
                v___x_2414_ = lean_uv_ntop_v4(v_ipv4_2409_);
                crate::leanh::lean_dec_ref(v_ipv4_2409_);
                if v_isShared_2412_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2411_, 3);
                    crate::leanh::lean_ctor_set(v___x_2411_, 0, v___x_2414_);
                    v___x_2416_ = v___x_2411_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
                    v___x_2416_ = v_reuseFailAlloc_2417_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_ctr_2365_ = v___x_2413_;
                v_a_2366_ = v___x_2416_;
                state = 2;
                continue;
            }
            8 => {
                v___x_2423_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__11;
                v___x_2424_ = lean_uv_ntop_v6(v_ipv6_2419_);
                crate::leanh::lean_dec_ref(v_ipv6_2419_);
                if v_isShared_2422_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2421_, 3);
                    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2421_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_ctr_2365_ = v___x_2423_;
                v_a_2366_ = v___x_2426_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_instReprHost_repr(
    mut v_x_2430_: *mut crate::leanh::LeanObject,
    mut v_prec_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_2430_);
    return v___x_2432_;
}
pub unsafe fn l_Std_Http_Header_instReprHost_repr___boxed(
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v_prec_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2435_ = l_Std_Http_Header_instReprHost_repr(v_x_2433_, v_prec_2434_);
    crate::leanh::lean_dec(v_prec_2434_);
    return v_res_2435_;
}
pub unsafe fn l_Std_Http_Header_instBEqHost_beq(
    mut v_x_2438_: *mut crate::leanh::LeanObject,
    mut v_x_2439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_host_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    v_host_2440_ = crate::leanh::lean_ctor_get(v_x_2438_, 0);
    v_port_2441_ = crate::leanh::lean_ctor_get(v_x_2438_, 1);
    v_host_2442_ = crate::leanh::lean_ctor_get(v_x_2439_, 0);
    v_port_2443_ = crate::leanh::lean_ctor_get(v_x_2439_, 1);
    v___x_2444_ = l_Std_Http_URI_instBEqHost_beq(v_host_2440_, v_host_2442_);
    if v___x_2444_ == 0 {
        return v___x_2444_;
    } else {
        let mut v___x_2445_: u8 = 0;
        v___x_2445_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_2441_, v_port_2443_);
        return v___x_2445_;
    }
}
pub unsafe fn l_Std_Http_Header_instBEqHost_beq___boxed(
    mut v_x_2446_: *mut crate::leanh::LeanObject,
    mut v_x_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2448_: u8 = 0;
    let mut v_r_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2448_ = l_Std_Http_Header_instBEqHost_beq(v_x_2446_, v_x_2447_);
    crate::leanh::lean_dec_ref(v_x_2447_);
    crate::leanh::lean_dec_ref(v_x_2446_);
    v_r_2449_ = crate::leanh::lean_box((v_res_2448_) as usize);
    return v_r_2449_;
}
pub unsafe fn l_Std_Http_Header_Host_parse___lam__0(
    mut v___x_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2465_: u8 = 0;
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_unused_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2457_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_2455_, v___y_2456_);
                if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                    v_pos_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                    crate::leanh::lean_inc(v_pos_2458_);
                    v_array_2459_ = crate::leanh::lean_ctor_get(v_pos_2458_, 0);
                    v_idx_2460_ = crate::leanh::lean_ctor_get(v_pos_2458_, 1);
                    v___x_2461_ = lean_byte_array_size(v_array_2459_);
                    v___x_2462_ = lean_nat_dec_lt(v_idx_2460_, v___x_2461_);
                    if v___x_2462_ == 0 {
                        crate::leanh::lean_dec(v_pos_2458_);
                        return v___x_2457_;
                    } else {
                        v_isSharedCheck_2470_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                        if v_isSharedCheck_2470_ == 0 {
                            v_unused_2471_ = crate::leanh::lean_ctor_get(v___x_2457_, 1);
                            crate::leanh::lean_dec(v_unused_2471_);
                            v_unused_2472_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                            crate::leanh::lean_dec(v_unused_2472_);
                            v___x_2464_ = v___x_2457_;
                            v_isShared_2465_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2457_);
                            v___x_2464_ = crate::leanh::lean_box(0);
                            v_isShared_2465_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_2457_;
                }
            }
            1 => {
                v___x_2466_ = l_Std_Http_Header_Host_parse___lam__0___closed__1;
                if v_isShared_2465_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2464_, 1);
                    crate::leanh::lean_ctor_set(v___x_2464_, 1, v___x_2466_);
                    v___x_2468_ = v___x_2464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_pos_2458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2466_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Host_parse___lam__0___boxed(
    mut v___x_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2475_ = l_Std_Http_Header_Host_parse___lam__0(v___x_2473_, v___y_2474_);
    crate::leanh::lean_dec_ref(v___x_2473_);
    return v_res_2475_;
}
pub unsafe fn l_Std_Http_Header_Host_parse(
    mut v_v_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parsed_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v_fst_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2487_ = l_Std_Http_Header_Host_parse___closed__1;
                v___x_2488_ = lean_string_to_utf8(v_v_2486_);
                v_parsed_2489_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2487_, v___x_2488_);
                if crate::leanh::lean_obj_tag(v_parsed_2489_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_parsed_2489_, 1);
                    v___x_2490_ = crate::leanh::lean_box(0);
                    return v___x_2490_;
                } else {
                    v_a_2491_ = crate::leanh::lean_ctor_get(v_parsed_2489_, 0);
                    v_isSharedCheck_2507_ =
                        (!crate::leanh::lean_is_exclusive(v_parsed_2489_)) as u8;
                    if v_isSharedCheck_2507_ == 0 {
                        v___x_2493_ = v_parsed_2489_;
                        v_isShared_2494_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2491_);
                        crate::leanh::lean_dec(v_parsed_2489_);
                        v___x_2493_ = crate::leanh::lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2495_ = crate::leanh::lean_ctor_get(v_a_2491_, 0);
                v_snd_2496_ = crate::leanh::lean_ctor_get(v_a_2491_, 1);
                v_isSharedCheck_2506_ = (!crate::leanh::lean_is_exclusive(v_a_2491_)) as u8;
                if v_isSharedCheck_2506_ == 0 {
                    v___x_2498_ = v_a_2491_;
                    v_isShared_2499_ = v_isSharedCheck_2506_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2496_);
                    crate::leanh::lean_inc(v_fst_2495_);
                    crate::leanh::lean_dec(v_a_2491_);
                    v___x_2498_ = crate::leanh::lean_box(0);
                    v_isShared_2499_ = v_isSharedCheck_2506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2499_ == 0 {
                    v___x_2501_ = v___x_2498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_fst_2495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_snd_2496_);
                    v___x_2501_ = v_reuseFailAlloc_2505_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2501_);
                    v___x_2503_ = v___x_2493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
                    v___x_2503_ = v_reuseFailAlloc_2504_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Host_parse___boxed(
    mut v_v_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Std_Http_Header_Host_parse(v_v_2508_);
    crate::leanh::lean_dec_ref(v_v_2508_);
    return v_res_2509_;
}
pub unsafe fn l_Std_Http_Header_Host_serialize(
    mut v_host_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2547_: u16 = 0;
    let mut v___y_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_port_2522_ = crate::leanh::lean_ctor_get(v_host_2512_, 1);
                match crate::leanh::lean_obj_tag(v_port_2522_) {
                    0 => {
                        v_host_2523_ = crate::leanh::lean_ctor_get(v_host_2512_, 0);
                        crate::leanh::lean_inc_ref(v_host_2523_);
                        crate::leanh::lean_dec_ref(v_host_2512_);
                        match crate::leanh::lean_obj_tag(v_host_2523_) {
                            0 => {
                                v_name_2524_ = crate::leanh::lean_ctor_get(v_host_2523_, 0);
                                crate::leanh::lean_inc_ref(v_name_2524_);
                                crate::leanh::lean_dec_ref_known(v_host_2523_, 1);
                                v___x_2525_ = l_Std_Http_Header_Value_ofString_x21(v_name_2524_);
                                v___y_2514_ = v___x_2525_;
                                state = 1;
                                continue;
                            }
                            1 => {
                                v_ipv4_2526_ = crate::leanh::lean_ctor_get(v_host_2523_, 0);
                                crate::leanh::lean_inc_ref(v_ipv4_2526_);
                                crate::leanh::lean_dec_ref_known(v_host_2523_, 1);
                                v___x_2527_ = lean_uv_ntop_v4(v_ipv4_2526_);
                                crate::leanh::lean_dec_ref(v_ipv4_2526_);
                                v___x_2528_ = l_Std_Http_Header_Value_ofString_x21(v___x_2527_);
                                v___y_2514_ = v___x_2528_;
                                state = 1;
                                continue;
                            }
                            _ => {
                                v_ipv6_2529_ = crate::leanh::lean_ctor_get(v_host_2523_, 0);
                                crate::leanh::lean_inc_ref(v_ipv6_2529_);
                                crate::leanh::lean_dec_ref_known(v_host_2523_, 1);
                                v___x_2530_ = l_Std_Http_Header_Host_serialize___closed__1;
                                v___x_2531_ = lean_uv_ntop_v6(v_ipv6_2529_);
                                crate::leanh::lean_dec_ref(v_ipv6_2529_);
                                v___x_2532_ = lean_string_append(v___x_2530_, v___x_2531_);
                                crate::leanh::lean_dec_ref(v___x_2531_);
                                v___x_2533_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4;
                                v___x_2534_ = lean_string_append(v___x_2532_, v___x_2533_);
                                v___x_2535_ = l_Std_Http_Header_Value_ofString_x21(v___x_2534_);
                                v___y_2514_ = v___x_2535_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_host_2536_ = crate::leanh::lean_ctor_get(v_host_2512_, 0);
                        crate::leanh::lean_inc_ref(v_host_2536_);
                        crate::leanh::lean_dec_ref(v_host_2512_);
                        match crate::leanh::lean_obj_tag(v_host_2536_) {
                            0 => {
                                v_name_2537_ = crate::leanh::lean_ctor_get(v_host_2536_, 0);
                                crate::leanh::lean_inc_ref(v_name_2537_);
                                crate::leanh::lean_dec_ref_known(v_host_2536_, 1);
                                v___y_2518_ = v_name_2537_;
                                state = 2;
                                continue;
                            }
                            1 => {
                                v_ipv4_2538_ = crate::leanh::lean_ctor_get(v_host_2536_, 0);
                                crate::leanh::lean_inc_ref(v_ipv4_2538_);
                                crate::leanh::lean_dec_ref_known(v_host_2536_, 1);
                                v___x_2539_ = lean_uv_ntop_v4(v_ipv4_2538_);
                                crate::leanh::lean_dec_ref(v_ipv4_2538_);
                                v___y_2518_ = v___x_2539_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                v_ipv6_2540_ = crate::leanh::lean_ctor_get(v_host_2536_, 0);
                                crate::leanh::lean_inc_ref(v_ipv6_2540_);
                                crate::leanh::lean_dec_ref_known(v_host_2536_, 1);
                                v___x_2541_ = l_Std_Http_Header_Host_serialize___closed__1;
                                v___x_2542_ = lean_uv_ntop_v6(v_ipv6_2540_);
                                crate::leanh::lean_dec_ref(v_ipv6_2540_);
                                v___x_2543_ = lean_string_append(v___x_2541_, v___x_2542_);
                                crate::leanh::lean_dec_ref(v___x_2542_);
                                v___x_2544_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4;
                                v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
                                v___y_2518_ = v___x_2545_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_inc_ref(v_port_2522_);
                        v_host_2546_ = crate::leanh::lean_ctor_get(v_host_2512_, 0);
                        crate::leanh::lean_inc_ref(v_host_2546_);
                        crate::leanh::lean_dec_ref(v_host_2512_);
                        v_port_2547_ = crate::leanh::lean_ctor_get_uint16(v_port_2522_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_port_2522_, 0);
                        match crate::leanh::lean_obj_tag(v_host_2546_) {
                            0 => {
                                v_name_2556_ = crate::leanh::lean_ctor_get(v_host_2546_, 0);
                                crate::leanh::lean_inc_ref(v_name_2556_);
                                crate::leanh::lean_dec_ref_known(v_host_2546_, 1);
                                v___y_2549_ = v_name_2556_;
                                state = 3;
                                continue;
                            }
                            1 => {
                                v_ipv4_2557_ = crate::leanh::lean_ctor_get(v_host_2546_, 0);
                                crate::leanh::lean_inc_ref(v_ipv4_2557_);
                                crate::leanh::lean_dec_ref_known(v_host_2546_, 1);
                                v___x_2558_ = lean_uv_ntop_v4(v_ipv4_2557_);
                                crate::leanh::lean_dec_ref(v_ipv4_2557_);
                                v___y_2549_ = v___x_2558_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                v_ipv6_2559_ = crate::leanh::lean_ctor_get(v_host_2546_, 0);
                                crate::leanh::lean_inc_ref(v_ipv6_2559_);
                                crate::leanh::lean_dec_ref_known(v_host_2546_, 1);
                                v___x_2560_ = l_Std_Http_Header_Host_serialize___closed__1;
                                v___x_2561_ = lean_uv_ntop_v6(v_ipv6_2559_);
                                crate::leanh::lean_dec_ref(v_ipv6_2559_);
                                v___x_2562_ = lean_string_append(v___x_2560_, v___x_2561_);
                                crate::leanh::lean_dec_ref(v___x_2561_);
                                v___x_2563_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4;
                                v___x_2564_ = lean_string_append(v___x_2562_, v___x_2563_);
                                v___y_2549_ = v___x_2564_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2515_ = l_Std_Http_Header_instReprHost_repr___redArg___closed__0;
                v___x_2516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                crate::leanh::lean_ctor_set(v___x_2516_, 1, v___y_2514_);
                return v___x_2516_;
            }
            2 => {
                v___x_2519_ = l_Std_Http_Header_Host_serialize___closed__0;
                v___x_2520_ = lean_string_append(v___y_2518_, v___x_2519_);
                v___x_2521_ = l_Std_Http_Header_Value_ofString_x21(v___x_2520_);
                v___y_2514_ = v___x_2521_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2550_ = l_Std_Http_Header_Host_serialize___closed__0;
                v___x_2551_ = lean_string_append(v___y_2549_, v___x_2550_);
                v___x_2552_ = lean_uint16_to_nat(v_port_2547_);
                v___x_2553_ = l_Nat_reprFast(v___x_2552_);
                v___x_2554_ = lean_string_append(v___x_2551_, v___x_2553_);
                crate::leanh::lean_dec_ref(v___x_2553_);
                v___x_2555_ = l_Std_Http_Header_Value_ofString_x21(v___x_2554_);
                v___y_2514_ = v___x_2555_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Expect_toCtorIdx(
    mut v_x_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_2572_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprExpect_repr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Std_Http_Header_instReprExpect_repr___closed__1;
    v___x_2580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once
        ),
        _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10,
    );
    v___x_2581_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2581_, 0, v___x_2580_);
    crate::leanh::lean_ctor_set(v___x_2581_, 1, v___x_2579_);
    return v___x_2581_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprExpect_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = 0;
    v___x_2583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprExpect_repr___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprExpect_repr___closed__2_once),
        _init_l_Std_Http_Header_instReprExpect_repr___closed__2,
    );
    v___x_2584_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2584_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2582_,
    );
    return v___x_2584_;
}
pub unsafe fn l_Std_Http_Header_instReprExpect_repr(
    mut v_x_2585_: *mut crate::leanh::LeanObject,
    mut v_prec_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprExpect_repr___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprExpect_repr___closed__3_once),
        _init_l_Std_Http_Header_instReprExpect_repr___closed__3,
    );
    return v___x_2587_;
}
pub unsafe fn l_Std_Http_Header_instReprExpect_repr___boxed(
    mut v_x_2588_: *mut crate::leanh::LeanObject,
    mut v_prec_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_Http_Header_instReprExpect_repr(v_x_2588_, v_prec_2589_);
    crate::leanh::lean_dec(v_prec_2589_);
    return v_res_2590_;
}
pub unsafe fn l_Std_Http_Header_instBEqExpect_beq(
    mut v_x_2593_: *mut crate::leanh::LeanObject,
    mut v_y_2594_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2595_: u8 = 0;
    v___x_2595_ = 1;
    return v___x_2595_;
}
pub unsafe fn l_Std_Http_Header_instBEqExpect_beq___boxed(
    mut v_x_2596_: *mut crate::leanh::LeanObject,
    mut v_y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2598_: u8 = 0;
    let mut v_r_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_Std_Http_Header_instBEqExpect_beq(v_x_2596_, v_y_2597_);
    v_r_2599_ = crate::leanh::lean_box((v_res_2598_) as usize);
    return v_r_2599_;
}
pub unsafe fn l_Std_Http_Header_Expect_parse(
    mut v_v_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_normalized_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: u8 = 0;
    v___x_2606_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2607_ = lean_string_utf8_byte_size(v_v_2605_);
    v___x_2608_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2608_, 0, v_v_2605_);
    crate::leanh::lean_ctor_set(v___x_2608_, 1, v___x_2606_);
    crate::leanh::lean_ctor_set(v___x_2608_, 2, v___x_2607_);
    v___x_2609_ = l_String_Slice_trimAscii(v___x_2608_);
    v___x_2610_ = l_String_Slice_toString(v___x_2609_);
    crate::leanh::lean_dec_ref(v___x_2609_);
    v_normalized_2611_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_2610_, v___x_2606_);
    v___x_2612_ = l_Std_Http_Header_Expect_parse___closed__0;
    v___x_2613_ = lean_string_dec_eq(v_normalized_2611_, v___x_2612_);
    crate::leanh::lean_dec_ref(v_normalized_2611_);
    if v___x_2613_ == 0 {
        let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2614_ = crate::leanh::lean_box(0);
        return v___x_2614_;
    } else {
        let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2615_ = l_Std_Http_Header_Expect_parse___closed__1;
        return v___x_2615_;
    }
}
pub unsafe fn _init_l_Std_Http_Header_Expect_serialize___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2616_ = l_Std_Http_Header_Expect_parse___closed__0;
    v___x_2617_ = l_Std_Http_Header_Value_ofString_x21(v___x_2616_);
    return v___x_2617_;
}
pub unsafe fn _init_l_Std_Http_Header_Expect_serialize___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Expect_serialize___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Header_Expect_serialize___closed__0_once),
        _init_l_Std_Http_Header_Expect_serialize___closed__0,
    );
    v___x_2619_ = l_Std_Http_Header_Name_expect;
    v___x_2620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 1, v___x_2618_);
    return v___x_2620_;
}
pub unsafe fn l_Std_Http_Header_Expect_serialize(
    mut v_x_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Expect_serialize___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Header_Expect_serialize___closed__1_once),
        _init_l_Std_Http_Header_Expect_serialize___closed__1,
    );
    return v___x_2622_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Headers_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_URI(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1 =
        _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Headers_Basic(
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
pub unsafe fn initialize_Std_Http_Data_Headers_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_URI(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Headers_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Headers_Basic(builtin);
}
