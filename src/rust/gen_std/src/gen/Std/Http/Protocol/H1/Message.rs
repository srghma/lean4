// Lean compiler output
// Module: Std.Http.Protocol.H1.Message
// Imports: Init.Data.Array Std.Http.Data
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_append, lean_string_dec_eq,
    lean_string_from_utf8_unchecked, lean_string_hash, lean_string_to_utf8,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set,
    lean_uint16_to_nat, lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint32_to_uint8, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
    lean_uv_ntop_v4, lean_uv_ntop_v6,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::{
    initialize_Init_Data_Array, runtime_initialize_Init_Data_Array,
};
use crate::r#gen::Init::Data::List::Basic::l_List_mapTR_loop___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_splitToSubslice___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::{l_String_decEq___boxed, l_String_hash___boxed};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Http::Data::Headers::Basic::{
    l_Std_Http_Header_Connection_parse, l_Std_Http_Header_ContentLength_parse,
    l_Std_Http_Header_TransferEncoding_isChunked, l_Std_Http_Header_TransferEncoding_parse,
};
use crate::r#gen::Std::Http::Data::Headers::Name::{
    l_Std_Http_Header_Name_connection, l_Std_Http_Header_Name_contentLength,
    l_Std_Http_Header_Name_transferEncoding,
};
use crate::r#gen::Std::Http::Data::Headers::{
    l_Std_Http_Headers_empty, l_Std_Http_Headers_fold___redArg,
};
use crate::r#gen::Std::Http::Data::Request::l_Std_Http_Request_instReprHead_repr___redArg;
use crate::r#gen::Std::Http::Data::Response::l_Std_Http_Response_instReprHead_repr___redArg;
use crate::r#gen::Std::Http::Data::Status::{
    l_Std_Http_Status_reasonPhrase, l_Std_Http_Status_toCode,
};
use crate::r#gen::Std::Http::Data::URI::Basic::l_Std_Http_URI_Query_formatQueryParam;
use crate::r#gen::Std::Http::Data::URI::Encoding::l_Std_Http_URI_EncodedFragment_encode;
use crate::r#gen::Std::Http::Data::Version::l_Std_Http_instBEqVersion_beq;
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::IndexMultiMap::l_Std_Internal_IndexMultiMap_instDecidableMem___redArg;
pub static l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instBEqDirection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_instBEqDirection: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value:
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
    m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
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
static mut l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
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
static mut l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 108, 111, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [107, 101, 101, 112, 45, 97, 108, 105, 118, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value:
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
static mut l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprHead___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instReprHead___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprHead___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprHead___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instReprHead___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprHead___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0_value:
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
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1_value:
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
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3_value:
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
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5_value:
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
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value:
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
    m_fun: l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_value:
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
    m_fun: l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 49, 46, 48, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 49, 46, 49, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 50, 46, 48, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 51, 46, 48, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value:
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
    m_data: [63, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value:
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
    m_data: [38, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value:
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
    m_data: [58, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value:
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
    m_data: [35, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value:
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
    m_data: [91, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value:
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
    m_data: [93, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value:
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
    m_data: [47, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26: u8 = 0;
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value:
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
    m_data: [47, 47, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value:
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
    m_data: [64, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value:
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
    m_data: [42, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 67, 76, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value:
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
        66, 65, 83, 69, 76, 73, 78, 69, 45, 67, 79, 78, 84, 82, 79, 76, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value:
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
    m_data: [66, 73, 78, 68, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value:
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
    m_data: [67, 72, 69, 67, 75, 73, 78, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [67, 72, 69, 67, 75, 79, 85, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value:
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
    m_data: [67, 79, 78, 78, 69, 67, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value:
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
    m_data: [67, 79, 80, 89, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value:
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
    m_data: [68, 69, 76, 69, 84, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [71, 69, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value:
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
    m_data: [72, 69, 65, 68, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value:
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
    m_data: [76, 65, 66, 69, 76, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value:
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
    m_data: [76, 73, 78, 75, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value:
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
    m_data: [76, 79, 67, 75, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value:
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
    m_data: [77, 69, 82, 71, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [77, 75, 65, 67, 84, 73, 86, 73, 84, 89, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [77, 75, 67, 65, 76, 69, 78, 68, 65, 82, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value:
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
    m_data: [77, 75, 67, 79, 76, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [77, 75, 82, 69, 68, 73, 82, 69, 67, 84, 82, 69, 70, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [77, 75, 87, 79, 82, 75, 83, 80, 65, 67, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value:
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
    m_data: [77, 79, 86, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value:
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
    m_data: [79, 80, 84, 73, 79, 78, 83, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [79, 82, 68, 69, 82, 80, 65, 84, 67, 72, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value:
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
    m_data: [80, 65, 84, 67, 72, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value:
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
    m_data: [80, 79, 83, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [80, 82, 73, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [80, 82, 79, 80, 70, 73, 78, 68, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [80, 82, 79, 80, 80, 65, 84, 67, 72, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [80, 85, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value:
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
    m_data: [81, 85, 69, 82, 89, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value:
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
    m_data: [82, 69, 66, 73, 78, 68, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value:
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
    m_data: [82, 69, 80, 79, 82, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value:
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
    m_data: [83, 69, 65, 82, 67, 72, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value:
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
    m_data: [84, 82, 65, 67, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value:
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
    m_data: [85, 78, 66, 73, 78, 68, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [85, 78, 67, 72, 69, 67, 75, 79, 85, 84, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value:
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
    m_data: [85, 78, 76, 73, 78, 75, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value:
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
    m_data: [85, 78, 76, 79, 67, 75, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value:
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
    m_data: [85, 80, 68, 65, 84, 69, 0],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        85, 80, 68, 65, 84, 69, 82, 69, 68, 73, 82, 69, 67, 84, 82, 69, 70, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        86, 69, 82, 83, 73, 79, 78, 45, 67, 79, 78, 84, 82, 79, 76, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1_value:
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
    m_fun: l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorIdx(
    mut v_x_1114_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_1114_ == 0 {
        let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1115_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1115_;
    } else {
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1116_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1116_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorIdx___boxed(
    mut v_x_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1118_: u8 = 0;
    let mut v_res_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1118_ = (crate::leanh::lean_unbox(v_x_1117_) as u8);
    v_res_1119_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_boxed_1118_);
    return v_res_1119_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_toCtorIdx(
    mut v_x_1120_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_toCtorIdx___boxed(
    mut v_x_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1123_: u8 = 0;
    let mut v_res_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1123_ = (crate::leanh::lean_unbox(v_x_1122_) as u8);
    v_res_1124_ = l_Std_Http_Protocol_H1_Direction_toCtorIdx(v_x_4__boxed_1123_);
    return v_res_1124_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(
    mut v_k_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1125_);
    return v_k_1125_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorElim___redArg___boxed(
    mut v_k_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(v_k_1126_);
    crate::leanh::lean_dec(v_k_1126_);
    return v_res_1127_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorElim(
    mut v_motive_1128_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1129_: *mut crate::leanh::LeanObject,
    mut v_t_1130_: u8,
    mut v_h_1131_: *mut crate::leanh::LeanObject,
    mut v_k_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1132_);
    return v_k_1132_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_ctorElim___boxed(
    mut v_motive_1133_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1134_: *mut crate::leanh::LeanObject,
    mut v_t_1135_: *mut crate::leanh::LeanObject,
    mut v_h_1136_: *mut crate::leanh::LeanObject,
    mut v_k_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1138_: u8 = 0;
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1138_ = (crate::leanh::lean_unbox(v_t_1135_) as u8);
    v_res_1139_ = l_Std_Http_Protocol_H1_Direction_ctorElim(
        v_motive_1133_,
        v_ctorIdx_1134_,
        v_t_boxed_1138_,
        v_h_1136_,
        v_k_1137_,
    );
    crate::leanh::lean_dec(v_k_1137_);
    crate::leanh::lean_dec(v_ctorIdx_1134_);
    return v_res_1139_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(
    mut v_receiving_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_receiving_1140_);
    return v_receiving_1140_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg___boxed(
    mut v_receiving_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(v_receiving_1141_);
    crate::leanh::lean_dec(v_receiving_1141_);
    return v_res_1142_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_receiving_elim(
    mut v_motive_1143_: *mut crate::leanh::LeanObject,
    mut v_t_1144_: u8,
    mut v_h_1145_: *mut crate::leanh::LeanObject,
    mut v_receiving_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_receiving_1146_);
    return v_receiving_1146_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_receiving_elim___boxed(
    mut v_motive_1147_: *mut crate::leanh::LeanObject,
    mut v_t_1148_: *mut crate::leanh::LeanObject,
    mut v_h_1149_: *mut crate::leanh::LeanObject,
    mut v_receiving_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1151_: u8 = 0;
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1151_ = (crate::leanh::lean_unbox(v_t_1148_) as u8);
    v_res_1152_ = l_Std_Http_Protocol_H1_Direction_receiving_elim(
        v_motive_1147_,
        v_t_boxed_1151_,
        v_h_1149_,
        v_receiving_1150_,
    );
    crate::leanh::lean_dec(v_receiving_1150_);
    return v_res_1152_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(
    mut v_sending_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sending_1153_);
    return v_sending_1153_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_sending_elim___redArg___boxed(
    mut v_sending_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(v_sending_1154_);
    crate::leanh::lean_dec(v_sending_1154_);
    return v_res_1155_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_sending_elim(
    mut v_motive_1156_: *mut crate::leanh::LeanObject,
    mut v_t_1157_: u8,
    mut v_h_1158_: *mut crate::leanh::LeanObject,
    mut v_sending_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sending_1159_);
    return v_sending_1159_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_sending_elim___boxed(
    mut v_motive_1160_: *mut crate::leanh::LeanObject,
    mut v_t_1161_: *mut crate::leanh::LeanObject,
    mut v_h_1162_: *mut crate::leanh::LeanObject,
    mut v_sending_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1164_: u8 = 0;
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1164_ = (crate::leanh::lean_unbox(v_t_1161_) as u8);
    v_res_1165_ = l_Std_Http_Protocol_H1_Direction_sending_elim(
        v_motive_1160_,
        v_t_boxed_1164_,
        v_h_1162_,
        v_sending_1163_,
    );
    crate::leanh::lean_dec(v_sending_1163_);
    return v_res_1165_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqDirection_beq(
    mut v_x_1166_: u8,
    mut v_y_1167_: u8,
) -> u8 {
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    v___x_1168_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_1166_);
    v___x_1169_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_y_1167_);
    v___x_1170_ = lean_nat_dec_eq(v___x_1168_, v___x_1169_);
    crate::leanh::lean_dec(v___x_1169_);
    crate::leanh::lean_dec(v___x_1168_);
    return v___x_1170_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(
    mut v_x_1171_: *mut crate::leanh::LeanObject,
    mut v_y_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1173_: u8 = 0;
    let mut v_y_18__boxed_1174_: u8 = 0;
    let mut v_res_1175_: u8 = 0;
    let mut v_r_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1173_ = (crate::leanh::lean_unbox(v_x_1171_) as u8);
    v_y_18__boxed_1174_ = (crate::leanh::lean_unbox(v_y_1172_) as u8);
    v_res_1175_ =
        l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_17__boxed_1173_, v_y_18__boxed_1174_);
    v_r_1176_ = crate::leanh::lean_box((v_res_1175_) as usize);
    return v_r_1176_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_swap(mut v_x_1179_: u8) -> u8 {
    if v_x_1179_ == 0 {
        let mut v___x_1180_: u8 = 0;
        v___x_1180_ = 1;
        return v___x_1180_;
    } else {
        let mut v___x_1181_: u8 = 0;
        v___x_1181_ = 0;
        return v___x_1181_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Direction_swap___boxed(
    mut v_x_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18__boxed_1183_: u8 = 0;
    let mut v_res_1184_: u8 = 0;
    let mut v_r_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_1183_ = (crate::leanh::lean_unbox(v_x_1182_) as u8);
    v_res_1184_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_18__boxed_1183_);
    v_r_1185_ = crate::leanh::lean_box((v_res_1184_) as usize);
    return v_r_1185_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_headers(
    mut v_dir_1186_: u8,
    mut v_m_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_headers_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_headers_1188_ = crate::leanh::lean_ctor_get(v_m_1187_, 1);
    crate::leanh::lean_inc_ref(v_headers_1188_);
    return v_headers_1188_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_headers___boxed(
    mut v_dir_1189_: *mut crate::leanh::LeanObject,
    mut v_m_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1191_: u8 = 0;
    let mut v_res_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1191_ = (crate::leanh::lean_unbox(v_dir_1189_) as u8);
    v_res_1192_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_boxed_1191_, v_m_1190_);
    crate::leanh::lean_dec(v_m_1190_);
    return v_res_1192_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_setHeaders(
    mut v_dir_1193_: u8,
    mut v_m_1194_: *mut crate::leanh::LeanObject,
    mut v_headers_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_method_1196_: u8 = 0;
    let mut v_version_1197_: u8 = 0;
    let mut v_uri_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_unused_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_status_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1208_: u8 = 0;
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1215_: u8 = 0;
    let mut v_unused_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_dir_1193_ == 0 {
                    v_method_1196_ = crate::leanh::lean_ctor_get_uint8(
                        v_m_1194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_version_1197_ = crate::leanh::lean_ctor_get_uint8(
                        v_m_1194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_uri_1198_ = crate::leanh::lean_ctor_get(v_m_1194_, 0);
                    v_isSharedCheck_1205_ = (!crate::leanh::lean_is_exclusive(v_m_1194_)) as u8;
                    if v_isSharedCheck_1205_ == 0 {
                        v_unused_1206_ = crate::leanh::lean_ctor_get(v_m_1194_, 1);
                        crate::leanh::lean_dec(v_unused_1206_);
                        v___x_1200_ = v_m_1194_;
                        v_isShared_1201_ = v_isSharedCheck_1205_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_uri_1198_);
                        crate::leanh::lean_dec(v_m_1194_);
                        v___x_1200_ = crate::leanh::lean_box(0);
                        v_isShared_1201_ = v_isSharedCheck_1205_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_status_1207_ = crate::leanh::lean_ctor_get(v_m_1194_, 0);
                    v_version_1208_ = crate::leanh::lean_ctor_get_uint8(
                        v_m_1194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1215_ = (!crate::leanh::lean_is_exclusive(v_m_1194_)) as u8;
                    if v_isSharedCheck_1215_ == 0 {
                        v_unused_1216_ = crate::leanh::lean_ctor_get(v_m_1194_, 1);
                        crate::leanh::lean_dec(v_unused_1216_);
                        v___x_1210_ = v_m_1194_;
                        v_isShared_1211_ = v_isSharedCheck_1215_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_status_1207_);
                        crate::leanh::lean_dec(v_m_1194_);
                        v___x_1210_ = crate::leanh::lean_box(0);
                        v_isShared_1211_ = v_isSharedCheck_1215_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1200_, 1, v_headers_1195_);
                    v___x_1203_ = v___x_1200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = crate::leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_uri_1198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_headers_1195_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1204_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_method_1196_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1204_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_1197_,
                    );
                    v___x_1203_ = v_reuseFailAlloc_1204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1203_;
            }
            3 => {
                if v_isShared_1211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1210_, 1, v_headers_1195_);
                    v___x_1213_ = v___x_1210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1214_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_status_1207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_headers_1195_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1214_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_version_1208_,
                    );
                    v___x_1213_ = v_reuseFailAlloc_1214_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(
    mut v_dir_1217_: *mut crate::leanh::LeanObject,
    mut v_m_1218_: *mut crate::leanh::LeanObject,
    mut v_headers_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1220_ = (crate::leanh::lean_unbox(v_dir_1217_) as u8);
    v_res_1221_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(
        v_dir_boxed_1220_,
        v_m_1218_,
        v_headers_1219_,
    );
    return v_res_1221_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_version(
    mut v_dir_1222_: u8,
    mut v_m_1223_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_dir_1222_ == 0 {
        let mut v_version_1224_: u8 = 0;
        v_version_1224_ = crate::leanh::lean_ctor_get_uint8(
            v_m_1223_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        );
        return v_version_1224_;
    } else {
        let mut v_version_1225_: u8 = 0;
        v_version_1225_ = crate::leanh::lean_ctor_get_uint8(
            v_m_1223_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        return v_version_1225_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_version___boxed(
    mut v_dir_1226_: *mut crate::leanh::LeanObject,
    mut v_m_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1228_: u8 = 0;
    let mut v_res_1229_: u8 = 0;
    let mut v_r_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1228_ = (crate::leanh::lean_unbox(v_dir_1226_) as u8);
    v_res_1229_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_1228_, v_m_1227_);
    crate::leanh::lean_dec(v_m_1227_);
    v_r_1230_ = crate::leanh::lean_box((v_res_1229_) as usize);
    return v_r_1230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_x_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1233_ = crate::leanh::lean_ctor_get(v_x_1232_, 0);
                v_value_1234_ = crate::leanh::lean_ctor_get(v_x_1232_, 1);
                v_tail_1235_ = crate::leanh::lean_ctor_get(v_x_1232_, 2);
                v___x_1236_ = lean_string_dec_eq(v_key_1233_, v_a_1231_);
                if v___x_1236_ == 0 {
                    v_x_1232_ = v_tail_1235_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_1234_);
                    return v_value_1234_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(
    mut v_a_1238_: *mut crate::leanh::LeanObject,
    mut v_x_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1240_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_1238_, v_x_1239_);
    crate::leanh::lean_dec(v_x_1239_);
    crate::leanh::lean_dec_ref(v_a_1238_);
    return v_res_1240_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(
    mut v_m_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u64 = 0;
    let mut v___x_1246_: u64 = 0;
    let mut v___x_1247_: u64 = 0;
    let mut v_fold_1248_: u64 = 0;
    let mut v___x_1249_: u64 = 0;
    let mut v___x_1250_: u64 = 0;
    let mut v___x_1251_: u64 = 0;
    let mut v___x_1252_: usize = 0;
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: usize = 0;
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1243_ = crate::leanh::lean_ctor_get(v_m_1241_, 1);
    v___x_1244_ = lean_array_get_size(v_buckets_1243_);
    v___x_1245_ = lean_string_hash(v_a_1242_);
    v___x_1246_ = 32u64;
    v___x_1247_ = lean_uint64_shift_right(v___x_1245_, v___x_1246_);
    v_fold_1248_ = lean_uint64_xor(v___x_1245_, v___x_1247_);
    v___x_1249_ = 16u64;
    v___x_1250_ = lean_uint64_shift_right(v_fold_1248_, v___x_1249_);
    v___x_1251_ = lean_uint64_xor(v_fold_1248_, v___x_1250_);
    v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
    v___x_1253_ = lean_usize_of_nat(v___x_1244_);
    v___x_1254_ = 1usize;
    v___x_1255_ = lean_usize_sub(v___x_1253_, v___x_1254_);
    v___x_1256_ = lean_usize_land(v___x_1252_, v___x_1255_);
    v___x_1257_ = lean_array_uget_borrowed(v_buckets_1243_, v___x_1256_);
    v___x_1258_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_1242_, v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(
    mut v_m_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_1259_, v_a_1260_);
    crate::leanh::lean_dec_ref(v_a_1260_);
    crate::leanh::lean_dec_ref(v_m_1259_);
    return v_res_1261_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(
    mut v___x_1262_: *mut crate::leanh::LeanObject,
    mut v___x_1263_: *mut crate::leanh::LeanObject,
    mut v_i_1264_: *mut crate::leanh::LeanObject,
    mut v_j_1265_: *mut crate::leanh::LeanObject,
    mut v_bs_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1268_: u8 = 0;
    let mut v_entries_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1267_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1268_ = lean_nat_dec_eq(v_i_1264_, v_zero_1267_);
                if v_isZero_1268_ == 1 {
                    crate::leanh::lean_dec(v_j_1265_);
                    crate::leanh::lean_dec(v_i_1264_);
                    return v_bs_1266_;
                } else {
                    v_entries_1269_ = crate::leanh::lean_ctor_get(v___x_1262_, 0);
                    v___x_1270_ = lean_array_fget_borrowed(v___x_1263_, v_j_1265_);
                    v___x_1271_ = lean_array_fget_borrowed(v_entries_1269_, v___x_1270_);
                    v_snd_1272_ = crate::leanh::lean_ctor_get(v___x_1271_, 1);
                    v_one_1273_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1274_ = lean_nat_sub(v_i_1264_, v_one_1273_);
                    crate::leanh::lean_dec(v_i_1264_);
                    v___x_1275_ = lean_nat_add(v_j_1265_, v_one_1273_);
                    crate::leanh::lean_dec(v_j_1265_);
                    crate::leanh::lean_inc(v_snd_1272_);
                    v___x_1276_ = lean_array_push(v_bs_1266_, v_snd_1272_);
                    v_i_1264_ = v_n_1274_;
                    v_j_1265_ = v___x_1275_;
                    v_bs_1266_ = v___x_1276_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(
    mut v___x_1278_: *mut crate::leanh::LeanObject,
    mut v___x_1279_: *mut crate::leanh::LeanObject,
    mut v_i_1280_: *mut crate::leanh::LeanObject,
    mut v_j_1281_: *mut crate::leanh::LeanObject,
    mut v_bs_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1283_ =
        l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(
            v___x_1278_,
            v___x_1279_,
            v_i_1280_,
            v_j_1281_,
            v_bs_1282_,
        );
    crate::leanh::lean_dec_ref(v___x_1279_);
    crate::leanh::lean_dec_ref(v___x_1278_);
    return v_res_1283_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_getSize(
    mut v_dir_1292_: u8,
    mut v_message_1293_: *mut crate::leanh::LeanObject,
    mut v_allowEOFBody_1294_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: u8 = 0;
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_indexes_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_te_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: u8 = 0;
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1295_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1292_, v_message_1293_);
                v___x_1350_ = l_Std_Http_Header_Name_contentLength;
                v___f_1351_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0;
                v___f_1352_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1;
                v___x_1353_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_1351_,
                    v___f_1352_,
                    v___x_1350_,
                    v___x_1295_,
                );
                if v___x_1353_ == 0 {
                    v___x_1354_ = crate::leanh::lean_box(0);
                    v___y_1297_ = v___x_1354_;
                    state = 1;
                    continue;
                } else {
                    v_indexes_1355_ = crate::leanh::lean_ctor_get(v___x_1295_, 1);
                    crate::leanh::lean_inc_ref(v_indexes_1355_);
                    v___x_1356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_1355_, v___x_1350_);
                    crate::leanh::lean_dec_ref(v_indexes_1355_);
                    v___x_1357_ = lean_array_get_size(v___x_1356_);
                    v___x_1358_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1359_ = lean_mk_empty_array_with_capacity(v___x_1357_);
                    v_entries_1360_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_1295_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1359_);
                    crate::leanh::lean_dec(v___x_1356_);
                    v___x_1361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1361_, 0, v_entries_1360_);
                    v___y_1297_ = v___x_1361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1298_ = l_Std_Http_Header_Name_transferEncoding;
                v___f_1299_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0;
                v___f_1300_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1;
                v___x_1301_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_1299_,
                    v___f_1300_,
                    v___x_1298_,
                    v___x_1295_,
                );
                if v___x_1301_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1295_);
                    if crate::leanh::lean_obj_tag(v___y_1297_) == 0 {
                        if v_allowEOFBody_1294_ == 0 {
                            v___x_1302_ = crate::leanh::lean_box(0);
                            return v___x_1302_;
                        } else {
                            v___x_1303_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3;
                            return v___x_1303_;
                        }
                    } else {
                        v_val_1304_ = crate::leanh::lean_ctor_get(v___y_1297_, 0);
                        v_isSharedCheck_1327_ =
                            (!crate::leanh::lean_is_exclusive(v___y_1297_)) as u8;
                        if v_isSharedCheck_1327_ == 0 {
                            v___x_1306_ = v___y_1297_;
                            v_isShared_1307_ = v_isSharedCheck_1327_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1304_);
                            crate::leanh::lean_dec(v___y_1297_);
                            v___x_1306_ = crate::leanh::lean_box(0);
                            v_isShared_1307_ = v_isSharedCheck_1327_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_indexes_1328_ = crate::leanh::lean_ctor_get(v___x_1295_, 1);
                    crate::leanh::lean_inc_ref(v_indexes_1328_);
                    v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_1328_, v___x_1298_);
                    crate::leanh::lean_dec_ref(v_indexes_1328_);
                    v___x_1330_ = lean_array_get_size(v___x_1329_);
                    v___x_1331_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1332_ = lean_mk_empty_array_with_capacity(v___x_1330_);
                    v_entries_1333_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_1295_, v___x_1329_, v___x_1330_, v___x_1331_, v___x_1332_);
                    crate::leanh::lean_dec(v___x_1329_);
                    crate::leanh::lean_dec_ref(v___x_1295_);
                    v___x_1334_ = lean_array_get_size(v_entries_1333_);
                    v___x_1335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1336_ = lean_nat_dec_eq(v___x_1334_, v___x_1335_);
                    if v___x_1336_ == 0 {
                        crate::leanh::lean_dec_ref(v_entries_1333_);
                        crate::leanh::lean_dec(v___y_1297_);
                        v___x_1337_ = crate::leanh::lean_box(0);
                        return v___x_1337_;
                    } else {
                        v___x_1338_ = lean_array_fget(v_entries_1333_, v___x_1331_);
                        crate::leanh::lean_dec_ref(v_entries_1333_);
                        v_te_1339_ = l_Std_Http_Header_TransferEncoding_parse(v___x_1338_);
                        if crate::leanh::lean_obj_tag(v_te_1339_) == 0 {
                            crate::leanh::lean_dec(v___y_1297_);
                            v___x_1340_ = crate::leanh::lean_box(0);
                            return v___x_1340_;
                        } else {
                            v_val_1341_ = crate::leanh::lean_ctor_get(v_te_1339_, 0);
                            crate::leanh::lean_inc(v_val_1341_);
                            crate::leanh::lean_dec_ref_known(v_te_1339_, 1);
                            v___x_1342_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_1341_);
                            crate::leanh::lean_dec(v_val_1341_);
                            if v___x_1342_ == 1 {
                                if crate::leanh::lean_obj_tag(v___y_1297_) == 0 {
                                    v___x_1343_ = l_Std_Http_Protocol_H1_Message_Head_version(
                                        v_dir_1292_,
                                        v_message_1293_,
                                    );
                                    v___x_1344_ = 0;
                                    v___x_1345_ =
                                        l_Std_Http_instBEqVersion_beq(v___x_1343_, v___x_1344_);
                                    if v___x_1345_ == 0 {
                                        v___x_1346_ =
                                            l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4;
                                        return v___x_1346_;
                                    } else {
                                        v___x_1347_ = crate::leanh::lean_box(0);
                                        return v___x_1347_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___y_1297_);
                                    v___x_1348_ = crate::leanh::lean_box(0);
                                    return v___x_1348_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___y_1297_);
                                v___x_1349_ = crate::leanh::lean_box(0);
                                return v___x_1349_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1308_ = lean_array_get_size(v_val_1304_);
                v___x_1309_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1310_ = lean_nat_dec_eq(v___x_1308_, v___x_1309_);
                if v___x_1310_ == 0 {
                    crate::leanh::lean_del_object(v___x_1306_);
                    crate::leanh::lean_dec(v_val_1304_);
                    v___x_1311_ = crate::leanh::lean_box(0);
                    return v___x_1311_;
                } else {
                    v___x_1312_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1313_ = lean_array_fget(v_val_1304_, v___x_1312_);
                    crate::leanh::lean_dec(v_val_1304_);
                    v___x_1314_ = l_Std_Http_Header_ContentLength_parse(v___x_1313_);
                    if crate::leanh::lean_obj_tag(v___x_1314_) == 0 {
                        crate::leanh::lean_del_object(v___x_1306_);
                        v___x_1315_ = crate::leanh::lean_box(0);
                        return v___x_1315_;
                    } else {
                        v_val_1316_ = crate::leanh::lean_ctor_get(v___x_1314_, 0);
                        v_isSharedCheck_1326_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1314_)) as u8;
                        if v_isSharedCheck_1326_ == 0 {
                            v___x_1318_ = v___x_1314_;
                            v_isShared_1319_ = v_isSharedCheck_1326_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1316_);
                            crate::leanh::lean_dec(v___x_1314_);
                            v___x_1318_ = crate::leanh::lean_box(0);
                            v_isShared_1319_ = v_isSharedCheck_1326_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1307_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1306_, 0, v_val_1316_);
                    v___x_1321_ = v___x_1306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_val_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1318_, 0, v___x_1321_);
                    v___x_1323_ = v___x_1318_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
                    v___x_1323_ = v_reuseFailAlloc_1324_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(
    mut v_dir_1362_: *mut crate::leanh::LeanObject,
    mut v_message_1363_: *mut crate::leanh::LeanObject,
    mut v_allowEOFBody_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1365_: u8 = 0;
    let mut v_allowEOFBody_boxed_1366_: u8 = 0;
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1365_ = (crate::leanh::lean_unbox(v_dir_1362_) as u8);
    v_allowEOFBody_boxed_1366_ = (crate::leanh::lean_unbox(v_allowEOFBody_1364_) as u8);
    v_res_1367_ = l_Std_Http_Protocol_H1_Message_Head_getSize(
        v_dir_boxed_1365_,
        v_message_1363_,
        v_allowEOFBody_boxed_1366_,
    );
    crate::leanh::lean_dec(v_message_1363_);
    return v_res_1367_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(
    mut v_00_u03b2_1368_: *mut crate::leanh::LeanObject,
    mut v_m_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
    mut v_hma_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_1369_, v_a_1370_);
    return v___x_1372_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(
    mut v_00_u03b2_1373_: *mut crate::leanh::LeanObject,
    mut v_m_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
    mut v_hma_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_1373_, v_m_1374_, v_a_1375_, v_hma_1376_);
    crate::leanh::lean_dec_ref(v_a_1375_);
    crate::leanh::lean_dec_ref(v_m_1374_);
    return v_res_1377_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(
    mut v___x_1378_: *mut crate::leanh::LeanObject,
    mut v___x_1379_: *mut crate::leanh::LeanObject,
    mut v_as_1380_: *mut crate::leanh::LeanObject,
    mut v_i_1381_: *mut crate::leanh::LeanObject,
    mut v_j_1382_: *mut crate::leanh::LeanObject,
    mut v_inv_1383_: *mut crate::leanh::LeanObject,
    mut v_bs_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1385_ =
        l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(
            v___x_1378_,
            v___x_1379_,
            v_i_1381_,
            v_j_1382_,
            v_bs_1384_,
        );
    return v___x_1385_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(
    mut v___x_1386_: *mut crate::leanh::LeanObject,
    mut v___x_1387_: *mut crate::leanh::LeanObject,
    mut v_as_1388_: *mut crate::leanh::LeanObject,
    mut v_i_1389_: *mut crate::leanh::LeanObject,
    mut v_j_1390_: *mut crate::leanh::LeanObject,
    mut v_inv_1391_: *mut crate::leanh::LeanObject,
    mut v_bs_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(
        v___x_1386_,
        v___x_1387_,
        v_as_1388_,
        v_i_1389_,
        v_j_1390_,
        v_inv_1391_,
        v_bs_1392_,
    );
    crate::leanh::lean_dec_ref(v_as_1388_);
    crate::leanh::lean_dec_ref(v___x_1387_);
    crate::leanh::lean_dec_ref(v___x_1386_);
    return v_res_1393_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(
    mut v_00_u03b2_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
    mut v_x_1396_: *mut crate::leanh::LeanObject,
    mut v_x_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_1395_, v_x_1396_);
    return v___x_1398_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(
    mut v_00_u03b2_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_x_1401_: *mut crate::leanh::LeanObject,
    mut v_x_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_1399_, v_a_1400_, v_x_1401_, v_x_1402_);
    crate::leanh::lean_dec(v_x_1401_);
    crate::leanh::lean_dec_ref(v_a_1400_);
    return v_res_1403_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(
    mut v_as_1405_: *mut crate::leanh::LeanObject,
    mut v_i_1406_: usize,
    mut v_stop_1407_: usize,
) -> u8 {
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1408_ = lean_usize_dec_eq(v_i_1406_, v_stop_1407_);
                if v___x_1408_ == 0 {
                    v___x_1409_ = lean_array_uget_borrowed(v_as_1405_, v_i_1406_);
                    v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0;
                    v___x_1411_ = lean_string_dec_eq(v___x_1409_, v___x_1410_);
                    if v___x_1411_ == 0 {
                        v___x_1412_ = 1usize;
                        v___x_1413_ = lean_usize_add(v_i_1406_, v___x_1412_);
                        v_i_1406_ = v___x_1413_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1411_;
                    }
                } else {
                    v___x_1415_ = 0;
                    return v___x_1415_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(
    mut v_as_1416_: *mut crate::leanh::LeanObject,
    mut v_i_1417_: *mut crate::leanh::LeanObject,
    mut v_stop_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1419_: usize = 0;
    let mut v_stop_boxed_1420_: usize = 0;
    let mut v_res_1421_: u8 = 0;
    let mut v_r_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1419_ = crate::leanh::lean_unbox_usize(v_i_1417_);
    crate::leanh::lean_dec(v_i_1417_);
    v_stop_boxed_1420_ = crate::leanh::lean_unbox_usize(v_stop_1418_);
    crate::leanh::lean_dec(v_stop_1418_);
    v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_1416_, v_i_boxed_1419_, v_stop_boxed_1420_);
    crate::leanh::lean_dec_ref(v_as_1416_);
    v_r_1422_ = crate::leanh::lean_box((v_res_1421_) as usize);
    return v_r_1422_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(
    mut v_as_1424_: *mut crate::leanh::LeanObject,
    mut v_i_1425_: usize,
    mut v_stop_1426_: usize,
) -> u8 {
    let mut v___x_1427_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    let mut v___x_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1427_ = lean_usize_dec_eq(v_i_1425_, v_stop_1426_);
                if v___x_1427_ == 0 {
                    v___x_1428_ = lean_array_uget_borrowed(v_as_1424_, v_i_1425_);
                    v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0;
                    v___x_1430_ = lean_string_dec_eq(v___x_1428_, v___x_1429_);
                    if v___x_1430_ == 0 {
                        v___x_1431_ = 1usize;
                        v___x_1432_ = lean_usize_add(v_i_1425_, v___x_1431_);
                        v_i_1425_ = v___x_1432_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1430_;
                    }
                } else {
                    v___x_1434_ = 0;
                    return v___x_1434_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(
    mut v_as_1435_: *mut crate::leanh::LeanObject,
    mut v_i_1436_: *mut crate::leanh::LeanObject,
    mut v_stop_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1438_: usize = 0;
    let mut v_stop_boxed_1439_: usize = 0;
    let mut v_res_1440_: u8 = 0;
    let mut v_r_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1438_ = crate::leanh::lean_unbox_usize(v_i_1436_);
    crate::leanh::lean_dec(v_i_1436_);
    v_stop_boxed_1439_ = crate::leanh::lean_unbox_usize(v_stop_1437_);
    crate::leanh::lean_dec(v_stop_1437_);
    v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_1435_, v_i_boxed_1438_, v_stop_boxed_1439_);
    crate::leanh::lean_dec_ref(v_as_1435_);
    v_r_1441_ = crate::leanh::lean_box((v_res_1440_) as usize);
    return v_r_1441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(
    mut v_as_1442_: *mut crate::leanh::LeanObject,
    mut v_i_1443_: usize,
    mut v_stop_1444_: usize,
    mut v_b_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v_val_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1451_ = lean_usize_dec_eq(v_i_1443_, v_stop_1444_);
                if v___x_1451_ == 0 {
                    if crate::leanh::lean_obj_tag(v_b_1445_) == 0 {
                        v___y_1447_ = v_b_1445_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1452_ = crate::leanh::lean_ctor_get(v_b_1445_, 0);
                        crate::leanh::lean_inc(v_val_1452_);
                        crate::leanh::lean_dec_ref_known(v_b_1445_, 1);
                        v___x_1453_ = lean_array_uget_borrowed(v_as_1442_, v_i_1443_);
                        crate::leanh::lean_inc(v___x_1453_);
                        v___x_1454_ = l_Std_Http_Header_Connection_parse(v___x_1453_);
                        if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                            crate::leanh::lean_dec(v_val_1452_);
                            v___x_1455_ = crate::leanh::lean_box(0);
                            v___y_1447_ = v___x_1455_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1456_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                            v_isSharedCheck_1464_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                            if v_isSharedCheck_1464_ == 0 {
                                v___x_1458_ = v___x_1454_;
                                v_isShared_1459_ = v_isSharedCheck_1464_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1456_);
                                crate::leanh::lean_dec(v___x_1454_);
                                v___x_1458_ = crate::leanh::lean_box(0);
                                v_isShared_1459_ = v_isSharedCheck_1464_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_b_1445_;
                }
            }
            1 => {
                v___x_1448_ = 1usize;
                v___x_1449_ = lean_usize_add(v_i_1443_, v___x_1448_);
                v_i_1443_ = v___x_1449_;
                v_b_1445_ = v___y_1447_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1460_ = l_Array_append___redArg(v_val_1452_, v_val_1456_);
                crate::leanh::lean_dec(v_val_1456_);
                if v_isShared_1459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1460_);
                    v___x_1462_ = v___x_1458_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1447_ = v___x_1462_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(
    mut v_as_1465_: *mut crate::leanh::LeanObject,
    mut v_i_1466_: *mut crate::leanh::LeanObject,
    mut v_stop_1467_: *mut crate::leanh::LeanObject,
    mut v_b_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1469_: usize = 0;
    let mut v_stop_boxed_1470_: usize = 0;
    let mut v_res_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1469_ = crate::leanh::lean_unbox_usize(v_i_1466_);
    crate::leanh::lean_dec(v_i_1466_);
    v_stop_boxed_1470_ = crate::leanh::lean_unbox_usize(v_stop_1467_);
    crate::leanh::lean_dec(v_stop_1467_);
    v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_1465_, v_i_boxed_1469_, v_stop_boxed_1470_, v_b_1468_);
    crate::leanh::lean_dec_ref(v_as_1465_);
    return v_res_1471_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(
    mut v_dir_1476_: u8,
    mut v_message_1477_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_val_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: usize = 0;
    let mut v___x_1487_: usize = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v___y_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v_val_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: usize = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1500_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1476_, v_message_1477_);
                v___x_1501_ = l_Std_Http_Header_Name_connection;
                v___f_1502_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0;
                v___f_1503_ = l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1;
                v___x_1504_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_1502_,
                    v___f_1503_,
                    v___x_1501_,
                    v___x_1500_,
                );
                if v___x_1504_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1500_);
                    v___x_1505_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0;
                    v_val_1479_ = v___x_1505_;
                    state = 1;
                    continue;
                } else {
                    v_indexes_1506_ = crate::leanh::lean_ctor_get(v___x_1500_, 1);
                    crate::leanh::lean_inc_ref(v_indexes_1506_);
                    v___x_1507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_1506_, v___x_1501_);
                    crate::leanh::lean_dec_ref(v_indexes_1506_);
                    v___x_1508_ = lean_array_get_size(v___x_1507_);
                    v___x_1509_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1510_ = lean_mk_empty_array_with_capacity(v___x_1508_);
                    v_entries_1511_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_1500_, v___x_1507_, v___x_1508_, v___x_1509_, v___x_1510_);
                    crate::leanh::lean_dec(v___x_1507_);
                    crate::leanh::lean_dec_ref(v___x_1500_);
                    v___x_1512_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0;
                    v___x_1513_ = lean_array_get_size(v_entries_1511_);
                    v___x_1514_ = lean_nat_dec_lt(v___x_1509_, v___x_1513_);
                    if v___x_1514_ == 0 {
                        crate::leanh::lean_dec_ref(v_entries_1511_);
                        v_val_1479_ = v___x_1512_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1515_ =
                            l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1;
                        v___x_1516_ = lean_nat_dec_le(v___x_1513_, v___x_1513_);
                        if v___x_1516_ == 0 {
                            if v___x_1514_ == 0 {
                                crate::leanh::lean_dec_ref(v_entries_1511_);
                                v_val_1479_ = v___x_1512_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1517_ = 0usize;
                                v___x_1518_ = lean_usize_of_nat(v___x_1513_);
                                v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_1511_, v___x_1517_, v___x_1518_, v___x_1515_);
                                crate::leanh::lean_dec_ref(v_entries_1511_);
                                v___y_1497_ = v___x_1519_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1520_ = 0usize;
                            v___x_1521_ = lean_usize_of_nat(v___x_1513_);
                            v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_1511_, v___x_1520_, v___x_1521_, v___x_1515_);
                            crate::leanh::lean_dec_ref(v_entries_1511_);
                            v___y_1497_ = v___x_1522_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1480_ =
                    l_Std_Http_Protocol_H1_Message_Head_version(v_dir_1476_, v_message_1477_);
                v___x_1481_ = 1;
                v___x_1482_ = l_Std_Http_instBEqVersion_beq(v___x_1480_, v___x_1481_);
                if v___x_1482_ == 0 {
                    v___x_1483_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1484_ = lean_array_get_size(v_val_1479_);
                    v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
                    if v___x_1485_ == 0 {
                        crate::leanh::lean_dec_ref(v_val_1479_);
                        return v___x_1482_;
                    } else {
                        if v___x_1485_ == 0 {
                            crate::leanh::lean_dec_ref(v_val_1479_);
                            return v___x_1482_;
                        } else {
                            v___x_1486_ = 0usize;
                            v___x_1487_ = lean_usize_of_nat(v___x_1484_);
                            v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_1479_, v___x_1486_, v___x_1487_);
                            crate::leanh::lean_dec_ref(v_val_1479_);
                            return v___x_1488_;
                        }
                    }
                } else {
                    v___x_1489_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1490_ = lean_array_get_size(v_val_1479_);
                    v___x_1491_ = lean_nat_dec_lt(v___x_1489_, v___x_1490_);
                    if v___x_1491_ == 0 {
                        crate::leanh::lean_dec_ref(v_val_1479_);
                        return v___x_1482_;
                    } else {
                        if v___x_1491_ == 0 {
                            crate::leanh::lean_dec_ref(v_val_1479_);
                            return v___x_1482_;
                        } else {
                            v___x_1492_ = 0usize;
                            v___x_1493_ = lean_usize_of_nat(v___x_1490_);
                            v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_1479_, v___x_1492_, v___x_1493_);
                            crate::leanh::lean_dec_ref(v_val_1479_);
                            if v___x_1494_ == 0 {
                                return v___x_1482_;
                            } else {
                                v___x_1495_ = 0;
                                return v___x_1495_;
                            }
                        }
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1497_) == 0 {
                    v___x_1498_ = 0;
                    return v___x_1498_;
                } else {
                    v_val_1499_ = crate::leanh::lean_ctor_get(v___y_1497_, 0);
                    crate::leanh::lean_inc(v_val_1499_);
                    crate::leanh::lean_dec_ref_known(v___y_1497_, 1);
                    v_val_1479_ = v_val_1499_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(
    mut v_dir_1523_: *mut crate::leanh::LeanObject,
    mut v_message_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1525_: u8 = 0;
    let mut v_res_1526_: u8 = 0;
    let mut v_r_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1525_ = (crate::leanh::lean_unbox(v_dir_1523_) as u8);
    v_res_1526_ =
        l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_1525_, v_message_1524_);
    crate::leanh::lean_dec(v_message_1524_);
    v_r_1527_ = crate::leanh::lean_box((v_res_1526_) as usize);
    return v_r_1527_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(
    mut v_x_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_1528_);
    return v___x_1529_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__1(
    mut v_x_1530_: *mut crate::leanh::LeanObject,
    mut v_prec_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_1530_);
    return v___x_1532_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(
    mut v_x_1533_: *mut crate::leanh::LeanObject,
    mut v_prec_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_1533_, v_prec_1534_);
    crate::leanh::lean_dec(v_prec_1534_);
    return v_res_1535_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(
    mut v_x_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__3(
    mut v_x_1538_: *mut crate::leanh::LeanObject,
    mut v_prec_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_1538_);
    return v___x_1540_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(
    mut v_x_1541_: *mut crate::leanh::LeanObject,
    mut v_prec_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_1541_, v_prec_1542_);
    crate::leanh::lean_dec(v_prec_1542_);
    return v_res_1543_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead(
    mut v_dir_1546_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_dir_1546_ == 0 {
        let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1547_ = l_Std_Http_Protocol_H1_instReprHead___closed__0;
        return v___x_1547_;
    } else {
        let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1548_ = l_Std_Http_Protocol_H1_instReprHead___closed__1;
        return v___x_1548_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprHead___boxed(
    mut v_dir_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_1550_: u8 = 0;
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_1550_ = (crate::leanh::lean_unbox(v_dir_1549_) as u8);
    v_res_1551_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_1550_);
    return v_res_1551_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(
    mut v_x_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1553_ = lean_string_from_utf8_unchecked(v_x_1552_);
    return v___x_1553_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(
    mut v_x_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1555_ = crate::leanh::lean_ctor_get(v_x_1554_, 0);
    crate::leanh::lean_inc(v_fst_1555_);
    v_snd_1556_ = crate::leanh::lean_ctor_get(v_x_1554_, 1);
    crate::leanh::lean_inc(v_snd_1556_);
    crate::leanh::lean_dec_ref(v_x_1554_);
    v___x_1557_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1555_, v_snd_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(
    mut v___x_1558_: *mut crate::leanh::LeanObject,
    mut v___x_1559_: *mut crate::leanh::LeanObject,
    mut v___x_1560_: *mut crate::leanh::LeanObject,
    mut v_name_1561_: *mut crate::leanh::LeanObject,
    mut v___x_1562_: *mut crate::leanh::LeanObject,
    mut v___x_1563_: u32,
    mut v___x_1564_: *mut crate::leanh::LeanObject,
    mut v_it_1565_: *mut crate::leanh::LeanObject,
    mut v_acc_1566_: *mut crate::leanh::LeanObject,
    mut v_hP_1567_: *mut crate::leanh::LeanObject,
    mut v_recur_1568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_it_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u32 = 0;
    let mut v___x_1592_: u32 = 0;
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u32 = 0;
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u32 = 0;
    let mut v___x_1599_: u32 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: u32 = 0;
    let mut v___x_1608_: u8 = 0;
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_1565_) == 0 {
                    v_currPos_1601_ = crate::leanh::lean_ctor_get(v_it_1565_, 0);
                    v_searcher_1602_ = crate::leanh::lean_ctor_get(v_it_1565_, 1);
                    v_isSharedCheck_1624_ = (!crate::leanh::lean_is_exclusive(v_it_1565_)) as u8;
                    if v_isSharedCheck_1624_ == 0 {
                        v___x_1604_ = v_it_1565_;
                        v_isShared_1605_ = v_isSharedCheck_1624_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1602_);
                        crate::leanh::lean_inc(v_currPos_1601_);
                        crate::leanh::lean_dec(v_it_1565_);
                        v___x_1604_ = crate::leanh::lean_box(0);
                        v_isShared_1605_ = v_isSharedCheck_1624_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recur_1568_);
                    crate::leanh::lean_dec(v___x_1562_);
                    return v_acc_1566_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_acc_1566_) == 0 {
                    v___x_1572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1572_, 0, v_out_1571_);
                    v___x_1573_ = crate::leanh::lean_apply_4(
                        v_recur_1568_,
                        v_it_1570_,
                        v___x_1572_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1573_;
                } else {
                    v_val_1574_ = crate::leanh::lean_ctor_get(v_acc_1566_, 0);
                    v_isSharedCheck_1585_ = (!crate::leanh::lean_is_exclusive(v_acc_1566_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v___x_1576_ = v_acc_1566_;
                        v_isShared_1577_ = v_isSharedCheck_1585_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1574_);
                        crate::leanh::lean_dec(v_acc_1566_);
                        v___x_1576_ = crate::leanh::lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1585_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1578_ = lean_string_utf8_extract(v___x_1558_, v___x_1559_, v___x_1560_);
                v___x_1579_ = lean_string_append(v_val_1574_, v___x_1578_);
                crate::leanh::lean_dec_ref(v___x_1578_);
                v___x_1580_ = lean_string_append(v___x_1579_, v_out_1571_);
                crate::leanh::lean_dec_ref(v_out_1571_);
                if v_isShared_1577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1576_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1580_);
                    v___x_1582_ = v_reuseFailAlloc_1584_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1583_ = crate::leanh::lean_apply_4(
                    v_recur_1568_,
                    v_it_1570_,
                    v___x_1582_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1583_;
            }
            4 => {
                v___x_1590_ = lean_string_utf8_extract(
                    v_name_1561_,
                    v_startInclusive_1588_,
                    v_endExclusive_1589_,
                );
                crate::leanh::lean_dec(v_endExclusive_1589_);
                crate::leanh::lean_dec(v_startInclusive_1588_);
                v___x_1591_ = lean_string_utf8_get(v___x_1590_, v___x_1559_);
                v___x_1592_ = 97;
                v___x_1593_ = lean_uint32_dec_le(v___x_1592_, v___x_1591_);
                if v___x_1593_ == 0 {
                    v___x_1594_ = lean_string_utf8_set(v___x_1590_, v___x_1559_, v___x_1591_);
                    v_it_1570_ = v_it_1587_;
                    v_out_1571_ = v___x_1594_;
                    state = 1;
                    continue;
                } else {
                    v___x_1595_ = 122;
                    v___x_1596_ = lean_uint32_dec_le(v___x_1591_, v___x_1595_);
                    if v___x_1596_ == 0 {
                        v___x_1597_ = lean_string_utf8_set(v___x_1590_, v___x_1559_, v___x_1591_);
                        v_it_1570_ = v_it_1587_;
                        v_out_1571_ = v___x_1597_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1598_ = 4294967264;
                        v___x_1599_ = lean_uint32_add(v___x_1591_, v___x_1598_);
                        v___x_1600_ = lean_string_utf8_set(v___x_1590_, v___x_1559_, v___x_1599_);
                        v_it_1570_ = v_it_1587_;
                        v_out_1571_ = v___x_1600_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1606_ = lean_nat_dec_eq(v_searcher_1602_, v___x_1562_);
                if v___x_1606_ == 0 {
                    crate::leanh::lean_dec(v___x_1562_);
                    v___x_1607_ = lean_string_utf8_get_fast(v_name_1561_, v_searcher_1602_);
                    v___x_1608_ = lean_uint32_dec_eq(v___x_1607_, v___x_1563_);
                    if v___x_1608_ == 0 {
                        v___x_1609_ = lean_string_utf8_next_fast(v_name_1561_, v_searcher_1602_);
                        crate::leanh::lean_dec(v_searcher_1602_);
                        if v_isShared_1605_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1604_, 1, v___x_1609_);
                            v___x_1611_ = v___x_1604_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1613_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_currPos_1601_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1609_);
                            v___x_1611_ = v_reuseFailAlloc_1613_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1614_ = lean_string_utf8_next_fast(v_name_1561_, v_searcher_1602_);
                        v___x_1615_ = lean_nat_sub(v___x_1614_, v_searcher_1602_);
                        v___x_1616_ = lean_nat_add(v_searcher_1602_, v___x_1615_);
                        crate::leanh::lean_dec(v___x_1615_);
                        v_slice_1617_ = l_String_Slice_subslice_x21(
                            v___x_1564_,
                            v_currPos_1601_,
                            v_searcher_1602_,
                        );
                        crate::leanh::lean_inc(v___x_1616_);
                        if v_isShared_1605_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1604_, 1, v___x_1616_);
                            crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1616_);
                            v_nextIt_1619_ = v___x_1604_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1622_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1616_);
                            v_nextIt_1619_ = v_reuseFailAlloc_1622_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1604_);
                    crate::leanh::lean_dec(v_searcher_1602_);
                    v___x_1623_ = crate::leanh::lean_box(1);
                    v_it_1587_ = v___x_1623_;
                    v_startInclusive_1588_ = v_currPos_1601_;
                    v_endExclusive_1589_ = v___x_1562_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1612_ = crate::leanh::lean_apply_4(
                    v_recur_1568_,
                    v___x_1611_,
                    v_acc_1566_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1612_;
            }
            7 => {
                v_startInclusive_1620_ = crate::leanh::lean_ctor_get(v_slice_1617_, 0);
                crate::leanh::lean_inc(v_startInclusive_1620_);
                v_endExclusive_1621_ = crate::leanh::lean_ctor_get(v_slice_1617_, 1);
                crate::leanh::lean_inc(v_endExclusive_1621_);
                crate::leanh::lean_dec_ref(v_slice_1617_);
                v_it_1587_ = v_nextIt_1619_;
                v_startInclusive_1588_ = v_startInclusive_1620_;
                v_endExclusive_1589_ = v_endExclusive_1621_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(
    mut v___x_1625_: *mut crate::leanh::LeanObject,
    mut v___x_1626_: *mut crate::leanh::LeanObject,
    mut v___x_1627_: *mut crate::leanh::LeanObject,
    mut v_name_1628_: *mut crate::leanh::LeanObject,
    mut v___x_1629_: *mut crate::leanh::LeanObject,
    mut v___x_1630_: *mut crate::leanh::LeanObject,
    mut v___x_1631_: *mut crate::leanh::LeanObject,
    mut v_it_1632_: *mut crate::leanh::LeanObject,
    mut v_acc_1633_: *mut crate::leanh::LeanObject,
    mut v_hP_1634_: *mut crate::leanh::LeanObject,
    mut v_recur_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2817__boxed_1636_: u32 = 0;
    let mut v_res_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2817__boxed_1636_ = crate::leanh::lean_unbox_uint32(v___x_1630_);
    crate::leanh::lean_dec(v___x_1630_);
    v_res_1637_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(
        v___x_1625_,
        v___x_1626_,
        v___x_1627_,
        v_name_1628_,
        v___x_1629_,
        v___x_2817__boxed_1636_,
        v___x_1631_,
        v_it_1632_,
        v_acc_1633_,
        v_hP_1634_,
        v_recur_1635_,
    );
    crate::leanh::lean_dec_ref(v___x_1631_);
    crate::leanh::lean_dec_ref(v_name_1628_);
    crate::leanh::lean_dec(v___x_1627_);
    crate::leanh::lean_dec(v___x_1626_);
    crate::leanh::lean_dec_ref(v___x_1625_);
    return v_res_1637_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3;
    v___x_1643_ = lean_string_utf8_byte_size(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: u32 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = 45;
    v___x_1646_ = crate::leanh::lean_box_uint32(v___x_1645_);
    return v___x_1646_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(
    mut v_buf_1647_: *mut crate::leanh::LeanObject,
    mut v_name_1648_: *mut crate::leanh::LeanObject,
    mut v_value_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v___f_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1670_ =
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2;
                v___x_1671_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1672_ = lean_string_utf8_byte_size(v_name_1648_);
                crate::leanh::lean_inc_ref(v_name_1648_);
                v___x_1673_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1673_, 0, v_name_1648_);
                crate::leanh::lean_ctor_set(v___x_1673_, 1, v___x_1671_);
                crate::leanh::lean_ctor_set(v___x_1673_, 2, v___x_1672_);
                crate::leanh::lean_inc_ref(v___x_1673_);
                v_it_1674_ = l_String_Slice_splitToSubslice___redArg(v___x_1673_, v___f_1670_);
                v___x_1675_ =
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3;
                v___x_1676_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4,
                );
                v___x_1677_ =
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1;
                v___f_1678_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_1678_, 0, v___x_1675_);
                crate::leanh::lean_closure_set(v___f_1678_, 1, v___x_1671_);
                crate::leanh::lean_closure_set(v___f_1678_, 2, v___x_1676_);
                crate::leanh::lean_closure_set(v___f_1678_, 3, v_name_1648_);
                crate::leanh::lean_closure_set(v___f_1678_, 4, v___x_1672_);
                crate::leanh::lean_closure_set(v___f_1678_, 5, v___x_1677_);
                crate::leanh::lean_closure_set(v___f_1678_, 6, v___x_1673_);
                v___x_1679_ = crate::leanh::lean_box(0);
                v___x_1680_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1678_,
                    v_it_1674_,
                    v___x_1679_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1680_) == 0 {
                    v___x_1681_ =
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                    v___y_1651_ = v___x_1681_;
                    state = 1;
                    continue;
                } else {
                    v_val_1682_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                    crate::leanh::lean_inc(v_val_1682_);
                    crate::leanh::lean_dec_ref_known(v___x_1680_, 1);
                    v___y_1651_ = v_val_1682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_1652_ = crate::leanh::lean_ctor_get(v_buf_1647_, 0);
                v_size_1653_ = crate::leanh::lean_ctor_get(v_buf_1647_, 1);
                v_isSharedCheck_1669_ = (!crate::leanh::lean_is_exclusive(v_buf_1647_)) as u8;
                if v_isSharedCheck_1669_ == 0 {
                    v___x_1655_ = v_buf_1647_;
                    v_isShared_1656_ = v_isSharedCheck_1669_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_1653_);
                    crate::leanh::lean_inc(v_data_1652_);
                    crate::leanh::lean_dec(v_buf_1647_);
                    v___x_1655_ = crate::leanh::lean_box(0);
                    v_isShared_1656_ = v_isSharedCheck_1669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1657_ =
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0;
                v___x_1658_ = lean_string_append(v___y_1651_, v___x_1657_);
                v___x_1659_ = lean_string_append(v___x_1658_, v_value_1649_);
                v___x_1660_ =
                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1;
                v___x_1661_ = lean_string_append(v___x_1659_, v___x_1660_);
                v___x_1662_ = lean_string_to_utf8(v___x_1661_);
                crate::leanh::lean_dec_ref(v___x_1661_);
                crate::leanh::lean_inc_ref(v___x_1662_);
                v___x_1663_ = lean_array_push(v_data_1652_, v___x_1662_);
                v___x_1664_ = lean_byte_array_size(v___x_1662_);
                crate::leanh::lean_dec_ref(v___x_1662_);
                v___x_1665_ = lean_nat_add(v_size_1653_, v___x_1664_);
                crate::leanh::lean_dec(v_size_1653_);
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1665_);
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1663_);
                    v___x_1667_ = v___x_1655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed(
    mut v_buf_1683_: *mut crate::leanh::LeanObject,
    mut v_name_1684_: *mut crate::leanh::LeanObject,
    mut v_value_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(
        v_buf_1683_,
        v_name_1684_,
        v_value_1685_,
    );
    crate::leanh::lean_dec_ref(v_value_1685_);
    return v_res_1686_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1;
    v___x_1691_ = lean_string_to_utf8(v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once),
        _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3,
    );
    v___x_1693_ = lean_byte_array_size(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26() -> u8 {
    let mut v___x_1724_: u32 = 0;
    let mut v___x_1725_: u8 = 0;
    v___x_1724_ = 32;
    v___x_1725_ = lean_uint32_to_uint8(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26),
        core::ptr::addr_of_mut!(
            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_once
        ),
        _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26,
    );
    v___x_1727_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
    v___x_1729_ = crate::leanh::lean_box((v___x_1726_) as usize);
    v___x_1730_ = lean_array_push(v___x_1728_, v___x_1729_);
    v___x_1731_ = lean_byte_array_mk(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27),
        core::ptr::addr_of_mut!(
            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once
        ),
        _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27,
    );
    v___x_1733_ = lean_byte_array_size(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(
    mut v_buffer_1777_: *mut crate::leanh::LeanObject,
    mut v_req_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_method_1779_: u8 = 0;
    let mut v_version_1780_: u8 = 0;
    let mut v_uri_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v___y_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1898_: u16 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1955_: usize = 0;
    let mut v___x_1956_: usize = 0;
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1992_: u16 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_2034_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2037_: usize = 0;
    let mut v___x_2038_: usize = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_1779_ = crate::leanh::lean_ctor_get_uint8(
                    v_req_1778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_version_1780_ = crate::leanh::lean_ctor_get_uint8(
                    v_req_1778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_1781_ = crate::leanh::lean_ctor_get(v_req_1778_, 0);
                crate::leanh::lean_inc(v_uri_1781_);
                v_headers_1782_ = crate::leanh::lean_ctor_get(v_req_1778_, 1);
                crate::leanh::lean_inc_ref(v_headers_1782_);
                crate::leanh::lean_dec_ref(v_req_1778_);
                v___f_1783_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0;
                v___f_1784_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1;
                v___f_1785_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2;
                match v_method_1779_ {
                    0 => {
                        v___x_2100_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32;
                        v___y_2020_ = v___x_2100_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_2101_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33;
                        v___y_2020_ = v___x_2101_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_2102_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34;
                        v___y_2020_ = v___x_2102_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_2103_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35;
                        v___y_2020_ = v___x_2103_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_2104_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36;
                        v___y_2020_ = v___x_2104_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_2105_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37;
                        v___y_2020_ = v___x_2105_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_2106_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38;
                        v___y_2020_ = v___x_2106_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_2107_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39;
                        v___y_2020_ = v___x_2107_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_2108_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40;
                        v___y_2020_ = v___x_2108_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_2109_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41;
                        v___y_2020_ = v___x_2109_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_2110_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42;
                        v___y_2020_ = v___x_2110_;
                        state = 16;
                        continue;
                    }
                    11 => {
                        v___x_2111_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43;
                        v___y_2020_ = v___x_2111_;
                        state = 16;
                        continue;
                    }
                    12 => {
                        v___x_2112_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44;
                        v___y_2020_ = v___x_2112_;
                        state = 16;
                        continue;
                    }
                    13 => {
                        v___x_2113_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45;
                        v___y_2020_ = v___x_2113_;
                        state = 16;
                        continue;
                    }
                    14 => {
                        v___x_2114_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46;
                        v___y_2020_ = v___x_2114_;
                        state = 16;
                        continue;
                    }
                    15 => {
                        v___x_2115_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47;
                        v___y_2020_ = v___x_2115_;
                        state = 16;
                        continue;
                    }
                    16 => {
                        v___x_2116_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48;
                        v___y_2020_ = v___x_2116_;
                        state = 16;
                        continue;
                    }
                    17 => {
                        v___x_2117_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49;
                        v___y_2020_ = v___x_2117_;
                        state = 16;
                        continue;
                    }
                    18 => {
                        v___x_2118_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50;
                        v___y_2020_ = v___x_2118_;
                        state = 16;
                        continue;
                    }
                    19 => {
                        v___x_2119_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51;
                        v___y_2020_ = v___x_2119_;
                        state = 16;
                        continue;
                    }
                    20 => {
                        v___x_2120_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52;
                        v___y_2020_ = v___x_2120_;
                        state = 16;
                        continue;
                    }
                    21 => {
                        v___x_2121_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53;
                        v___y_2020_ = v___x_2121_;
                        state = 16;
                        continue;
                    }
                    22 => {
                        v___x_2122_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54;
                        v___y_2020_ = v___x_2122_;
                        state = 16;
                        continue;
                    }
                    23 => {
                        v___x_2123_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55;
                        v___y_2020_ = v___x_2123_;
                        state = 16;
                        continue;
                    }
                    24 => {
                        v___x_2124_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56;
                        v___y_2020_ = v___x_2124_;
                        state = 16;
                        continue;
                    }
                    25 => {
                        v___x_2125_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57;
                        v___y_2020_ = v___x_2125_;
                        state = 16;
                        continue;
                    }
                    26 => {
                        v___x_2126_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58;
                        v___y_2020_ = v___x_2126_;
                        state = 16;
                        continue;
                    }
                    27 => {
                        v___x_2127_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59;
                        v___y_2020_ = v___x_2127_;
                        state = 16;
                        continue;
                    }
                    28 => {
                        v___x_2128_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60;
                        v___y_2020_ = v___x_2128_;
                        state = 16;
                        continue;
                    }
                    29 => {
                        v___x_2129_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61;
                        v___y_2020_ = v___x_2129_;
                        state = 16;
                        continue;
                    }
                    30 => {
                        v___x_2130_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62;
                        v___y_2020_ = v___x_2130_;
                        state = 16;
                        continue;
                    }
                    31 => {
                        v___x_2131_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63;
                        v___y_2020_ = v___x_2131_;
                        state = 16;
                        continue;
                    }
                    32 => {
                        v___x_2132_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64;
                        v___y_2020_ = v___x_2132_;
                        state = 16;
                        continue;
                    }
                    33 => {
                        v___x_2133_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65;
                        v___y_2020_ = v___x_2133_;
                        state = 16;
                        continue;
                    }
                    34 => {
                        v___x_2134_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66;
                        v___y_2020_ = v___x_2134_;
                        state = 16;
                        continue;
                    }
                    35 => {
                        v___x_2135_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67;
                        v___y_2020_ = v___x_2135_;
                        state = 16;
                        continue;
                    }
                    36 => {
                        v___x_2136_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68;
                        v___y_2020_ = v___x_2136_;
                        state = 16;
                        continue;
                    }
                    37 => {
                        v___x_2137_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69;
                        v___y_2020_ = v___x_2137_;
                        state = 16;
                        continue;
                    }
                    38 => {
                        v___x_2138_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70;
                        v___y_2020_ = v___x_2138_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_2139_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71;
                        v___y_2020_ = v___x_2139_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1790_ = lean_string_to_utf8(v___y_1789_);
                crate::leanh::lean_inc_ref(v___x_1790_);
                v___x_1791_ = lean_array_push(v___y_1787_, v___x_1790_);
                v___x_1792_ = lean_byte_array_size(v___x_1790_);
                crate::leanh::lean_dec_ref(v___x_1790_);
                v___x_1793_ = lean_nat_add(v___y_1788_, v___x_1792_);
                crate::leanh::lean_dec(v___y_1788_);
                v___x_1794_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3,
                );
                v___x_1795_ = lean_array_push(v___x_1791_, v___x_1794_);
                v___x_1796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4,
                );
                v___x_1797_ = lean_nat_add(v___x_1793_, v___x_1796_);
                crate::leanh::lean_dec(v___x_1793_);
                v_buffer_1798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_buffer_1798_, 0, v___x_1795_);
                crate::leanh::lean_ctor_set(v_buffer_1798_, 1, v___x_1797_);
                v_buffer_1799_ =
                    l_Std_Http_Headers_fold___redArg(v_headers_1782_, v_buffer_1798_, v___f_1785_);
                crate::leanh::lean_dec_ref(v_headers_1782_);
                v_data_1800_ = crate::leanh::lean_ctor_get(v_buffer_1799_, 0);
                v_size_1801_ = crate::leanh::lean_ctor_get(v_buffer_1799_, 1);
                v_isSharedCheck_1810_ = (!crate::leanh::lean_is_exclusive(v_buffer_1799_)) as u8;
                if v_isSharedCheck_1810_ == 0 {
                    v___x_1803_ = v_buffer_1799_;
                    v_isShared_1804_ = v_isSharedCheck_1810_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_1801_);
                    crate::leanh::lean_inc(v_data_1800_);
                    crate::leanh::lean_dec(v_buffer_1799_);
                    v___x_1803_ = crate::leanh::lean_box(0);
                    v_isShared_1804_ = v_isSharedCheck_1810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1805_ = lean_array_push(v_data_1800_, v___x_1794_);
                v___x_1806_ = lean_nat_add(v_size_1801_, v___x_1796_);
                crate::leanh::lean_dec(v_size_1801_);
                if v_isShared_1804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1803_, 1, v___x_1806_);
                    crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1805_);
                    v___x_1808_ = v___x_1803_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 1, v___x_1806_);
                    v___x_1808_ = v_reuseFailAlloc_1809_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1808_;
            }
            4 => {
                v___x_1817_ = lean_string_to_utf8(v___y_1816_);
                crate::leanh::lean_dec_ref(v___y_1816_);
                crate::leanh::lean_inc_ref(v___x_1817_);
                v___x_1818_ = lean_array_push(v___y_1815_, v___x_1817_);
                v___x_1819_ = lean_byte_array_size(v___x_1817_);
                crate::leanh::lean_dec_ref(v___x_1817_);
                v___x_1820_ = lean_nat_add(v___y_1814_, v___x_1819_);
                crate::leanh::lean_dec(v___y_1814_);
                v___x_1821_ = lean_array_push(v___x_1818_, v___y_1813_);
                v___x_1822_ = lean_nat_add(v___x_1820_, v___y_1812_);
                crate::leanh::lean_dec(v___x_1820_);
                match v_version_1780_ {
                    0 => {
                        v___x_1823_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5;
                        v___y_1787_ = v___x_1821_;
                        v___y_1788_ = v___x_1822_;
                        v___y_1789_ = v___x_1823_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1824_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6;
                        v___y_1787_ = v___x_1821_;
                        v___y_1788_ = v___x_1822_;
                        v___y_1789_ = v___x_1824_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_1825_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7;
                        v___y_1787_ = v___x_1821_;
                        v___y_1788_ = v___x_1822_;
                        v___y_1789_ = v___x_1825_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1826_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8;
                        v___y_1787_ = v___x_1821_;
                        v___y_1788_ = v___x_1822_;
                        v___y_1789_ = v___x_1826_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_1830_) == 0 {
                    v___y_1812_ = v___y_1828_;
                    v___y_1813_ = v___y_1829_;
                    v___y_1814_ = v___y_1831_;
                    v___y_1815_ = v___y_1832_;
                    v___y_1816_ = v___y_1833_;
                    state = 4;
                    continue;
                } else {
                    v_val_1834_ = crate::leanh::lean_ctor_get(v___y_1830_, 0);
                    crate::leanh::lean_inc(v_val_1834_);
                    crate::leanh::lean_dec_ref_known(v___y_1830_, 1);
                    v___x_1835_ = lean_array_get_size(v_val_1834_);
                    v___x_1836_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1837_ = lean_nat_dec_eq(v___x_1835_, v___x_1836_);
                    if v___x_1837_ == 0 {
                        v___x_1838_ = lean_array_to_list(v_val_1834_);
                        v___x_1839_ = crate::leanh::lean_box(0);
                        v_encodedParams_1840_ =
                            l_List_mapTR_loop___redArg(v___f_1784_, v___x_1838_, v___x_1839_);
                        v___x_1841_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9;
                        v___x_1842_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10;
                        v___x_1843_ = l_String_intercalate(v___x_1842_, v_encodedParams_1840_);
                        v___x_1844_ = lean_string_append(v___x_1841_, v___x_1843_);
                        crate::leanh::lean_dec_ref(v___x_1843_);
                        v___x_1845_ = lean_string_append(v___y_1833_, v___x_1844_);
                        crate::leanh::lean_dec_ref(v___x_1844_);
                        v___y_1812_ = v___y_1828_;
                        v___y_1813_ = v___y_1829_;
                        v___y_1814_ = v___y_1831_;
                        v___y_1815_ = v___y_1832_;
                        v___y_1816_ = v___x_1845_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_1834_);
                        v___y_1812_ = v___y_1828_;
                        v___y_1813_ = v___y_1829_;
                        v___y_1814_ = v___y_1831_;
                        v___y_1815_ = v___y_1832_;
                        v___y_1816_ = v___y_1833_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1856_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                v___x_1857_ = lean_string_append(v___y_1852_, v___x_1856_);
                v___x_1858_ = lean_string_append(v___x_1857_, v___y_1854_);
                crate::leanh::lean_dec_ref(v___y_1854_);
                v___x_1859_ = lean_string_append(v___x_1858_, v___y_1851_);
                crate::leanh::lean_dec_ref(v___y_1851_);
                v___x_1860_ = lean_string_append(v___x_1859_, v___y_1849_);
                crate::leanh::lean_dec_ref(v___y_1849_);
                v___x_1861_ = lean_string_append(v___x_1860_, v___y_1855_);
                crate::leanh::lean_dec_ref(v___y_1855_);
                v___y_1812_ = v___y_1847_;
                v___y_1813_ = v___y_1848_;
                v___y_1814_ = v___y_1850_;
                v___y_1815_ = v___y_1853_;
                v___y_1816_ = v___x_1861_;
                state = 4;
                continue;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_1863_) == 0 {
                    v___x_1872_ =
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                    v___y_1847_ = v___y_1864_;
                    v___y_1848_ = v___y_1865_;
                    v___y_1849_ = v___y_1871_;
                    v___y_1850_ = v___y_1867_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1868_;
                    v___y_1853_ = v___y_1870_;
                    v___y_1854_ = v___y_1869_;
                    v___y_1855_ = v___x_1872_;
                    state = 6;
                    continue;
                } else {
                    v_val_1873_ = crate::leanh::lean_ctor_get(v___y_1863_, 0);
                    crate::leanh::lean_inc(v_val_1873_);
                    crate::leanh::lean_dec_ref_known(v___y_1863_, 1);
                    v___x_1874_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12;
                    v___x_1875_ = l_Std_Http_URI_EncodedFragment_encode(v_val_1873_);
                    crate::leanh::lean_dec(v_val_1873_);
                    v___x_1876_ = lean_string_from_utf8_unchecked(v___x_1875_);
                    v___x_1877_ = lean_string_append(v___x_1874_, v___x_1876_);
                    crate::leanh::lean_dec_ref(v___x_1876_);
                    v___y_1847_ = v___y_1864_;
                    v___y_1848_ = v___y_1865_;
                    v___y_1849_ = v___y_1871_;
                    v___y_1850_ = v___y_1867_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1868_;
                    v___y_1853_ = v___y_1870_;
                    v___y_1854_ = v___y_1869_;
                    v___y_1855_ = v___x_1877_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_1886_ = lean_string_append(v___y_1883_, v___y_1880_);
                crate::leanh::lean_dec_ref(v___y_1880_);
                v___x_1887_ = lean_string_append(v___x_1886_, v___y_1885_);
                crate::leanh::lean_dec_ref(v___y_1885_);
                v___y_1812_ = v___y_1879_;
                v___y_1813_ = v___y_1881_;
                v___y_1814_ = v___y_1882_;
                v___y_1815_ = v___y_1884_;
                v___y_1816_ = v___x_1887_;
                state = 4;
                continue;
            }
            9 => match crate::leanh::lean_obj_tag(v_port_1891_) {
                0 => {
                    v___x_1896_ =
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                    v___y_1879_ = v___y_1889_;
                    v___y_1880_ = v___y_1895_;
                    v___y_1881_ = v___y_1890_;
                    v___y_1882_ = v___y_1892_;
                    v___y_1883_ = v___y_1893_;
                    v___y_1884_ = v___y_1894_;
                    v___y_1885_ = v___x_1896_;
                    state = 8;
                    continue;
                }
                1 => {
                    v___x_1897_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                    v___y_1879_ = v___y_1889_;
                    v___y_1880_ = v___y_1895_;
                    v___y_1881_ = v___y_1890_;
                    v___y_1882_ = v___y_1892_;
                    v___y_1883_ = v___y_1893_;
                    v___y_1884_ = v___y_1894_;
                    v___y_1885_ = v___x_1897_;
                    state = 8;
                    continue;
                }
                _ => {
                    v_port_1898_ = crate::leanh::lean_ctor_get_uint16(v_port_1891_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_port_1891_, 0);
                    v___x_1899_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                    v___x_1900_ = lean_uint16_to_nat(v_port_1898_);
                    v___x_1901_ = l_Nat_reprFast(v___x_1900_);
                    v___x_1902_ = lean_string_append(v___x_1899_, v___x_1901_);
                    crate::leanh::lean_dec_ref(v___x_1901_);
                    v___y_1879_ = v___y_1889_;
                    v___y_1880_ = v___y_1895_;
                    v___y_1881_ = v___y_1890_;
                    v___y_1882_ = v___y_1892_;
                    v___y_1883_ = v___y_1893_;
                    v___y_1884_ = v___y_1894_;
                    v___y_1885_ = v___x_1902_;
                    state = 8;
                    continue;
                }
            },
            10 => match crate::leanh::lean_obj_tag(v_host_1906_) {
                0 => {
                    v_name_1911_ = crate::leanh::lean_ctor_get(v_host_1906_, 0);
                    crate::leanh::lean_inc_ref(v_name_1911_);
                    crate::leanh::lean_dec_ref_known(v_host_1906_, 1);
                    v___y_1889_ = v___y_1904_;
                    v___y_1890_ = v___y_1905_;
                    v_port_1891_ = v_port_1907_;
                    v___y_1892_ = v___y_1908_;
                    v___y_1893_ = v___y_1910_;
                    v___y_1894_ = v___y_1909_;
                    v___y_1895_ = v_name_1911_;
                    state = 9;
                    continue;
                }
                1 => {
                    v_ipv4_1912_ = crate::leanh::lean_ctor_get(v_host_1906_, 0);
                    crate::leanh::lean_inc_ref(v_ipv4_1912_);
                    crate::leanh::lean_dec_ref_known(v_host_1906_, 1);
                    v___x_1913_ = lean_uv_ntop_v4(v_ipv4_1912_);
                    crate::leanh::lean_dec_ref(v_ipv4_1912_);
                    v___y_1889_ = v___y_1904_;
                    v___y_1890_ = v___y_1905_;
                    v_port_1891_ = v_port_1907_;
                    v___y_1892_ = v___y_1908_;
                    v___y_1893_ = v___y_1910_;
                    v___y_1894_ = v___y_1909_;
                    v___y_1895_ = v___x_1913_;
                    state = 9;
                    continue;
                }
                _ => {
                    v_ipv6_1914_ = crate::leanh::lean_ctor_get(v_host_1906_, 0);
                    crate::leanh::lean_inc_ref(v_ipv6_1914_);
                    crate::leanh::lean_dec_ref_known(v_host_1906_, 1);
                    v___x_1915_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13;
                    v___x_1916_ = lean_uv_ntop_v6(v_ipv6_1914_);
                    crate::leanh::lean_dec_ref(v_ipv6_1914_);
                    v___x_1917_ = lean_string_append(v___x_1915_, v___x_1916_);
                    crate::leanh::lean_dec_ref(v___x_1916_);
                    v___x_1918_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14;
                    v___x_1919_ = lean_string_append(v___x_1917_, v___x_1918_);
                    v___y_1889_ = v___y_1904_;
                    v___y_1890_ = v___y_1905_;
                    v_port_1891_ = v_port_1907_;
                    v___y_1892_ = v___y_1908_;
                    v___y_1893_ = v___y_1910_;
                    v___y_1894_ = v___y_1909_;
                    v___y_1895_ = v___x_1919_;
                    state = 9;
                    continue;
                }
            },
            11 => {
                v___x_1930_ = lean_array_get_size(v___y_1928_);
                v___x_1931_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1932_ = lean_nat_dec_eq(v___x_1930_, v___x_1931_);
                if v___x_1932_ == 0 {
                    v___x_1933_ = lean_array_to_list(v___y_1928_);
                    v___x_1934_ = crate::leanh::lean_box(0);
                    v_encodedParams_1935_ =
                        l_List_mapTR_loop___redArg(v___f_1784_, v___x_1933_, v___x_1934_);
                    v___x_1936_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9;
                    v___x_1937_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10;
                    v___x_1938_ = l_String_intercalate(v___x_1937_, v_encodedParams_1935_);
                    v___x_1939_ = lean_string_append(v___x_1936_, v___x_1938_);
                    crate::leanh::lean_dec_ref(v___x_1938_);
                    v___y_1863_ = v___y_1922_;
                    v___y_1864_ = v___y_1921_;
                    v___y_1865_ = v___y_1923_;
                    v___y_1866_ = v___y_1929_;
                    v___y_1867_ = v___y_1924_;
                    v___y_1868_ = v___y_1925_;
                    v___y_1869_ = v___y_1927_;
                    v___y_1870_ = v___y_1926_;
                    v___y_1871_ = v___x_1939_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1928_);
                    v___x_1940_ =
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                    v___y_1863_ = v___y_1922_;
                    v___y_1864_ = v___y_1921_;
                    v___y_1865_ = v___y_1923_;
                    v___y_1866_ = v___y_1929_;
                    v___y_1867_ = v___y_1924_;
                    v___y_1868_ = v___y_1925_;
                    v___y_1869_ = v___y_1927_;
                    v___y_1870_ = v___y_1926_;
                    v___y_1871_ = v___x_1940_;
                    state = 7;
                    continue;
                }
            }
            12 => {
                v_segments_1951_ = crate::leanh::lean_ctor_get(v___y_1945_, 0);
                crate::leanh::lean_inc_ref(v_segments_1951_);
                v_absolute_1952_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v___y_1945_);
                v___x_1953_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15;
                v___x_1954_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25;
                v_sz_1955_ = lean_array_size(v_segments_1951_);
                v___x_1956_ = 0usize;
                v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1954_,
                    v___f_1783_,
                    v_sz_1955_,
                    v___x_1956_,
                    v_segments_1951_,
                );
                v___x_1958_ = lean_array_to_list(v___x_1957_);
                v_result_1959_ = l_String_intercalate(v___x_1953_, v___x_1958_);
                if v_absolute_1952_ == 0 {
                    v___y_1921_ = v___y_1943_;
                    v___y_1922_ = v___y_1942_;
                    v___y_1923_ = v___y_1944_;
                    v___y_1924_ = v___y_1946_;
                    v___y_1925_ = v___y_1947_;
                    v___y_1926_ = v___y_1948_;
                    v___y_1927_ = v___y_1950_;
                    v___y_1928_ = v___y_1949_;
                    v___y_1929_ = v_result_1959_;
                    state = 11;
                    continue;
                } else {
                    v___x_1960_ = lean_string_append(v___x_1953_, v_result_1959_);
                    crate::leanh::lean_dec_ref(v_result_1959_);
                    v___y_1921_ = v___y_1943_;
                    v___y_1922_ = v___y_1942_;
                    v___y_1923_ = v___y_1944_;
                    v___y_1924_ = v___y_1946_;
                    v___y_1925_ = v___y_1947_;
                    v___y_1926_ = v___y_1948_;
                    v___y_1927_ = v___y_1950_;
                    v___y_1928_ = v___y_1949_;
                    v___y_1929_ = v___x_1960_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_1974_ = lean_string_append(v___y_1971_, v___y_1966_);
                crate::leanh::lean_dec_ref(v___y_1966_);
                v___x_1975_ = lean_string_append(v___x_1974_, v___y_1973_);
                crate::leanh::lean_dec_ref(v___y_1973_);
                crate::leanh::lean_inc_ref(v___y_1970_);
                v___x_1976_ = lean_string_append(v___y_1970_, v___x_1975_);
                crate::leanh::lean_dec_ref(v___x_1975_);
                v___y_1942_ = v___y_1963_;
                v___y_1943_ = v___y_1962_;
                v___y_1944_ = v___y_1964_;
                v___y_1945_ = v___y_1965_;
                v___y_1946_ = v___y_1967_;
                v___y_1947_ = v___y_1968_;
                v___y_1948_ = v___y_1969_;
                v___y_1949_ = v___y_1972_;
                v___y_1950_ = v___x_1976_;
                state = 12;
                continue;
            }
            14 => match crate::leanh::lean_obj_tag(v_port_1978_) {
                0 => {
                    v___x_1990_ =
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                    v___y_1962_ = v___y_1980_;
                    v___y_1963_ = v___y_1979_;
                    v___y_1964_ = v___y_1981_;
                    v___y_1965_ = v___y_1982_;
                    v___y_1966_ = v___y_1989_;
                    v___y_1967_ = v___y_1983_;
                    v___y_1968_ = v___y_1984_;
                    v___y_1969_ = v___y_1986_;
                    v___y_1970_ = v___y_1985_;
                    v___y_1971_ = v___y_1987_;
                    v___y_1972_ = v___y_1988_;
                    v___y_1973_ = v___x_1990_;
                    state = 13;
                    continue;
                }
                1 => {
                    v___x_1991_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                    v___y_1962_ = v___y_1980_;
                    v___y_1963_ = v___y_1979_;
                    v___y_1964_ = v___y_1981_;
                    v___y_1965_ = v___y_1982_;
                    v___y_1966_ = v___y_1989_;
                    v___y_1967_ = v___y_1983_;
                    v___y_1968_ = v___y_1984_;
                    v___y_1969_ = v___y_1986_;
                    v___y_1970_ = v___y_1985_;
                    v___y_1971_ = v___y_1987_;
                    v___y_1972_ = v___y_1988_;
                    v___y_1973_ = v___x_1991_;
                    state = 13;
                    continue;
                }
                _ => {
                    v_port_1992_ = crate::leanh::lean_ctor_get_uint16(v_port_1978_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_port_1978_, 0);
                    v___x_1993_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                    v___x_1994_ = lean_uint16_to_nat(v_port_1992_);
                    v___x_1995_ = l_Nat_reprFast(v___x_1994_);
                    v___x_1996_ = lean_string_append(v___x_1993_, v___x_1995_);
                    crate::leanh::lean_dec_ref(v___x_1995_);
                    v___y_1962_ = v___y_1980_;
                    v___y_1963_ = v___y_1979_;
                    v___y_1964_ = v___y_1981_;
                    v___y_1965_ = v___y_1982_;
                    v___y_1966_ = v___y_1989_;
                    v___y_1967_ = v___y_1983_;
                    v___y_1968_ = v___y_1984_;
                    v___y_1969_ = v___y_1986_;
                    v___y_1970_ = v___y_1985_;
                    v___y_1971_ = v___y_1987_;
                    v___y_1972_ = v___y_1988_;
                    v___y_1973_ = v___x_1996_;
                    state = 13;
                    continue;
                }
            },
            15 => match crate::leanh::lean_obj_tag(v_host_1998_) {
                0 => {
                    v_name_2010_ = crate::leanh::lean_ctor_get(v_host_1998_, 0);
                    crate::leanh::lean_inc_ref(v_name_2010_);
                    crate::leanh::lean_dec_ref_known(v_host_1998_, 1);
                    v_port_1978_ = v_port_1999_;
                    v___y_1979_ = v___y_2001_;
                    v___y_1980_ = v___y_2000_;
                    v___y_1981_ = v___y_2002_;
                    v___y_1982_ = v___y_2003_;
                    v___y_1983_ = v___y_2004_;
                    v___y_1984_ = v___y_2005_;
                    v___y_1985_ = v___y_2007_;
                    v___y_1986_ = v___y_2006_;
                    v___y_1987_ = v___y_2009_;
                    v___y_1988_ = v___y_2008_;
                    v___y_1989_ = v_name_2010_;
                    state = 14;
                    continue;
                }
                1 => {
                    v_ipv4_2011_ = crate::leanh::lean_ctor_get(v_host_1998_, 0);
                    crate::leanh::lean_inc_ref(v_ipv4_2011_);
                    crate::leanh::lean_dec_ref_known(v_host_1998_, 1);
                    v___x_2012_ = lean_uv_ntop_v4(v_ipv4_2011_);
                    crate::leanh::lean_dec_ref(v_ipv4_2011_);
                    v_port_1978_ = v_port_1999_;
                    v___y_1979_ = v___y_2001_;
                    v___y_1980_ = v___y_2000_;
                    v___y_1981_ = v___y_2002_;
                    v___y_1982_ = v___y_2003_;
                    v___y_1983_ = v___y_2004_;
                    v___y_1984_ = v___y_2005_;
                    v___y_1985_ = v___y_2007_;
                    v___y_1986_ = v___y_2006_;
                    v___y_1987_ = v___y_2009_;
                    v___y_1988_ = v___y_2008_;
                    v___y_1989_ = v___x_2012_;
                    state = 14;
                    continue;
                }
                _ => {
                    v_ipv6_2013_ = crate::leanh::lean_ctor_get(v_host_1998_, 0);
                    crate::leanh::lean_inc_ref(v_ipv6_2013_);
                    crate::leanh::lean_dec_ref_known(v_host_1998_, 1);
                    v___x_2014_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13;
                    v___x_2015_ = lean_uv_ntop_v6(v_ipv6_2013_);
                    crate::leanh::lean_dec_ref(v_ipv6_2013_);
                    v___x_2016_ = lean_string_append(v___x_2014_, v___x_2015_);
                    crate::leanh::lean_dec_ref(v___x_2015_);
                    v___x_2017_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14;
                    v___x_2018_ = lean_string_append(v___x_2016_, v___x_2017_);
                    v_port_1978_ = v_port_1999_;
                    v___y_1979_ = v___y_2001_;
                    v___y_1980_ = v___y_2000_;
                    v___y_1981_ = v___y_2002_;
                    v___y_1982_ = v___y_2003_;
                    v___y_1983_ = v___y_2004_;
                    v___y_1984_ = v___y_2005_;
                    v___y_1985_ = v___y_2007_;
                    v___y_1986_ = v___y_2006_;
                    v___y_1987_ = v___y_2009_;
                    v___y_1988_ = v___y_2008_;
                    v___y_1989_ = v___x_2018_;
                    state = 14;
                    continue;
                }
            },
            16 => {
                v_data_2021_ = crate::leanh::lean_ctor_get(v_buffer_1777_, 0);
                crate::leanh::lean_inc_ref(v_data_2021_);
                v_size_2022_ = crate::leanh::lean_ctor_get(v_buffer_1777_, 1);
                crate::leanh::lean_inc(v_size_2022_);
                crate::leanh::lean_dec_ref(v_buffer_1777_);
                v___x_2023_ = lean_string_to_utf8(v___y_2020_);
                crate::leanh::lean_inc_ref(v___x_2023_);
                v___x_2024_ = lean_array_push(v_data_2021_, v___x_2023_);
                v___x_2025_ = lean_byte_array_size(v___x_2023_);
                crate::leanh::lean_dec_ref(v___x_2023_);
                v___x_2026_ = lean_nat_add(v_size_2022_, v___x_2025_);
                crate::leanh::lean_dec(v_size_2022_);
                v___x_2027_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27,
                );
                v___x_2028_ = lean_array_push(v___x_2024_, v___x_2027_);
                v___x_2029_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28,
                );
                v___x_2030_ = lean_nat_add(v___x_2026_, v___x_2029_);
                crate::leanh::lean_dec(v___x_2026_);
                match crate::leanh::lean_obj_tag(v_uri_1781_) {
                    0 => {
                        v_path_2031_ = crate::leanh::lean_ctor_get(v_uri_1781_, 0);
                        crate::leanh::lean_inc_ref(v_path_2031_);
                        v_query_2032_ = crate::leanh::lean_ctor_get(v_uri_1781_, 1);
                        crate::leanh::lean_inc(v_query_2032_);
                        crate::leanh::lean_dec_ref_known(v_uri_1781_, 2);
                        v_segments_2033_ = crate::leanh::lean_ctor_get(v_path_2031_, 0);
                        crate::leanh::lean_inc_ref(v_segments_2033_);
                        v_absolute_2034_ = crate::leanh::lean_ctor_get_uint8(
                            v_path_2031_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        crate::leanh::lean_dec_ref(v_path_2031_);
                        v___x_2035_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15;
                        v___x_2036_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25;
                        v_sz_2037_ = lean_array_size(v_segments_2033_);
                        v___x_2038_ = 0usize;
                        v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2036_,
                            v___f_1783_,
                            v_sz_2037_,
                            v___x_2038_,
                            v_segments_2033_,
                        );
                        v___x_2040_ = lean_array_to_list(v___x_2039_);
                        v_result_2041_ = l_String_intercalate(v___x_2035_, v___x_2040_);
                        if v_absolute_2034_ == 0 {
                            v___y_1828_ = v___x_2029_;
                            v___y_1829_ = v___x_2027_;
                            v___y_1830_ = v_query_2032_;
                            v___y_1831_ = v___x_2030_;
                            v___y_1832_ = v___x_2028_;
                            v___y_1833_ = v_result_2041_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2042_ = lean_string_append(v___x_2035_, v_result_2041_);
                            crate::leanh::lean_dec_ref(v_result_2041_);
                            v___y_1828_ = v___x_2029_;
                            v___y_1829_ = v___x_2027_;
                            v___y_1830_ = v_query_2032_;
                            v___y_1831_ = v___x_2030_;
                            v___y_1832_ = v___x_2028_;
                            v___y_1833_ = v___x_2042_;
                            state = 5;
                            continue;
                        }
                    }
                    1 => {
                        v_uri_2043_ = crate::leanh::lean_ctor_get(v_uri_1781_, 0);
                        crate::leanh::lean_inc_ref(v_uri_2043_);
                        crate::leanh::lean_dec_ref_known(v_uri_1781_, 1);
                        v_authority_2044_ = crate::leanh::lean_ctor_get(v_uri_2043_, 1);
                        if crate::leanh::lean_obj_tag(v_authority_2044_) == 0 {
                            v_scheme_2045_ = crate::leanh::lean_ctor_get(v_uri_2043_, 0);
                            crate::leanh::lean_inc_ref(v_scheme_2045_);
                            v_path_2046_ = crate::leanh::lean_ctor_get(v_uri_2043_, 2);
                            crate::leanh::lean_inc_ref(v_path_2046_);
                            v_query_2047_ = crate::leanh::lean_ctor_get(v_uri_2043_, 3);
                            crate::leanh::lean_inc_ref(v_query_2047_);
                            v_fragment_2048_ = crate::leanh::lean_ctor_get(v_uri_2043_, 4);
                            crate::leanh::lean_inc(v_fragment_2048_);
                            crate::leanh::lean_dec_ref(v_uri_2043_);
                            v___x_2049_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                            v___y_1942_ = v_fragment_2048_;
                            v___y_1943_ = v___x_2029_;
                            v___y_1944_ = v___x_2027_;
                            v___y_1945_ = v_path_2046_;
                            v___y_1946_ = v___x_2030_;
                            v___y_1947_ = v_scheme_2045_;
                            v___y_1948_ = v___x_2028_;
                            v___y_1949_ = v_query_2047_;
                            v___y_1950_ = v___x_2049_;
                            state = 12;
                            continue;
                        } else {
                            v_val_2050_ = crate::leanh::lean_ctor_get(v_authority_2044_, 0);
                            crate::leanh::lean_inc(v_val_2050_);
                            v_scheme_2051_ = crate::leanh::lean_ctor_get(v_uri_2043_, 0);
                            crate::leanh::lean_inc_ref(v_scheme_2051_);
                            v_path_2052_ = crate::leanh::lean_ctor_get(v_uri_2043_, 2);
                            crate::leanh::lean_inc_ref(v_path_2052_);
                            v_query_2053_ = crate::leanh::lean_ctor_get(v_uri_2043_, 3);
                            crate::leanh::lean_inc_ref(v_query_2053_);
                            v_fragment_2054_ = crate::leanh::lean_ctor_get(v_uri_2043_, 4);
                            crate::leanh::lean_inc(v_fragment_2054_);
                            crate::leanh::lean_dec_ref(v_uri_2043_);
                            v_userInfo_2055_ = crate::leanh::lean_ctor_get(v_val_2050_, 0);
                            crate::leanh::lean_inc(v_userInfo_2055_);
                            v_host_2056_ = crate::leanh::lean_ctor_get(v_val_2050_, 1);
                            crate::leanh::lean_inc_ref(v_host_2056_);
                            v_port_2057_ = crate::leanh::lean_ctor_get(v_val_2050_, 2);
                            crate::leanh::lean_inc(v_port_2057_);
                            crate::leanh::lean_dec(v_val_2050_);
                            v___x_2058_ =
                                l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29;
                            if crate::leanh::lean_obj_tag(v_userInfo_2055_) == 0 {
                                v___x_2059_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                                v_host_1998_ = v_host_2056_;
                                v_port_1999_ = v_port_2057_;
                                v___y_2000_ = v___x_2029_;
                                v___y_2001_ = v_fragment_2054_;
                                v___y_2002_ = v___x_2027_;
                                v___y_2003_ = v_path_2052_;
                                v___y_2004_ = v___x_2030_;
                                v___y_2005_ = v_scheme_2051_;
                                v___y_2006_ = v___x_2028_;
                                v___y_2007_ = v___x_2058_;
                                v___y_2008_ = v_query_2053_;
                                v___y_2009_ = v___x_2059_;
                                state = 15;
                                continue;
                            } else {
                                v_val_2060_ = crate::leanh::lean_ctor_get(v_userInfo_2055_, 0);
                                crate::leanh::lean_inc(v_val_2060_);
                                crate::leanh::lean_dec_ref_known(v_userInfo_2055_, 1);
                                v_password_2061_ = crate::leanh::lean_ctor_get(v_val_2060_, 1);
                                if crate::leanh::lean_obj_tag(v_password_2061_) == 0 {
                                    v_username_2062_ = crate::leanh::lean_ctor_get(v_val_2060_, 0);
                                    crate::leanh::lean_inc_ref(v_username_2062_);
                                    crate::leanh::lean_dec(v_val_2060_);
                                    v___x_2063_ = lean_string_from_utf8_unchecked(v_username_2062_);
                                    v___x_2064_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30;
                                    v___x_2065_ = lean_string_append(v___x_2063_, v___x_2064_);
                                    v_host_1998_ = v_host_2056_;
                                    v_port_1999_ = v_port_2057_;
                                    v___y_2000_ = v___x_2029_;
                                    v___y_2001_ = v_fragment_2054_;
                                    v___y_2002_ = v___x_2027_;
                                    v___y_2003_ = v_path_2052_;
                                    v___y_2004_ = v___x_2030_;
                                    v___y_2005_ = v_scheme_2051_;
                                    v___y_2006_ = v___x_2028_;
                                    v___y_2007_ = v___x_2058_;
                                    v___y_2008_ = v_query_2053_;
                                    v___y_2009_ = v___x_2065_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc_ref(v_password_2061_);
                                    v_username_2066_ = crate::leanh::lean_ctor_get(v_val_2060_, 0);
                                    crate::leanh::lean_inc_ref(v_username_2066_);
                                    crate::leanh::lean_dec(v_val_2060_);
                                    v_val_2067_ = crate::leanh::lean_ctor_get(v_password_2061_, 0);
                                    crate::leanh::lean_inc(v_val_2067_);
                                    crate::leanh::lean_dec_ref_known(v_password_2061_, 1);
                                    v___x_2068_ = lean_string_from_utf8_unchecked(v_username_2066_);
                                    v___x_2069_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                                    v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
                                    v___x_2071_ = lean_string_from_utf8_unchecked(v_val_2067_);
                                    v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
                                    crate::leanh::lean_dec_ref(v___x_2071_);
                                    v___x_2073_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30;
                                    v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
                                    v_host_1998_ = v_host_2056_;
                                    v_port_1999_ = v_port_2057_;
                                    v___y_2000_ = v___x_2029_;
                                    v___y_2001_ = v_fragment_2054_;
                                    v___y_2002_ = v___x_2027_;
                                    v___y_2003_ = v_path_2052_;
                                    v___y_2004_ = v___x_2030_;
                                    v___y_2005_ = v_scheme_2051_;
                                    v___y_2006_ = v___x_2028_;
                                    v___y_2007_ = v___x_2058_;
                                    v___y_2008_ = v_query_2053_;
                                    v___y_2009_ = v___x_2074_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    }
                    2 => {
                        v_authority_2075_ = crate::leanh::lean_ctor_get(v_uri_1781_, 0);
                        crate::leanh::lean_inc_ref(v_authority_2075_);
                        crate::leanh::lean_dec_ref_known(v_uri_1781_, 1);
                        v_userInfo_2076_ = crate::leanh::lean_ctor_get(v_authority_2075_, 0);
                        if crate::leanh::lean_obj_tag(v_userInfo_2076_) == 0 {
                            v_host_2077_ = crate::leanh::lean_ctor_get(v_authority_2075_, 1);
                            crate::leanh::lean_inc_ref(v_host_2077_);
                            v_port_2078_ = crate::leanh::lean_ctor_get(v_authority_2075_, 2);
                            crate::leanh::lean_inc(v_port_2078_);
                            crate::leanh::lean_dec_ref(v_authority_2075_);
                            v___x_2079_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5;
                            v___y_1904_ = v___x_2029_;
                            v___y_1905_ = v___x_2027_;
                            v_host_1906_ = v_host_2077_;
                            v_port_1907_ = v_port_2078_;
                            v___y_1908_ = v___x_2030_;
                            v___y_1909_ = v___x_2028_;
                            v___y_1910_ = v___x_2079_;
                            state = 10;
                            continue;
                        } else {
                            v_val_2080_ = crate::leanh::lean_ctor_get(v_userInfo_2076_, 0);
                            crate::leanh::lean_inc(v_val_2080_);
                            v_password_2081_ = crate::leanh::lean_ctor_get(v_val_2080_, 1);
                            if crate::leanh::lean_obj_tag(v_password_2081_) == 0 {
                                v_host_2082_ = crate::leanh::lean_ctor_get(v_authority_2075_, 1);
                                crate::leanh::lean_inc_ref(v_host_2082_);
                                v_port_2083_ = crate::leanh::lean_ctor_get(v_authority_2075_, 2);
                                crate::leanh::lean_inc(v_port_2083_);
                                crate::leanh::lean_dec_ref(v_authority_2075_);
                                v_username_2084_ = crate::leanh::lean_ctor_get(v_val_2080_, 0);
                                crate::leanh::lean_inc_ref(v_username_2084_);
                                crate::leanh::lean_dec(v_val_2080_);
                                v___x_2085_ = lean_string_from_utf8_unchecked(v_username_2084_);
                                v___x_2086_ =
                                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30;
                                v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
                                v___y_1904_ = v___x_2029_;
                                v___y_1905_ = v___x_2027_;
                                v_host_1906_ = v_host_2082_;
                                v_port_1907_ = v_port_2083_;
                                v___y_1908_ = v___x_2030_;
                                v___y_1909_ = v___x_2028_;
                                v___y_1910_ = v___x_2087_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_password_2081_);
                                v_host_2088_ = crate::leanh::lean_ctor_get(v_authority_2075_, 1);
                                crate::leanh::lean_inc_ref(v_host_2088_);
                                v_port_2089_ = crate::leanh::lean_ctor_get(v_authority_2075_, 2);
                                crate::leanh::lean_inc(v_port_2089_);
                                crate::leanh::lean_dec_ref(v_authority_2075_);
                                v_username_2090_ = crate::leanh::lean_ctor_get(v_val_2080_, 0);
                                crate::leanh::lean_inc_ref(v_username_2090_);
                                crate::leanh::lean_dec(v_val_2080_);
                                v_val_2091_ = crate::leanh::lean_ctor_get(v_password_2081_, 0);
                                crate::leanh::lean_inc(v_val_2091_);
                                crate::leanh::lean_dec_ref_known(v_password_2081_, 1);
                                v___x_2092_ = lean_string_from_utf8_unchecked(v_username_2090_);
                                v___x_2093_ =
                                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
                                v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
                                v___x_2095_ = lean_string_from_utf8_unchecked(v_val_2091_);
                                v___x_2096_ = lean_string_append(v___x_2094_, v___x_2095_);
                                crate::leanh::lean_dec_ref(v___x_2095_);
                                v___x_2097_ =
                                    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30;
                                v___x_2098_ = lean_string_append(v___x_2096_, v___x_2097_);
                                v___y_1904_ = v___x_2029_;
                                v___y_1905_ = v___x_2027_;
                                v_host_1906_ = v_host_2088_;
                                v_port_1907_ = v_port_2089_;
                                v___y_1908_ = v___x_2030_;
                                v___y_1909_ = v___x_2028_;
                                v___y_1910_ = v___x_2098_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                    _ => {
                        v___x_2099_ =
                            l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31;
                        v___y_1812_ = v___x_2029_;
                        v___y_1813_ = v___x_2027_;
                        v___y_1814_ = v___x_2030_;
                        v___y_1815_ = v___x_2028_;
                        v___y_1816_ = v___x_2099_;
                        state = 4;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(
    mut v_buffer_2140_: *mut crate::leanh::LeanObject,
    mut v_r_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_status_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2143_: u8 = 0;
    let mut v_headers_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u16 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_status_2142_ = crate::leanh::lean_ctor_get(v_r_2141_, 0);
                v_version_2143_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_headers_2144_ = crate::leanh::lean_ctor_get(v_r_2141_, 1);
                v___f_2145_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2;
                match v_version_2143_ {
                    0 => {
                        v___x_2197_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5;
                        v___y_2147_ = v___x_2197_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2198_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6;
                        v___y_2147_ = v___x_2198_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_2199_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7;
                        v___y_2147_ = v___x_2199_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2200_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8;
                        v___y_2147_ = v___x_2200_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_data_2148_ = crate::leanh::lean_ctor_get(v_buffer_2140_, 0);
                v_size_2149_ = crate::leanh::lean_ctor_get(v_buffer_2140_, 1);
                v_isSharedCheck_2196_ = (!crate::leanh::lean_is_exclusive(v_buffer_2140_)) as u8;
                if v_isSharedCheck_2196_ == 0 {
                    v___x_2151_ = v_buffer_2140_;
                    v_isShared_2152_ = v_isSharedCheck_2196_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_2149_);
                    crate::leanh::lean_inc(v_data_2148_);
                    crate::leanh::lean_dec(v_buffer_2140_);
                    v___x_2151_ = crate::leanh::lean_box(0);
                    v_isShared_2152_ = v_isSharedCheck_2196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2153_ = lean_string_to_utf8(v___y_2147_);
                crate::leanh::lean_inc_ref(v___x_2153_);
                v___x_2154_ = lean_array_push(v_data_2148_, v___x_2153_);
                v___x_2155_ = lean_byte_array_size(v___x_2153_);
                crate::leanh::lean_dec_ref(v___x_2153_);
                v___x_2156_ = lean_nat_add(v_size_2149_, v___x_2155_);
                crate::leanh::lean_dec(v_size_2149_);
                v___x_2157_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2158_ = lean_mk_empty_array_with_capacity(v___x_2157_);
                crate::leanh::lean_dec_ref(v___x_2158_);
                v___x_2159_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27,
                );
                v___x_2160_ = lean_array_push(v___x_2154_, v___x_2159_);
                v___x_2161_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28,
                );
                v___x_2162_ = lean_nat_add(v___x_2156_, v___x_2161_);
                crate::leanh::lean_dec(v___x_2156_);
                v___x_2163_ = l_Std_Http_Status_toCode(v_status_2142_);
                v___x_2164_ = lean_uint16_to_nat(v___x_2163_);
                v___x_2165_ = l_Nat_reprFast(v___x_2164_);
                v___x_2166_ = lean_string_to_utf8(v___x_2165_);
                crate::leanh::lean_dec_ref(v___x_2165_);
                crate::leanh::lean_inc_ref(v___x_2166_);
                v___x_2167_ = lean_array_push(v___x_2160_, v___x_2166_);
                v___x_2168_ = lean_byte_array_size(v___x_2166_);
                crate::leanh::lean_dec_ref(v___x_2166_);
                v___x_2169_ = lean_nat_add(v___x_2162_, v___x_2168_);
                crate::leanh::lean_dec(v___x_2162_);
                v___x_2170_ = lean_array_push(v___x_2167_, v___x_2159_);
                v___x_2171_ = lean_nat_add(v___x_2169_, v___x_2161_);
                crate::leanh::lean_dec(v___x_2169_);
                v___x_2172_ = l_Std_Http_Status_reasonPhrase(v_status_2142_);
                v___x_2173_ = lean_string_to_utf8(v___x_2172_);
                crate::leanh::lean_dec_ref(v___x_2172_);
                crate::leanh::lean_inc_ref(v___x_2173_);
                v___x_2174_ = lean_array_push(v___x_2170_, v___x_2173_);
                v___x_2175_ = lean_byte_array_size(v___x_2173_);
                crate::leanh::lean_dec_ref(v___x_2173_);
                v___x_2176_ = lean_nat_add(v___x_2171_, v___x_2175_);
                crate::leanh::lean_dec(v___x_2171_);
                v___x_2177_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3,
                );
                v___x_2178_ = lean_array_push(v___x_2174_, v___x_2177_);
                v___x_2179_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once
                    ),
                    _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4,
                );
                v___x_2180_ = lean_nat_add(v___x_2176_, v___x_2179_);
                crate::leanh::lean_dec(v___x_2176_);
                if v_isShared_2152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2151_, 1, v___x_2180_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2178_);
                    v_buffer_2182_ = v___x_2151_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2180_);
                    v_buffer_2182_ = v_reuseFailAlloc_2195_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_buffer_2183_ =
                    l_Std_Http_Headers_fold___redArg(v_headers_2144_, v_buffer_2182_, v___f_2145_);
                v_data_2184_ = crate::leanh::lean_ctor_get(v_buffer_2183_, 0);
                v_size_2185_ = crate::leanh::lean_ctor_get(v_buffer_2183_, 1);
                v_isSharedCheck_2194_ = (!crate::leanh::lean_is_exclusive(v_buffer_2183_)) as u8;
                if v_isSharedCheck_2194_ == 0 {
                    v___x_2187_ = v_buffer_2183_;
                    v_isShared_2188_ = v_isSharedCheck_2194_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_2185_);
                    crate::leanh::lean_inc(v_data_2184_);
                    crate::leanh::lean_dec(v_buffer_2183_);
                    v___x_2187_ = crate::leanh::lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2189_ = lean_array_push(v_data_2184_, v___x_2177_);
                v___x_2190_ = lean_nat_add(v_size_2185_, v___x_2179_);
                crate::leanh::lean_dec(v_size_2185_);
                if v_isShared_2188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2187_, 1, v___x_2190_);
                    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2189_);
                    v___x_2192_ = v___x_2187_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2190_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(
    mut v_buffer_2201_: *mut crate::leanh::LeanObject,
    mut v_r_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_2201_, v_r_2202_);
    crate::leanh::lean_dec_ref(v_r_2202_);
    return v_res_2203_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head(
    mut v_dir_2206_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_dir_2206_ == 0 {
        let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2207_ = l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0;
        return v___x_2207_;
    } else {
        let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2208_ = l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1;
        return v___x_2208_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(
    mut v_dir_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2210_: u8 = 0;
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2210_ = (crate::leanh::lean_unbox(v_dir_2209_) as u8);
    v_res_2211_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_2210_);
    return v_res_2211_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Std_Http_Headers_empty;
    v___x_2213_ = crate::leanh::lean_box(3);
    v___x_2214_ = 1;
    v___x_2215_ = 8;
    v___x_2216_ = crate::leanh::lean_alloc_ctor(0, 2, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2213_);
    crate::leanh::lean_ctor_set(v___x_2216_, 1, v___x_2212_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2216_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2215_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2216_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        v___x_2214_,
    );
    return v___x_2216_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Std_Http_Headers_empty;
    v___x_2218_ = 1;
    v___x_2219_ = crate::leanh::lean_box(4);
    v___x_2220_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
    crate::leanh::lean_ctor_set(v___x_2220_, 1, v___x_2217_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2220_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2218_,
    );
    return v___x_2220_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instEmptyCollectionHead(
    mut v_dir_2221_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_dir_2221_ == 0 {
        let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2222_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0),
            core::ptr::addr_of_mut!(
                l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once
            ),
            _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0,
        );
        return v___x_2222_;
    } else {
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2223_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1),
            core::ptr::addr_of_mut!(
                l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once
            ),
            _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1,
        );
        return v___x_2223_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(
    mut v_dir_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2225_: u8 = 0;
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2225_ = (crate::leanh::lean_unbox(v_dir_2224_) as u8);
    v_res_2226_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_2225_);
    return v_res_2226_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Message(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1 =
        _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Message(
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
pub unsafe fn initialize_Std_Http_Protocol_H1_Message(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Message(builtin);
}
