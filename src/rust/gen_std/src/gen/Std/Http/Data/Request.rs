// Lean compiler output
// Module: Std.Http.Data.Request
// Imports: Std.Http.Data.Extensions Std.Http.Data.Method Std.Http.Data.Version Std.Http.Data.Headers Std.Http.Data.URI
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_nat_to_int, lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq,
    lean_string_from_utf8_unchecked, lean_string_hash, lean_string_length, lean_string_to_utf8,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set,
    lean_uint16_to_nat, lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint32_to_uint8, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub, lean_uv_ntop_v4, lean_uv_ntop_v6,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::List::Basic::l_List_mapTR_loop___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_splitToSubslice___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_typeNameImpl;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Http::Data::Extensions::{
    initialize_Std_Http_Data_Extensions, l_Std_Http_Extensions_compareName___boxed,
    l_Std_Http_Extensions_empty, runtime_initialize_Std_Http_Data_Extensions,
};
use crate::r#gen::Std::Http::Data::Headers::Name::{
    l_Std_Http_Header_Name_ofString_x3f, l_Std_Http_Header_Name_ofString_x21,
};
use crate::r#gen::Std::Http::Data::Headers::Value::{
    l_Std_Http_Header_Value_ofString_x3f, l_Std_Http_Header_Value_ofString_x21,
};
use crate::r#gen::Std::Http::Data::Headers::{
    initialize_Std_Http_Data_Headers, l_Std_Http_Headers_empty, l_Std_Http_Headers_fold___redArg,
    l_Std_Http_instReprHeaders_repr___redArg, runtime_initialize_Std_Http_Data_Headers,
};
use crate::r#gen::Std::Http::Data::Method::{
    initialize_Std_Http_Data_Method, l_Std_Http_instReprMethod_repr,
    runtime_initialize_Std_Http_Data_Method,
};
use crate::r#gen::Std::Http::Data::URI::Basic::{
    l_Std_Http_URI_Query_formatQueryParam, l_Std_Http_instInhabitedRequestTarget_default,
    l_Std_Http_instReprRequestTarget_repr,
};
use crate::r#gen::Std::Http::Data::URI::Encoding::l_Std_Http_URI_EncodedFragment_encode;
use crate::r#gen::Std::Http::Data::URI::Parser::l_Std_Http_URI_Parser_parseRequestTarget;
use crate::r#gen::Std::Http::Data::URI::{
    initialize_Std_Http_Data_URI, runtime_initialize_Std_Http_Data_URI,
};
use crate::r#gen::Std::Http::Data::Version::{
    initialize_Std_Http_Data_Version, l_Std_Http_instReprVersion_repr,
    runtime_initialize_Std_Http_Data_Version,
};
use crate::r#gen::Std::Internal::Parsec::ByteArray::l_Std_Internal_Parsec_ByteArray_Parser_run___redArg;
static mut l_Std_Http_Request_instInhabitedHead_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instInhabitedHead_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Request_instInhabitedHead_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Request_instInhabitedHead: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
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
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 114, 105, 0],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 101, 97, 100, 101, 114, 115, 0],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__21_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead_repr___redArg___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instReprHead_repr___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instReprHead___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Request_instReprHead_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Request_instReprHead___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Request_instReprHead: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instReprHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__3___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__3___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__3___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_instToStringHead___lam__3___closed__4_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__3___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__9_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__11_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__12_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__13_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__14_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__15_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__16_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__17_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__18_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__19_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__20_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__21_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__22_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__23_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__24_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__25_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__26_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__27_value:
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
        66, 65, 83, 69, 76, 73, 78, 69, 45, 67, 79, 78, 84, 82, 79, 76, 0,
    ],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__28_value:
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
    m_data: [66, 73, 78, 68, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__29_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__30_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__31_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__31:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__32_value:
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
    m_data: [67, 79, 80, 89, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__32:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__33_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__33:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__34_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__34:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__35_value:
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
    m_data: [72, 69, 65, 68, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__36_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__36:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__37_value:
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
    m_data: [76, 73, 78, 75, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__38_value:
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
    m_data: [76, 79, 67, 75, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__38:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__39_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__39:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__40_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__40:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__41_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__41:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__42_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__42:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__43_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__43:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__43_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__44_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__44:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__44_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__45_value:
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
    m_data: [77, 79, 86, 69, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__45:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__45_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__46_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__46:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__46_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__47_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__47:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__47_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__48_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__48:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__48_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__49_value:
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
    m_data: [80, 79, 83, 84, 0],
};
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__49:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__49_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__50_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__50:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__50_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__51_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__51:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__51_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__52_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__52:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__52_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__53_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__53:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__53_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__54_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__54:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__54_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__55_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__55:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__55_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__56_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__56:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__56_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__57_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__57:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__57_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__58_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__58:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__58_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__59_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__59:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__59_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__60_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__60:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__60_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__61_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__61:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__61_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__62_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__62:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__62_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__63_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__63:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__63_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__64_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__64:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__64_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___lam__6___closed__65_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_instToStringHead___lam__6___closed__65:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___lam__6___closed__65_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instToStringHead___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instToStringHead___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instToStringHead___lam__3 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instToStringHead___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instToStringHead___closed__3_value: leanh::LeanClosureObject<
    5,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instToStringHead___lam__6 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instToStringHead___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Request_instToStringHead: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2: u8 = 0;
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_instEncodeV11Head___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instEncodeV11Head___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_instEncodeV11Head___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instEncodeV11Head___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_instEncodeV11Head___closed__1_value: leanh::LeanClosureObject<
    5,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_instEncodeV11Head___lam__4 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 5,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_instEncodeV11Head___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Request_instToStringHead___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_instEncodeV11Head___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instEncodeV11Head___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Request_instEncodeV11Head: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_instEncodeV11Head___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_new___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_new___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_new___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_new___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Request_new: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___closed__0_value: leanh::LeanCtorObject<9> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 9
                + 0) as u16,
            other: 9,
            tag: 0,
        },
        m_objs: [
            (((13 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((253 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((256 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((128 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Request_Builder_uri_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Request_Builder_uri_x21___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Request_Builder_uri_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___closed__2_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 85, 82, 73, 0,
    ],
};
static mut l_Std_Http_Request_Builder_uri_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___closed__3_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 112, 97, 114, 115, 101, 33, 0,
    ],
};
static mut l_Std_Http_Request_Builder_uri_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_uri_x21___closed__4_value: leanh::LeanStringObject<
    23,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 116, 97, 114,
        103, 101, 116, 0,
    ],
};
static mut l_Std_Http_Request_Builder_uri_x21___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_uri_x21___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_Builder_uri_x21___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_Builder_uri_x21___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_Builder_extension___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Request_Builder_extension___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_extension___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_get___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_get___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_post___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_post___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_put___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_put___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_delete___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_delete___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_patch___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_patch___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_head___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_head___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_options___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_options___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_connect___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_connect___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Request_trace___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_trace___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Http_Request_instInhabitedHead_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Std_Http_Headers_empty;
    v___x_1724_ = leanh::lean_box(3);
    v___x_1725_ = 0;
    v___x_1726_ = 0;
    v___x_1727_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
    leanh::lean_ctor_set(v___x_1727_, 0, v___x_1724_);
    leanh::lean_ctor_set(v___x_1727_, 1, v___x_1723_);
    leanh::lean_ctor_set_uint8(
        v___x_1727_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1726_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1727_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
        v___x_1725_,
    );
    return v___x_1727_;
}
pub unsafe fn _init_l_Std_Http_Request_instInhabitedHead_default() -> *mut leanh::LeanObject
{
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instInhabitedHead_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instInhabitedHead_default___closed__0_once),
        _init_l_Std_Http_Request_instInhabitedHead_default___closed__0,
    );
    return v___x_1728_;
}
pub unsafe fn _init_l_Std_Http_Request_instInhabitedHead() -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = l_Std_Http_Request_instInhabitedHead_default;
    return v___x_1729_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Request_instReprHead_repr_spec__0(
    mut v_a_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = lean_nat_to_int(v_a_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = leanh::lean_unsigned_to_nat(10);
    v___x_1746_ = lean_nat_to_int(v___x_1745_);
    return v___x_1746_;
}
pub unsafe fn _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = leanh::lean_unsigned_to_nat(11);
    v___x_1754_ = lean_nat_to_int(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = leanh::lean_unsigned_to_nat(7);
    v___x_1759_ = lean_nat_to_int(v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__0;
    v___x_1765_ = lean_string_length(v___x_1764_);
    return v___x_1765_;
}
pub unsafe fn _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__19_once),
        _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19,
    );
    v___x_1767_ = lean_nat_to_int(v___x_1766_);
    return v___x_1767_;
}
pub unsafe fn l_Std_Http_Request_instReprHead_repr___redArg(
    mut v_x_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_1773_: u8 = 0;
    let mut v_version_1774_: u8 = 0;
    let mut v_uri_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_method_1773_ = leanh::lean_ctor_get_uint8(
        v_x_1772_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_version_1774_ = leanh::lean_ctor_get_uint8(
        v_x_1772_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
    );
    v_uri_1775_ = leanh::lean_ctor_get(v_x_1772_, 0);
    leanh::lean_inc(v_uri_1775_);
    v_headers_1776_ = leanh::lean_ctor_get(v_x_1772_, 1);
    leanh::lean_inc_ref(v_headers_1776_);
    leanh::lean_dec_ref(v_x_1772_);
    v___x_1777_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__5;
    v___x_1778_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__6;
    v___x_1779_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once),
        _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7,
    );
    v___x_1780_ = leanh::lean_unsigned_to_nat(0);
    v___x_1781_ = l_Std_Http_instReprMethod_repr(v_method_1773_, v___x_1780_);
    v___x_1782_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1779_);
    leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
    v___x_1783_ = 0;
    v___x_1784_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1782_);
    leanh::lean_ctor_set_uint8(
        v___x_1784_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1783_,
    );
    v___x_1785_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1785_, 0, v___x_1778_);
    leanh::lean_ctor_set(v___x_1785_, 1, v___x_1784_);
    v___x_1786_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__9;
    v___x_1787_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1787_, 0, v___x_1785_);
    leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
    v___x_1788_ = leanh::lean_box(1);
    v___x_1789_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1789_, 0, v___x_1787_);
    leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
    v___x_1790_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__11;
    v___x_1791_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1791_, 0, v___x_1789_);
    leanh::lean_ctor_set(v___x_1791_, 1, v___x_1790_);
    v___x_1792_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1792_, 0, v___x_1791_);
    leanh::lean_ctor_set(v___x_1792_, 1, v___x_1777_);
    v___x_1793_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once),
        _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12,
    );
    v___x_1794_ = l_Std_Http_instReprVersion_repr(v_version_1774_, v___x_1780_);
    v___x_1795_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1795_, 0, v___x_1793_);
    leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
    v___x_1796_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1796_, 0, v___x_1795_);
    leanh::lean_ctor_set_uint8(
        v___x_1796_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1783_,
    );
    v___x_1797_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1797_, 0, v___x_1792_);
    leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
    v___x_1798_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1798_, 0, v___x_1797_);
    leanh::lean_ctor_set(v___x_1798_, 1, v___x_1786_);
    v___x_1799_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1799_, 0, v___x_1798_);
    leanh::lean_ctor_set(v___x_1799_, 1, v___x_1788_);
    v___x_1800_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__14;
    v___x_1801_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1799_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1800_);
    v___x_1802_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    leanh::lean_ctor_set(v___x_1802_, 1, v___x_1777_);
    v___x_1803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once),
        _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15,
    );
    v___x_1804_ = l_Std_Http_instReprRequestTarget_repr(v_uri_1775_, v___x_1780_);
    v___x_1805_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1803_);
    leanh::lean_ctor_set(v___x_1805_, 1, v___x_1804_);
    v___x_1806_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1806_, 0, v___x_1805_);
    leanh::lean_ctor_set_uint8(
        v___x_1806_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1783_,
    );
    v___x_1807_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1807_, 0, v___x_1802_);
    leanh::lean_ctor_set(v___x_1807_, 1, v___x_1806_);
    v___x_1808_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1808_, 0, v___x_1807_);
    leanh::lean_ctor_set(v___x_1808_, 1, v___x_1786_);
    v___x_1809_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    leanh::lean_ctor_set(v___x_1809_, 1, v___x_1788_);
    v___x_1810_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__17;
    v___x_1811_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1809_);
    leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
    v___x_1812_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    leanh::lean_ctor_set(v___x_1812_, 1, v___x_1777_);
    v___x_1813_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_1776_);
    v___x_1814_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1814_, 0, v___x_1793_);
    leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
    v___x_1815_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    leanh::lean_ctor_set_uint8(
        v___x_1815_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1783_,
    );
    v___x_1816_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1816_, 0, v___x_1812_);
    leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
    v___x_1817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instReprHead_repr___redArg___closed__20_once),
        _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20,
    );
    v___x_1818_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__21;
    v___x_1819_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
    leanh::lean_ctor_set(v___x_1819_, 1, v___x_1816_);
    v___x_1820_ = l_Std_Http_Request_instReprHead_repr___redArg___closed__22;
    v___x_1821_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1821_, 0, v___x_1819_);
    leanh::lean_ctor_set(v___x_1821_, 1, v___x_1820_);
    v___x_1822_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1822_, 0, v___x_1817_);
    leanh::lean_ctor_set(v___x_1822_, 1, v___x_1821_);
    v___x_1823_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1823_, 0, v___x_1822_);
    leanh::lean_ctor_set_uint8(
        v___x_1823_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1783_,
    );
    return v___x_1823_;
}
pub unsafe fn l_Std_Http_Request_instReprHead_repr(
    mut v_x_1824_: *mut leanh::LeanObject,
    mut v_prec_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_1824_);
    return v___x_1826_;
}
pub unsafe fn l_Std_Http_Request_instReprHead_repr___boxed(
    mut v_x_1827_: *mut leanh::LeanObject,
    mut v_prec_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Std_Http_Request_instReprHead_repr(v_x_1827_, v_prec_1828_);
    leanh::lean_dec(v_prec_1828_);
    return v_res_1829_;
}
pub unsafe fn l_Std_Http_instInhabitedRequest_default___redArg(
    mut v_inst_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Std_Http_Request_instInhabitedHead_default;
    v___x_1834_ = l_Std_Http_Extensions_empty;
    v___x_1835_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1835_, 0, v___x_1833_);
    leanh::lean_ctor_set(v___x_1835_, 1, v_inst_1832_);
    leanh::lean_ctor_set(v___x_1835_, 2, v___x_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Std_Http_instInhabitedRequest_default(
    mut v_t_1836_: *mut leanh::LeanObject,
    mut v_inst_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Std_Http_instInhabitedRequest___redArg(
    mut v_inst_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_1839_);
    return v___x_1840_;
}
pub unsafe fn l_Std_Http_instInhabitedRequest(
    mut v_a_1841_: *mut leanh::LeanObject,
    mut v_inst_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__0(
    mut v_x_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1845_ = leanh::lean_ctor_get(v_x_1844_, 0);
    leanh::lean_inc(v_fst_1845_);
    v_snd_1846_ = leanh::lean_ctor_get(v_x_1844_, 1);
    leanh::lean_inc(v_snd_1846_);
    leanh::lean_dec_ref(v_x_1844_);
    v___x_1847_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1845_, v_snd_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__1(
    mut v_x_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = lean_string_from_utf8_unchecked(v_x_1848_);
    return v___x_1849_;
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__2(
    mut v___x_1850_: *mut leanh::LeanObject,
    mut v___x_1851_: *mut leanh::LeanObject,
    mut v___x_1852_: *mut leanh::LeanObject,
    mut v_fst_1853_: *mut leanh::LeanObject,
    mut v___x_1854_: *mut leanh::LeanObject,
    mut v___x_1855_: u32,
    mut v___x_1856_: *mut leanh::LeanObject,
    mut v_it_1857_: *mut leanh::LeanObject,
    mut v_acc_1858_: *mut leanh::LeanObject,
    mut v_hP_1859_: *mut leanh::LeanObject,
    mut v_recur_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_it_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u32 = 0;
    let mut v___x_1884_: u32 = 0;
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u32 = 0;
    let mut v___x_1888_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u32 = 0;
    let mut v___x_1891_: u32 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1899_: u32 = 0;
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_1857_) == 0 {
                    v_currPos_1893_ = leanh::lean_ctor_get(v_it_1857_, 0);
                    v_searcher_1894_ = leanh::lean_ctor_get(v_it_1857_, 1);
                    v_isSharedCheck_1916_ = (!leanh::lean_is_exclusive(v_it_1857_)) as u8;
                    if v_isSharedCheck_1916_ == 0 {
                        v___x_1896_ = v_it_1857_;
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1894_);
                        leanh::lean_inc(v_currPos_1893_);
                        leanh::lean_dec(v_it_1857_);
                        v___x_1896_ = leanh::lean_box(0);
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_recur_1860_);
                    leanh::lean_dec(v___x_1854_);
                    return v_acc_1858_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_acc_1858_) == 0 {
                    v___x_1864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1864_, 0, v_out_1863_);
                    v___x_1865_ = leanh::lean_apply_4(
                        v_recur_1860_,
                        v_it_1862_,
                        v___x_1864_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_1865_;
                } else {
                    v_val_1866_ = leanh::lean_ctor_get(v_acc_1858_, 0);
                    v_isSharedCheck_1877_ = (!leanh::lean_is_exclusive(v_acc_1858_)) as u8;
                    if v_isSharedCheck_1877_ == 0 {
                        v___x_1868_ = v_acc_1858_;
                        v_isShared_1869_ = v_isSharedCheck_1877_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1866_);
                        leanh::lean_dec(v_acc_1858_);
                        v___x_1868_ = leanh::lean_box(0);
                        v_isShared_1869_ = v_isSharedCheck_1877_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1870_ = lean_string_utf8_extract(v___x_1850_, v___x_1851_, v___x_1852_);
                v___x_1871_ = lean_string_append(v_val_1866_, v___x_1870_);
                leanh::lean_dec_ref(v___x_1870_);
                v___x_1872_ = lean_string_append(v___x_1871_, v_out_1863_);
                leanh::lean_dec_ref(v_out_1863_);
                if v_isShared_1869_ == 0 {
                    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1872_);
                    v___x_1874_ = v___x_1868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1872_);
                    v___x_1874_ = v_reuseFailAlloc_1876_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1875_ = leanh::lean_apply_4(
                    v_recur_1860_,
                    v_it_1862_,
                    v___x_1874_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1875_;
            }
            4 => {
                v___x_1882_ = lean_string_utf8_extract(
                    v_fst_1853_,
                    v_startInclusive_1880_,
                    v_endExclusive_1881_,
                );
                leanh::lean_dec(v_endExclusive_1881_);
                leanh::lean_dec(v_startInclusive_1880_);
                v___x_1883_ = lean_string_utf8_get(v___x_1882_, v___x_1851_);
                v___x_1884_ = 97;
                v___x_1885_ = lean_uint32_dec_le(v___x_1884_, v___x_1883_);
                if v___x_1885_ == 0 {
                    v___x_1886_ = lean_string_utf8_set(v___x_1882_, v___x_1851_, v___x_1883_);
                    v_it_1862_ = v_it_1879_;
                    v_out_1863_ = v___x_1886_;
                    state = 1;
                    continue;
                } else {
                    v___x_1887_ = 122;
                    v___x_1888_ = lean_uint32_dec_le(v___x_1883_, v___x_1887_);
                    if v___x_1888_ == 0 {
                        v___x_1889_ = lean_string_utf8_set(v___x_1882_, v___x_1851_, v___x_1883_);
                        v_it_1862_ = v_it_1879_;
                        v_out_1863_ = v___x_1889_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1890_ = 4294967264;
                        v___x_1891_ = lean_uint32_add(v___x_1883_, v___x_1890_);
                        v___x_1892_ = lean_string_utf8_set(v___x_1882_, v___x_1851_, v___x_1891_);
                        v_it_1862_ = v_it_1879_;
                        v_out_1863_ = v___x_1892_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1898_ = lean_nat_dec_eq(v_searcher_1894_, v___x_1854_);
                if v___x_1898_ == 0 {
                    leanh::lean_dec(v___x_1854_);
                    v___x_1899_ = lean_string_utf8_get_fast(v_fst_1853_, v_searcher_1894_);
                    v___x_1900_ = lean_uint32_dec_eq(v___x_1899_, v___x_1855_);
                    if v___x_1900_ == 0 {
                        v___x_1901_ = lean_string_utf8_next_fast(v_fst_1853_, v_searcher_1894_);
                        leanh::lean_dec(v_searcher_1894_);
                        if v_isShared_1897_ == 0 {
                            leanh::lean_ctor_set(v___x_1896_, 1, v___x_1901_);
                            v___x_1903_ = v___x_1896_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1905_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_currPos_1893_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1901_);
                            v___x_1903_ = v_reuseFailAlloc_1905_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1906_ = lean_string_utf8_next_fast(v_fst_1853_, v_searcher_1894_);
                        v___x_1907_ = lean_nat_sub(v___x_1906_, v_searcher_1894_);
                        v___x_1908_ = lean_nat_add(v_searcher_1894_, v___x_1907_);
                        leanh::lean_dec(v___x_1907_);
                        v_slice_1909_ = l_String_Slice_subslice_x21(
                            v___x_1856_,
                            v_currPos_1893_,
                            v_searcher_1894_,
                        );
                        leanh::lean_inc(v___x_1908_);
                        if v_isShared_1897_ == 0 {
                            leanh::lean_ctor_set(v___x_1896_, 1, v___x_1908_);
                            leanh::lean_ctor_set(v___x_1896_, 0, v___x_1908_);
                            v_nextIt_1911_ = v___x_1896_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1914_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1908_);
                            v_nextIt_1911_ = v_reuseFailAlloc_1914_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1896_);
                    leanh::lean_dec(v_searcher_1894_);
                    v___x_1915_ = leanh::lean_box(1);
                    v_it_1879_ = v___x_1915_;
                    v_startInclusive_1880_ = v_currPos_1893_;
                    v_endExclusive_1881_ = v___x_1854_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1904_ = leanh::lean_apply_4(
                    v_recur_1860_,
                    v___x_1903_,
                    v_acc_1858_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1904_;
            }
            7 => {
                v_startInclusive_1912_ = leanh::lean_ctor_get(v_slice_1909_, 0);
                leanh::lean_inc(v_startInclusive_1912_);
                v_endExclusive_1913_ = leanh::lean_ctor_get(v_slice_1909_, 1);
                leanh::lean_inc(v_endExclusive_1913_);
                leanh::lean_dec_ref(v_slice_1909_);
                v_it_1879_ = v_nextIt_1911_;
                v_startInclusive_1880_ = v_startInclusive_1912_;
                v_endExclusive_1881_ = v_endExclusive_1913_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__2___boxed(
    mut v___x_1917_: *mut leanh::LeanObject,
    mut v___x_1918_: *mut leanh::LeanObject,
    mut v___x_1919_: *mut leanh::LeanObject,
    mut v_fst_1920_: *mut leanh::LeanObject,
    mut v___x_1921_: *mut leanh::LeanObject,
    mut v___x_1922_: *mut leanh::LeanObject,
    mut v___x_1923_: *mut leanh::LeanObject,
    mut v_it_1924_: *mut leanh::LeanObject,
    mut v_acc_1925_: *mut leanh::LeanObject,
    mut v_hP_1926_: *mut leanh::LeanObject,
    mut v_recur_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609__boxed_1928_: u32 = 0;
    let mut v_res_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609__boxed_1928_ = leanh::lean_unbox_uint32(v___x_1922_);
    leanh::lean_dec(v___x_1922_);
    v_res_1929_ = l_Std_Http_Request_instToStringHead___lam__2(
        v___x_1917_,
        v___x_1918_,
        v___x_1919_,
        v_fst_1920_,
        v___x_1921_,
        v___x_1609__boxed_1928_,
        v___x_1923_,
        v_it_1924_,
        v_acc_1925_,
        v_hP_1926_,
        v_recur_1927_,
    );
    leanh::lean_dec_ref(v___x_1923_);
    leanh::lean_dec_ref(v_fst_1920_);
    leanh::lean_dec(v___x_1919_);
    leanh::lean_dec(v___x_1918_);
    leanh::lean_dec_ref(v___x_1917_);
    return v_res_1929_;
}
pub unsafe fn _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Std_Http_Request_instToStringHead___lam__3___closed__2;
    v___x_1934_ = lean_string_utf8_byte_size(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1936_: u32 = 0;
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = 45;
    v___x_1937_ = leanh::lean_box_uint32(v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__3(
    mut v_x_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1939_ = leanh::lean_ctor_get(v_x_1938_, 0);
                leanh::lean_inc_n(v_fst_1939_, 2);
                v_snd_1940_ = leanh::lean_ctor_get(v_x_1938_, 1);
                leanh::lean_inc(v_snd_1940_);
                leanh::lean_dec_ref(v_x_1938_);
                v___f_1946_ = l_Std_Http_Request_instToStringHead___lam__3___closed__1;
                v___x_1947_ = leanh::lean_unsigned_to_nat(0);
                v___x_1948_ = lean_string_utf8_byte_size(v_fst_1939_);
                v___x_1949_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1949_, 0, v_fst_1939_);
                leanh::lean_ctor_set(v___x_1949_, 1, v___x_1947_);
                leanh::lean_ctor_set(v___x_1949_, 2, v___x_1948_);
                leanh::lean_inc_ref(v___x_1949_);
                v_it_1950_ = l_String_Slice_splitToSubslice___redArg(v___x_1949_, v___f_1946_);
                v___x_1951_ = l_Std_Http_Request_instToStringHead___lam__3___closed__2;
                v___x_1952_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instToStringHead___lam__3___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instToStringHead___lam__3___closed__3_once
                    ),
                    _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3,
                );
                v___x_1953_ = l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1;
                v___f_1954_ = leanh::lean_alloc_closure(
                    l_Std_Http_Request_instToStringHead___lam__2___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_1954_, 0, v___x_1951_);
                leanh::lean_closure_set(v___f_1954_, 1, v___x_1947_);
                leanh::lean_closure_set(v___f_1954_, 2, v___x_1952_);
                leanh::lean_closure_set(v___f_1954_, 3, v_fst_1939_);
                leanh::lean_closure_set(v___f_1954_, 4, v___x_1948_);
                leanh::lean_closure_set(v___f_1954_, 5, v___x_1953_);
                leanh::lean_closure_set(v___f_1954_, 6, v___x_1949_);
                v___x_1955_ = leanh::lean_box(0);
                v___x_1956_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1954_,
                    v_it_1950_,
                    v___x_1955_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1956_) == 0 {
                    v___x_1957_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_1942_ = v___x_1957_;
                    state = 1;
                    continue;
                } else {
                    v_val_1958_ = leanh::lean_ctor_get(v___x_1956_, 0);
                    leanh::lean_inc(v_val_1958_);
                    leanh::lean_dec_ref_known(v___x_1956_, 1);
                    v___y_1942_ = v_val_1958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1943_ = l_Std_Http_Request_instToStringHead___lam__3___closed__0;
                v___x_1944_ = lean_string_append(v___y_1942_, v___x_1943_);
                v___x_1945_ = lean_string_append(v___x_1944_, v_snd_1940_);
                leanh::lean_dec(v_snd_1940_);
                return v___x_1945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_instToStringHead___lam__6(
    mut v___f_2034_: *mut leanh::LeanObject,
    mut v___f_2035_: *mut leanh::LeanObject,
    mut v___f_2036_: *mut leanh::LeanObject,
    mut v___f_2037_: *mut leanh::LeanObject,
    mut v___f_2038_: *mut leanh::LeanObject,
    mut v_req_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_2040_: u8 = 0;
    let mut v_version_2041_: u8 = 0;
    let mut v_uri_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2052_: usize = 0;
    let mut v___x_2053_: usize = 0;
    let mut v_pairs_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_2142_: u8 = 0;
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2145_: usize = 0;
    let mut v___x_2146_: usize = 0;
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2178_: u16 = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2219_: u16 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_2246_: u8 = 0;
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2249_: usize = 0;
    let mut v___x_2250_: usize = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_2040_ = leanh::lean_ctor_get_uint8(
                    v_req_2039_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_2041_ = leanh::lean_ctor_get_uint8(
                    v_req_2039_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_2042_ = leanh::lean_ctor_get(v_req_2039_, 0);
                leanh::lean_inc(v_uri_2042_);
                v_headers_2043_ = leanh::lean_ctor_get(v_req_2039_, 1);
                leanh::lean_inc_ref(v_headers_2043_);
                leanh::lean_dec_ref(v_req_2039_);
                match v_method_2040_ {
                    0 => {
                        v___x_2312_ = l_Std_Http_Request_instToStringHead___lam__6___closed__26;
                        v___y_2240_ = v___x_2312_;
                        state = 14;
                        continue;
                    }
                    1 => {
                        v___x_2313_ = l_Std_Http_Request_instToStringHead___lam__6___closed__27;
                        v___y_2240_ = v___x_2313_;
                        state = 14;
                        continue;
                    }
                    2 => {
                        v___x_2314_ = l_Std_Http_Request_instToStringHead___lam__6___closed__28;
                        v___y_2240_ = v___x_2314_;
                        state = 14;
                        continue;
                    }
                    3 => {
                        v___x_2315_ = l_Std_Http_Request_instToStringHead___lam__6___closed__29;
                        v___y_2240_ = v___x_2315_;
                        state = 14;
                        continue;
                    }
                    4 => {
                        v___x_2316_ = l_Std_Http_Request_instToStringHead___lam__6___closed__30;
                        v___y_2240_ = v___x_2316_;
                        state = 14;
                        continue;
                    }
                    5 => {
                        v___x_2317_ = l_Std_Http_Request_instToStringHead___lam__6___closed__31;
                        v___y_2240_ = v___x_2317_;
                        state = 14;
                        continue;
                    }
                    6 => {
                        v___x_2318_ = l_Std_Http_Request_instToStringHead___lam__6___closed__32;
                        v___y_2240_ = v___x_2318_;
                        state = 14;
                        continue;
                    }
                    7 => {
                        v___x_2319_ = l_Std_Http_Request_instToStringHead___lam__6___closed__33;
                        v___y_2240_ = v___x_2319_;
                        state = 14;
                        continue;
                    }
                    8 => {
                        v___x_2320_ = l_Std_Http_Request_instToStringHead___lam__6___closed__34;
                        v___y_2240_ = v___x_2320_;
                        state = 14;
                        continue;
                    }
                    9 => {
                        v___x_2321_ = l_Std_Http_Request_instToStringHead___lam__6___closed__35;
                        v___y_2240_ = v___x_2321_;
                        state = 14;
                        continue;
                    }
                    10 => {
                        v___x_2322_ = l_Std_Http_Request_instToStringHead___lam__6___closed__36;
                        v___y_2240_ = v___x_2322_;
                        state = 14;
                        continue;
                    }
                    11 => {
                        v___x_2323_ = l_Std_Http_Request_instToStringHead___lam__6___closed__37;
                        v___y_2240_ = v___x_2323_;
                        state = 14;
                        continue;
                    }
                    12 => {
                        v___x_2324_ = l_Std_Http_Request_instToStringHead___lam__6___closed__38;
                        v___y_2240_ = v___x_2324_;
                        state = 14;
                        continue;
                    }
                    13 => {
                        v___x_2325_ = l_Std_Http_Request_instToStringHead___lam__6___closed__39;
                        v___y_2240_ = v___x_2325_;
                        state = 14;
                        continue;
                    }
                    14 => {
                        v___x_2326_ = l_Std_Http_Request_instToStringHead___lam__6___closed__40;
                        v___y_2240_ = v___x_2326_;
                        state = 14;
                        continue;
                    }
                    15 => {
                        v___x_2327_ = l_Std_Http_Request_instToStringHead___lam__6___closed__41;
                        v___y_2240_ = v___x_2327_;
                        state = 14;
                        continue;
                    }
                    16 => {
                        v___x_2328_ = l_Std_Http_Request_instToStringHead___lam__6___closed__42;
                        v___y_2240_ = v___x_2328_;
                        state = 14;
                        continue;
                    }
                    17 => {
                        v___x_2329_ = l_Std_Http_Request_instToStringHead___lam__6___closed__43;
                        v___y_2240_ = v___x_2329_;
                        state = 14;
                        continue;
                    }
                    18 => {
                        v___x_2330_ = l_Std_Http_Request_instToStringHead___lam__6___closed__44;
                        v___y_2240_ = v___x_2330_;
                        state = 14;
                        continue;
                    }
                    19 => {
                        v___x_2331_ = l_Std_Http_Request_instToStringHead___lam__6___closed__45;
                        v___y_2240_ = v___x_2331_;
                        state = 14;
                        continue;
                    }
                    20 => {
                        v___x_2332_ = l_Std_Http_Request_instToStringHead___lam__6___closed__46;
                        v___y_2240_ = v___x_2332_;
                        state = 14;
                        continue;
                    }
                    21 => {
                        v___x_2333_ = l_Std_Http_Request_instToStringHead___lam__6___closed__47;
                        v___y_2240_ = v___x_2333_;
                        state = 14;
                        continue;
                    }
                    22 => {
                        v___x_2334_ = l_Std_Http_Request_instToStringHead___lam__6___closed__48;
                        v___y_2240_ = v___x_2334_;
                        state = 14;
                        continue;
                    }
                    23 => {
                        v___x_2335_ = l_Std_Http_Request_instToStringHead___lam__6___closed__49;
                        v___y_2240_ = v___x_2335_;
                        state = 14;
                        continue;
                    }
                    24 => {
                        v___x_2336_ = l_Std_Http_Request_instToStringHead___lam__6___closed__50;
                        v___y_2240_ = v___x_2336_;
                        state = 14;
                        continue;
                    }
                    25 => {
                        v___x_2337_ = l_Std_Http_Request_instToStringHead___lam__6___closed__51;
                        v___y_2240_ = v___x_2337_;
                        state = 14;
                        continue;
                    }
                    26 => {
                        v___x_2338_ = l_Std_Http_Request_instToStringHead___lam__6___closed__52;
                        v___y_2240_ = v___x_2338_;
                        state = 14;
                        continue;
                    }
                    27 => {
                        v___x_2339_ = l_Std_Http_Request_instToStringHead___lam__6___closed__53;
                        v___y_2240_ = v___x_2339_;
                        state = 14;
                        continue;
                    }
                    28 => {
                        v___x_2340_ = l_Std_Http_Request_instToStringHead___lam__6___closed__54;
                        v___y_2240_ = v___x_2340_;
                        state = 14;
                        continue;
                    }
                    29 => {
                        v___x_2341_ = l_Std_Http_Request_instToStringHead___lam__6___closed__55;
                        v___y_2240_ = v___x_2341_;
                        state = 14;
                        continue;
                    }
                    30 => {
                        v___x_2342_ = l_Std_Http_Request_instToStringHead___lam__6___closed__56;
                        v___y_2240_ = v___x_2342_;
                        state = 14;
                        continue;
                    }
                    31 => {
                        v___x_2343_ = l_Std_Http_Request_instToStringHead___lam__6___closed__57;
                        v___y_2240_ = v___x_2343_;
                        state = 14;
                        continue;
                    }
                    32 => {
                        v___x_2344_ = l_Std_Http_Request_instToStringHead___lam__6___closed__58;
                        v___y_2240_ = v___x_2344_;
                        state = 14;
                        continue;
                    }
                    33 => {
                        v___x_2345_ = l_Std_Http_Request_instToStringHead___lam__6___closed__59;
                        v___y_2240_ = v___x_2345_;
                        state = 14;
                        continue;
                    }
                    34 => {
                        v___x_2346_ = l_Std_Http_Request_instToStringHead___lam__6___closed__60;
                        v___y_2240_ = v___x_2346_;
                        state = 14;
                        continue;
                    }
                    35 => {
                        v___x_2347_ = l_Std_Http_Request_instToStringHead___lam__6___closed__61;
                        v___y_2240_ = v___x_2347_;
                        state = 14;
                        continue;
                    }
                    36 => {
                        v___x_2348_ = l_Std_Http_Request_instToStringHead___lam__6___closed__62;
                        v___y_2240_ = v___x_2348_;
                        state = 14;
                        continue;
                    }
                    37 => {
                        v___x_2349_ = l_Std_Http_Request_instToStringHead___lam__6___closed__63;
                        v___y_2240_ = v___x_2349_;
                        state = 14;
                        continue;
                    }
                    38 => {
                        v___x_2350_ = l_Std_Http_Request_instToStringHead___lam__6___closed__64;
                        v___y_2240_ = v___x_2350_;
                        state = 14;
                        continue;
                    }
                    _ => {
                        v___x_2351_ = l_Std_Http_Request_instToStringHead___lam__6___closed__65;
                        v___y_2240_ = v___x_2351_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v_entries_2047_ = leanh::lean_ctor_get(v_headers_2043_, 0);
                leanh::lean_inc_ref(v_entries_2047_);
                leanh::lean_dec_ref(v_headers_2043_);
                v___x_2048_ = lean_string_append(v___y_2045_, v___y_2046_);
                v___x_2049_ = l_Std_Http_Request_instToStringHead___lam__6___closed__0;
                v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
                v___x_2051_ = l_Std_Http_Request_instToStringHead___lam__6___closed__10;
                v_sz_2052_ = lean_array_size(v_entries_2047_);
                v___x_2053_ = 0usize;
                v_pairs_2054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2051_,
                    v___f_2034_,
                    v_sz_2052_,
                    v___x_2053_,
                    v_entries_2047_,
                );
                v___x_2055_ = lean_array_to_list(v_pairs_2054_);
                v___x_2056_ = l_String_intercalate(v___x_2049_, v___x_2055_);
                v___x_2057_ = lean_string_append(v___x_2050_, v___x_2056_);
                leanh::lean_dec_ref(v___x_2056_);
                v___x_2058_ = lean_string_append(v___x_2057_, v___x_2049_);
                return v___x_2058_;
            }
            2 => {
                v___x_2063_ = lean_string_append(v___y_2060_, v___y_2062_);
                leanh::lean_dec_ref(v___y_2062_);
                v___x_2064_ = lean_string_append(v___x_2063_, v___y_2061_);
                match v_version_2041_ {
                    0 => {
                        v___x_2065_ = l_Std_Http_Request_instToStringHead___lam__6___closed__11;
                        v___y_2045_ = v___x_2064_;
                        v___y_2046_ = v___x_2065_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2066_ = l_Std_Http_Request_instToStringHead___lam__6___closed__12;
                        v___y_2045_ = v___x_2064_;
                        v___y_2046_ = v___x_2066_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_2067_ = l_Std_Http_Request_instToStringHead___lam__6___closed__13;
                        v___y_2045_ = v___x_2064_;
                        v___y_2046_ = v___x_2067_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2068_ = l_Std_Http_Request_instToStringHead___lam__6___closed__14;
                        v___y_2045_ = v___x_2064_;
                        v___y_2046_ = v___x_2068_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_2072_) == 0 {
                    leanh::lean_dec_ref(v___f_2035_);
                    v___y_2060_ = v___y_2070_;
                    v___y_2061_ = v___y_2071_;
                    v___y_2062_ = v___y_2073_;
                    state = 2;
                    continue;
                } else {
                    v_val_2074_ = leanh::lean_ctor_get(v___y_2072_, 0);
                    leanh::lean_inc(v_val_2074_);
                    leanh::lean_dec_ref_known(v___y_2072_, 1);
                    v___x_2075_ = lean_array_get_size(v_val_2074_);
                    v___x_2076_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2077_ = lean_nat_dec_eq(v___x_2075_, v___x_2076_);
                    if v___x_2077_ == 0 {
                        v___x_2078_ = lean_array_to_list(v_val_2074_);
                        v___x_2079_ = leanh::lean_box(0);
                        v_encodedParams_2080_ =
                            l_List_mapTR_loop___redArg(v___f_2035_, v___x_2078_, v___x_2079_);
                        v___x_2081_ = l_Std_Http_Request_instToStringHead___lam__6___closed__15;
                        v___x_2082_ = l_Std_Http_Request_instToStringHead___lam__6___closed__16;
                        v___x_2083_ = l_String_intercalate(v___x_2082_, v_encodedParams_2080_);
                        v___x_2084_ = lean_string_append(v___x_2081_, v___x_2083_);
                        leanh::lean_dec_ref(v___x_2083_);
                        v___x_2085_ = lean_string_append(v___y_2073_, v___x_2084_);
                        leanh::lean_dec_ref(v___x_2084_);
                        v___y_2060_ = v___y_2070_;
                        v___y_2061_ = v___y_2071_;
                        v___y_2062_ = v___x_2085_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_2074_);
                        leanh::lean_dec_ref(v___f_2035_);
                        v___y_2060_ = v___y_2070_;
                        v___y_2061_ = v___y_2071_;
                        v___y_2062_ = v___y_2073_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2094_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                v___x_2095_ = lean_string_append(v___y_2087_, v___x_2094_);
                v___x_2096_ = lean_string_append(v___x_2095_, v___y_2091_);
                leanh::lean_dec_ref(v___y_2091_);
                v___x_2097_ = lean_string_append(v___x_2096_, v___y_2089_);
                leanh::lean_dec_ref(v___y_2089_);
                v___x_2098_ = lean_string_append(v___x_2097_, v___y_2092_);
                leanh::lean_dec_ref(v___y_2092_);
                v___x_2099_ = lean_string_append(v___x_2098_, v___y_2093_);
                leanh::lean_dec_ref(v___y_2093_);
                v___y_2060_ = v___y_2088_;
                v___y_2061_ = v___y_2090_;
                v___y_2062_ = v___x_2099_;
                state = 2;
                continue;
            }
            5 => {
                if leanh::lean_obj_tag(v___y_2102_) == 0 {
                    v___x_2108_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2087_ = v___y_2101_;
                    v___y_2088_ = v___y_2103_;
                    v___y_2089_ = v___y_2104_;
                    v___y_2090_ = v___y_2106_;
                    v___y_2091_ = v___y_2105_;
                    v___y_2092_ = v___y_2107_;
                    v___y_2093_ = v___x_2108_;
                    state = 4;
                    continue;
                } else {
                    v_val_2109_ = leanh::lean_ctor_get(v___y_2102_, 0);
                    leanh::lean_inc(v_val_2109_);
                    leanh::lean_dec_ref_known(v___y_2102_, 1);
                    v___x_2110_ = l_Std_Http_Request_instToStringHead___lam__6___closed__18;
                    v___x_2111_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2109_);
                    leanh::lean_dec(v_val_2109_);
                    v___x_2112_ = lean_string_from_utf8_unchecked(v___x_2111_);
                    v___x_2113_ = lean_string_append(v___x_2110_, v___x_2112_);
                    leanh::lean_dec_ref(v___x_2112_);
                    v___y_2087_ = v___y_2101_;
                    v___y_2088_ = v___y_2103_;
                    v___y_2089_ = v___y_2104_;
                    v___y_2090_ = v___y_2106_;
                    v___y_2091_ = v___y_2105_;
                    v___y_2092_ = v___y_2107_;
                    v___y_2093_ = v___x_2113_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2122_ = lean_array_get_size(v___y_2118_);
                v___x_2123_ = leanh::lean_unsigned_to_nat(0);
                v___x_2124_ = lean_nat_dec_eq(v___x_2122_, v___x_2123_);
                if v___x_2124_ == 0 {
                    v___x_2125_ = lean_array_to_list(v___y_2118_);
                    v___x_2126_ = leanh::lean_box(0);
                    v_encodedParams_2127_ =
                        l_List_mapTR_loop___redArg(v___f_2036_, v___x_2125_, v___x_2126_);
                    v___x_2128_ = l_Std_Http_Request_instToStringHead___lam__6___closed__15;
                    v___x_2129_ = l_Std_Http_Request_instToStringHead___lam__6___closed__16;
                    v___x_2130_ = l_String_intercalate(v___x_2129_, v_encodedParams_2127_);
                    v___x_2131_ = lean_string_append(v___x_2128_, v___x_2130_);
                    leanh::lean_dec_ref(v___x_2130_);
                    v___y_2101_ = v___y_2115_;
                    v___y_2102_ = v___y_2117_;
                    v___y_2103_ = v___y_2116_;
                    v___y_2104_ = v___y_2121_;
                    v___y_2105_ = v___y_2120_;
                    v___y_2106_ = v___y_2119_;
                    v___y_2107_ = v___x_2131_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_2118_);
                    leanh::lean_dec_ref(v___f_2036_);
                    v___x_2132_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2101_ = v___y_2115_;
                    v___y_2102_ = v___y_2117_;
                    v___y_2103_ = v___y_2116_;
                    v___y_2104_ = v___y_2121_;
                    v___y_2105_ = v___y_2120_;
                    v___y_2106_ = v___y_2119_;
                    v___y_2107_ = v___x_2132_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v_segments_2141_ = leanh::lean_ctor_get(v___y_2139_, 0);
                leanh::lean_inc_ref(v_segments_2141_);
                v_absolute_2142_ = leanh::lean_ctor_get_uint8(
                    v___y_2139_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v___y_2139_);
                v___x_2143_ = l_Std_Http_Request_instToStringHead___lam__6___closed__19;
                v___x_2144_ = l_Std_Http_Request_instToStringHead___lam__6___closed__10;
                v_sz_2145_ = lean_array_size(v_segments_2141_);
                v___x_2146_ = 0usize;
                v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2144_,
                    v___f_2037_,
                    v_sz_2145_,
                    v___x_2146_,
                    v_segments_2141_,
                );
                v___x_2148_ = lean_array_to_list(v___x_2147_);
                v_result_2149_ = l_String_intercalate(v___x_2143_, v___x_2148_);
                if v_absolute_2142_ == 0 {
                    v___y_2115_ = v___y_2134_;
                    v___y_2116_ = v___y_2136_;
                    v___y_2117_ = v___y_2135_;
                    v___y_2118_ = v___y_2137_;
                    v___y_2119_ = v___y_2138_;
                    v___y_2120_ = v___y_2140_;
                    v___y_2121_ = v_result_2149_;
                    state = 6;
                    continue;
                } else {
                    v___x_2150_ = lean_string_append(v___x_2143_, v_result_2149_);
                    leanh::lean_dec_ref(v_result_2149_);
                    v___y_2115_ = v___y_2134_;
                    v___y_2116_ = v___y_2136_;
                    v___y_2117_ = v___y_2135_;
                    v___y_2118_ = v___y_2137_;
                    v___y_2119_ = v___y_2138_;
                    v___y_2120_ = v___y_2140_;
                    v___y_2121_ = v___x_2150_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_2162_ = lean_string_append(v___y_2159_, v___y_2153_);
                leanh::lean_dec_ref(v___y_2153_);
                v___x_2163_ = lean_string_append(v___x_2162_, v___y_2161_);
                leanh::lean_dec_ref(v___y_2161_);
                leanh::lean_inc_ref(v___y_2152_);
                v___x_2164_ = lean_string_append(v___y_2152_, v___x_2163_);
                leanh::lean_dec_ref(v___x_2163_);
                v___y_2134_ = v___y_2154_;
                v___y_2135_ = v___y_2156_;
                v___y_2136_ = v___y_2155_;
                v___y_2137_ = v___y_2157_;
                v___y_2138_ = v___y_2158_;
                v___y_2139_ = v___y_2160_;
                v___y_2140_ = v___x_2164_;
                state = 7;
                continue;
            }
            9 => match leanh::lean_obj_tag(v_port_2173_) {
                0 => {
                    v___x_2176_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2152_ = v___y_2166_;
                    v___y_2153_ = v___y_2175_;
                    v___y_2154_ = v___y_2167_;
                    v___y_2155_ = v___y_2169_;
                    v___y_2156_ = v___y_2168_;
                    v___y_2157_ = v___y_2170_;
                    v___y_2158_ = v___y_2171_;
                    v___y_2159_ = v___y_2172_;
                    v___y_2160_ = v___y_2174_;
                    v___y_2161_ = v___x_2176_;
                    state = 8;
                    continue;
                }
                1 => {
                    v___x_2177_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___y_2152_ = v___y_2166_;
                    v___y_2153_ = v___y_2175_;
                    v___y_2154_ = v___y_2167_;
                    v___y_2155_ = v___y_2169_;
                    v___y_2156_ = v___y_2168_;
                    v___y_2157_ = v___y_2170_;
                    v___y_2158_ = v___y_2171_;
                    v___y_2159_ = v___y_2172_;
                    v___y_2160_ = v___y_2174_;
                    v___y_2161_ = v___x_2177_;
                    state = 8;
                    continue;
                }
                _ => {
                    v_port_2178_ = leanh::lean_ctor_get_uint16(v_port_2173_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_2173_, 0);
                    v___x_2179_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___x_2180_ = lean_uint16_to_nat(v_port_2178_);
                    v___x_2181_ = l_Nat_reprFast(v___x_2180_);
                    v___x_2182_ = lean_string_append(v___x_2179_, v___x_2181_);
                    leanh::lean_dec_ref(v___x_2181_);
                    v___y_2152_ = v___y_2166_;
                    v___y_2153_ = v___y_2175_;
                    v___y_2154_ = v___y_2167_;
                    v___y_2155_ = v___y_2169_;
                    v___y_2156_ = v___y_2168_;
                    v___y_2157_ = v___y_2170_;
                    v___y_2158_ = v___y_2171_;
                    v___y_2159_ = v___y_2172_;
                    v___y_2160_ = v___y_2174_;
                    v___y_2161_ = v___x_2182_;
                    state = 8;
                    continue;
                }
            },
            10 => match leanh::lean_obj_tag(v_host_2191_) {
                0 => {
                    v_name_2194_ = leanh::lean_ctor_get(v_host_2191_, 0);
                    leanh::lean_inc_ref(v_name_2194_);
                    leanh::lean_dec_ref_known(v_host_2191_, 1);
                    v___y_2166_ = v___y_2184_;
                    v___y_2167_ = v___y_2185_;
                    v___y_2168_ = v___y_2187_;
                    v___y_2169_ = v___y_2186_;
                    v___y_2170_ = v___y_2188_;
                    v___y_2171_ = v___y_2189_;
                    v___y_2172_ = v___y_2193_;
                    v_port_2173_ = v_port_2192_;
                    v___y_2174_ = v___y_2190_;
                    v___y_2175_ = v_name_2194_;
                    state = 9;
                    continue;
                }
                1 => {
                    v_ipv4_2195_ = leanh::lean_ctor_get(v_host_2191_, 0);
                    leanh::lean_inc_ref(v_ipv4_2195_);
                    leanh::lean_dec_ref_known(v_host_2191_, 1);
                    v___x_2196_ = lean_uv_ntop_v4(v_ipv4_2195_);
                    leanh::lean_dec_ref(v_ipv4_2195_);
                    v___y_2166_ = v___y_2184_;
                    v___y_2167_ = v___y_2185_;
                    v___y_2168_ = v___y_2187_;
                    v___y_2169_ = v___y_2186_;
                    v___y_2170_ = v___y_2188_;
                    v___y_2171_ = v___y_2189_;
                    v___y_2172_ = v___y_2193_;
                    v_port_2173_ = v_port_2192_;
                    v___y_2174_ = v___y_2190_;
                    v___y_2175_ = v___x_2196_;
                    state = 9;
                    continue;
                }
                _ => {
                    v_ipv6_2197_ = leanh::lean_ctor_get(v_host_2191_, 0);
                    leanh::lean_inc_ref(v_ipv6_2197_);
                    leanh::lean_dec_ref_known(v_host_2191_, 1);
                    v___x_2198_ = l_Std_Http_Request_instToStringHead___lam__6___closed__20;
                    v___x_2199_ = lean_uv_ntop_v6(v_ipv6_2197_);
                    leanh::lean_dec_ref(v_ipv6_2197_);
                    v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
                    leanh::lean_dec_ref(v___x_2199_);
                    v___x_2201_ = l_Std_Http_Request_instToStringHead___lam__6___closed__21;
                    v___x_2202_ = lean_string_append(v___x_2200_, v___x_2201_);
                    v___y_2166_ = v___y_2184_;
                    v___y_2167_ = v___y_2185_;
                    v___y_2168_ = v___y_2187_;
                    v___y_2169_ = v___y_2186_;
                    v___y_2170_ = v___y_2188_;
                    v___y_2171_ = v___y_2189_;
                    v___y_2172_ = v___y_2193_;
                    v_port_2173_ = v_port_2192_;
                    v___y_2174_ = v___y_2190_;
                    v___y_2175_ = v___x_2202_;
                    state = 9;
                    continue;
                }
            },
            11 => {
                v___x_2209_ = lean_string_append(v___y_2207_, v___y_2206_);
                leanh::lean_dec_ref(v___y_2206_);
                v___x_2210_ = lean_string_append(v___x_2209_, v___y_2208_);
                leanh::lean_dec_ref(v___y_2208_);
                v___y_2060_ = v___y_2204_;
                v___y_2061_ = v___y_2205_;
                v___y_2062_ = v___x_2210_;
                state = 2;
                continue;
            }
            12 => match leanh::lean_obj_tag(v_port_2212_) {
                0 => {
                    v___x_2217_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2204_ = v___y_2213_;
                    v___y_2205_ = v___y_2214_;
                    v___y_2206_ = v___y_2216_;
                    v___y_2207_ = v___y_2215_;
                    v___y_2208_ = v___x_2217_;
                    state = 11;
                    continue;
                }
                1 => {
                    v___x_2218_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___y_2204_ = v___y_2213_;
                    v___y_2205_ = v___y_2214_;
                    v___y_2206_ = v___y_2216_;
                    v___y_2207_ = v___y_2215_;
                    v___y_2208_ = v___x_2218_;
                    state = 11;
                    continue;
                }
                _ => {
                    v_port_2219_ = leanh::lean_ctor_get_uint16(v_port_2212_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_2212_, 0);
                    v___x_2220_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___x_2221_ = lean_uint16_to_nat(v_port_2219_);
                    v___x_2222_ = l_Nat_reprFast(v___x_2221_);
                    v___x_2223_ = lean_string_append(v___x_2220_, v___x_2222_);
                    leanh::lean_dec_ref(v___x_2222_);
                    v___y_2204_ = v___y_2213_;
                    v___y_2205_ = v___y_2214_;
                    v___y_2206_ = v___y_2216_;
                    v___y_2207_ = v___y_2215_;
                    v___y_2208_ = v___x_2223_;
                    state = 11;
                    continue;
                }
            },
            13 => match leanh::lean_obj_tag(v_host_2225_) {
                0 => {
                    v_name_2230_ = leanh::lean_ctor_get(v_host_2225_, 0);
                    leanh::lean_inc_ref(v_name_2230_);
                    leanh::lean_dec_ref_known(v_host_2225_, 1);
                    v_port_2212_ = v_port_2226_;
                    v___y_2213_ = v___y_2227_;
                    v___y_2214_ = v___y_2228_;
                    v___y_2215_ = v___y_2229_;
                    v___y_2216_ = v_name_2230_;
                    state = 12;
                    continue;
                }
                1 => {
                    v_ipv4_2231_ = leanh::lean_ctor_get(v_host_2225_, 0);
                    leanh::lean_inc_ref(v_ipv4_2231_);
                    leanh::lean_dec_ref_known(v_host_2225_, 1);
                    v___x_2232_ = lean_uv_ntop_v4(v_ipv4_2231_);
                    leanh::lean_dec_ref(v_ipv4_2231_);
                    v_port_2212_ = v_port_2226_;
                    v___y_2213_ = v___y_2227_;
                    v___y_2214_ = v___y_2228_;
                    v___y_2215_ = v___y_2229_;
                    v___y_2216_ = v___x_2232_;
                    state = 12;
                    continue;
                }
                _ => {
                    v_ipv6_2233_ = leanh::lean_ctor_get(v_host_2225_, 0);
                    leanh::lean_inc_ref(v_ipv6_2233_);
                    leanh::lean_dec_ref_known(v_host_2225_, 1);
                    v___x_2234_ = l_Std_Http_Request_instToStringHead___lam__6___closed__20;
                    v___x_2235_ = lean_uv_ntop_v6(v_ipv6_2233_);
                    leanh::lean_dec_ref(v_ipv6_2233_);
                    v___x_2236_ = lean_string_append(v___x_2234_, v___x_2235_);
                    leanh::lean_dec_ref(v___x_2235_);
                    v___x_2237_ = l_Std_Http_Request_instToStringHead___lam__6___closed__21;
                    v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
                    v_port_2212_ = v_port_2226_;
                    v___y_2213_ = v___y_2227_;
                    v___y_2214_ = v___y_2228_;
                    v___y_2215_ = v___y_2229_;
                    v___y_2216_ = v___x_2238_;
                    state = 12;
                    continue;
                }
            },
            14 => {
                v___x_2241_ = l_Std_Http_Request_instToStringHead___lam__6___closed__22;
                leanh::lean_inc_ref(v___y_2240_);
                v___x_2242_ = lean_string_append(v___y_2240_, v___x_2241_);
                match leanh::lean_obj_tag(v_uri_2042_) {
                    0 => {
                        leanh::lean_dec_ref(v___f_2037_);
                        leanh::lean_dec_ref(v___f_2036_);
                        v_path_2243_ = leanh::lean_ctor_get(v_uri_2042_, 0);
                        leanh::lean_inc_ref(v_path_2243_);
                        v_query_2244_ = leanh::lean_ctor_get(v_uri_2042_, 1);
                        leanh::lean_inc(v_query_2244_);
                        leanh::lean_dec_ref_known(v_uri_2042_, 2);
                        v_segments_2245_ = leanh::lean_ctor_get(v_path_2243_, 0);
                        leanh::lean_inc_ref(v_segments_2245_);
                        v_absolute_2246_ = leanh::lean_ctor_get_uint8(
                            v_path_2243_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        leanh::lean_dec_ref(v_path_2243_);
                        v___x_2247_ = l_Std_Http_Request_instToStringHead___lam__6___closed__19;
                        v___x_2248_ = l_Std_Http_Request_instToStringHead___lam__6___closed__10;
                        v_sz_2249_ = lean_array_size(v_segments_2245_);
                        v___x_2250_ = 0usize;
                        v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2248_,
                            v___f_2038_,
                            v_sz_2249_,
                            v___x_2250_,
                            v_segments_2245_,
                        );
                        v___x_2252_ = lean_array_to_list(v___x_2251_);
                        v_result_2253_ = l_String_intercalate(v___x_2247_, v___x_2252_);
                        if v_absolute_2246_ == 0 {
                            v___y_2070_ = v___x_2242_;
                            v___y_2071_ = v___x_2241_;
                            v___y_2072_ = v_query_2244_;
                            v___y_2073_ = v_result_2253_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2254_ = lean_string_append(v___x_2247_, v_result_2253_);
                            leanh::lean_dec_ref(v_result_2253_);
                            v___y_2070_ = v___x_2242_;
                            v___y_2071_ = v___x_2241_;
                            v___y_2072_ = v_query_2244_;
                            v___y_2073_ = v___x_2254_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_dec_ref(v___f_2038_);
                        leanh::lean_dec_ref(v___f_2035_);
                        v_uri_2255_ = leanh::lean_ctor_get(v_uri_2042_, 0);
                        leanh::lean_inc_ref(v_uri_2255_);
                        leanh::lean_dec_ref_known(v_uri_2042_, 1);
                        v_authority_2256_ = leanh::lean_ctor_get(v_uri_2255_, 1);
                        if leanh::lean_obj_tag(v_authority_2256_) == 0 {
                            v_scheme_2257_ = leanh::lean_ctor_get(v_uri_2255_, 0);
                            leanh::lean_inc_ref(v_scheme_2257_);
                            v_path_2258_ = leanh::lean_ctor_get(v_uri_2255_, 2);
                            leanh::lean_inc_ref(v_path_2258_);
                            v_query_2259_ = leanh::lean_ctor_get(v_uri_2255_, 3);
                            leanh::lean_inc_ref(v_query_2259_);
                            v_fragment_2260_ = leanh::lean_ctor_get(v_uri_2255_, 4);
                            leanh::lean_inc(v_fragment_2260_);
                            leanh::lean_dec_ref(v_uri_2255_);
                            v___x_2261_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                            v___y_2134_ = v_scheme_2257_;
                            v___y_2135_ = v_fragment_2260_;
                            v___y_2136_ = v___x_2242_;
                            v___y_2137_ = v_query_2259_;
                            v___y_2138_ = v___x_2241_;
                            v___y_2139_ = v_path_2258_;
                            v___y_2140_ = v___x_2261_;
                            state = 7;
                            continue;
                        } else {
                            v_val_2262_ = leanh::lean_ctor_get(v_authority_2256_, 0);
                            leanh::lean_inc(v_val_2262_);
                            v_scheme_2263_ = leanh::lean_ctor_get(v_uri_2255_, 0);
                            leanh::lean_inc_ref(v_scheme_2263_);
                            v_path_2264_ = leanh::lean_ctor_get(v_uri_2255_, 2);
                            leanh::lean_inc_ref(v_path_2264_);
                            v_query_2265_ = leanh::lean_ctor_get(v_uri_2255_, 3);
                            leanh::lean_inc_ref(v_query_2265_);
                            v_fragment_2266_ = leanh::lean_ctor_get(v_uri_2255_, 4);
                            leanh::lean_inc(v_fragment_2266_);
                            leanh::lean_dec_ref(v_uri_2255_);
                            v_userInfo_2267_ = leanh::lean_ctor_get(v_val_2262_, 0);
                            leanh::lean_inc(v_userInfo_2267_);
                            v_host_2268_ = leanh::lean_ctor_get(v_val_2262_, 1);
                            leanh::lean_inc_ref(v_host_2268_);
                            v_port_2269_ = leanh::lean_ctor_get(v_val_2262_, 2);
                            leanh::lean_inc(v_port_2269_);
                            leanh::lean_dec(v_val_2262_);
                            v___x_2270_ = l_Std_Http_Request_instToStringHead___lam__6___closed__23;
                            if leanh::lean_obj_tag(v_userInfo_2267_) == 0 {
                                v___x_2271_ =
                                    l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                                v___y_2184_ = v___x_2270_;
                                v___y_2185_ = v_scheme_2263_;
                                v___y_2186_ = v___x_2242_;
                                v___y_2187_ = v_fragment_2266_;
                                v___y_2188_ = v_query_2265_;
                                v___y_2189_ = v___x_2241_;
                                v___y_2190_ = v_path_2264_;
                                v_host_2191_ = v_host_2268_;
                                v_port_2192_ = v_port_2269_;
                                v___y_2193_ = v___x_2271_;
                                state = 10;
                                continue;
                            } else {
                                v_val_2272_ = leanh::lean_ctor_get(v_userInfo_2267_, 0);
                                leanh::lean_inc(v_val_2272_);
                                leanh::lean_dec_ref_known(v_userInfo_2267_, 1);
                                v_password_2273_ = leanh::lean_ctor_get(v_val_2272_, 1);
                                if leanh::lean_obj_tag(v_password_2273_) == 0 {
                                    v_username_2274_ = leanh::lean_ctor_get(v_val_2272_, 0);
                                    leanh::lean_inc_ref(v_username_2274_);
                                    leanh::lean_dec(v_val_2272_);
                                    v___x_2275_ = lean_string_from_utf8_unchecked(v_username_2274_);
                                    v___x_2276_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                    v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
                                    v___y_2184_ = v___x_2270_;
                                    v___y_2185_ = v_scheme_2263_;
                                    v___y_2186_ = v___x_2242_;
                                    v___y_2187_ = v_fragment_2266_;
                                    v___y_2188_ = v_query_2265_;
                                    v___y_2189_ = v___x_2241_;
                                    v___y_2190_ = v_path_2264_;
                                    v_host_2191_ = v_host_2268_;
                                    v_port_2192_ = v_port_2269_;
                                    v___y_2193_ = v___x_2277_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc_ref(v_password_2273_);
                                    v_username_2278_ = leanh::lean_ctor_get(v_val_2272_, 0);
                                    leanh::lean_inc_ref(v_username_2278_);
                                    leanh::lean_dec(v_val_2272_);
                                    v_val_2279_ = leanh::lean_ctor_get(v_password_2273_, 0);
                                    leanh::lean_inc(v_val_2279_);
                                    leanh::lean_dec_ref_known(v_password_2273_, 1);
                                    v___x_2280_ = lean_string_from_utf8_unchecked(v_username_2278_);
                                    v___x_2281_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                                    v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
                                    v___x_2283_ = lean_string_from_utf8_unchecked(v_val_2279_);
                                    v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
                                    leanh::lean_dec_ref(v___x_2283_);
                                    v___x_2285_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                    v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
                                    v___y_2184_ = v___x_2270_;
                                    v___y_2185_ = v_scheme_2263_;
                                    v___y_2186_ = v___x_2242_;
                                    v___y_2187_ = v_fragment_2266_;
                                    v___y_2188_ = v_query_2265_;
                                    v___y_2189_ = v___x_2241_;
                                    v___y_2190_ = v_path_2264_;
                                    v_host_2191_ = v_host_2268_;
                                    v_port_2192_ = v_port_2269_;
                                    v___y_2193_ = v___x_2286_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                    2 => {
                        leanh::lean_dec_ref(v___f_2038_);
                        leanh::lean_dec_ref(v___f_2037_);
                        leanh::lean_dec_ref(v___f_2036_);
                        leanh::lean_dec_ref(v___f_2035_);
                        v_authority_2287_ = leanh::lean_ctor_get(v_uri_2042_, 0);
                        leanh::lean_inc_ref(v_authority_2287_);
                        leanh::lean_dec_ref_known(v_uri_2042_, 1);
                        v_userInfo_2288_ = leanh::lean_ctor_get(v_authority_2287_, 0);
                        if leanh::lean_obj_tag(v_userInfo_2288_) == 0 {
                            v_host_2289_ = leanh::lean_ctor_get(v_authority_2287_, 1);
                            leanh::lean_inc_ref(v_host_2289_);
                            v_port_2290_ = leanh::lean_ctor_get(v_authority_2287_, 2);
                            leanh::lean_inc(v_port_2290_);
                            leanh::lean_dec_ref(v_authority_2287_);
                            v___x_2291_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                            v_host_2225_ = v_host_2289_;
                            v_port_2226_ = v_port_2290_;
                            v___y_2227_ = v___x_2242_;
                            v___y_2228_ = v___x_2241_;
                            v___y_2229_ = v___x_2291_;
                            state = 13;
                            continue;
                        } else {
                            v_val_2292_ = leanh::lean_ctor_get(v_userInfo_2288_, 0);
                            leanh::lean_inc(v_val_2292_);
                            v_password_2293_ = leanh::lean_ctor_get(v_val_2292_, 1);
                            if leanh::lean_obj_tag(v_password_2293_) == 0 {
                                v_host_2294_ = leanh::lean_ctor_get(v_authority_2287_, 1);
                                leanh::lean_inc_ref(v_host_2294_);
                                v_port_2295_ = leanh::lean_ctor_get(v_authority_2287_, 2);
                                leanh::lean_inc(v_port_2295_);
                                leanh::lean_dec_ref(v_authority_2287_);
                                v_username_2296_ = leanh::lean_ctor_get(v_val_2292_, 0);
                                leanh::lean_inc_ref(v_username_2296_);
                                leanh::lean_dec(v_val_2292_);
                                v___x_2297_ = lean_string_from_utf8_unchecked(v_username_2296_);
                                v___x_2298_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                v___x_2299_ = lean_string_append(v___x_2297_, v___x_2298_);
                                v_host_2225_ = v_host_2294_;
                                v_port_2226_ = v_port_2295_;
                                v___y_2227_ = v___x_2242_;
                                v___y_2228_ = v___x_2241_;
                                v___y_2229_ = v___x_2299_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_password_2293_);
                                v_host_2300_ = leanh::lean_ctor_get(v_authority_2287_, 1);
                                leanh::lean_inc_ref(v_host_2300_);
                                v_port_2301_ = leanh::lean_ctor_get(v_authority_2287_, 2);
                                leanh::lean_inc(v_port_2301_);
                                leanh::lean_dec_ref(v_authority_2287_);
                                v_username_2302_ = leanh::lean_ctor_get(v_val_2292_, 0);
                                leanh::lean_inc_ref(v_username_2302_);
                                leanh::lean_dec(v_val_2292_);
                                v_val_2303_ = leanh::lean_ctor_get(v_password_2293_, 0);
                                leanh::lean_inc(v_val_2303_);
                                leanh::lean_dec_ref_known(v_password_2293_, 1);
                                v___x_2304_ = lean_string_from_utf8_unchecked(v_username_2302_);
                                v___x_2305_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                                v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
                                v___x_2307_ = lean_string_from_utf8_unchecked(v_val_2303_);
                                v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
                                leanh::lean_dec_ref(v___x_2307_);
                                v___x_2309_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
                                v_host_2225_ = v_host_2300_;
                                v_port_2226_ = v_port_2301_;
                                v___y_2227_ = v___x_2242_;
                                v___y_2228_ = v___x_2241_;
                                v___y_2229_ = v___x_2310_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v___f_2038_);
                        leanh::lean_dec_ref(v___f_2037_);
                        leanh::lean_dec_ref(v___f_2036_);
                        leanh::lean_dec_ref(v___f_2035_);
                        v___x_2311_ = l_Std_Http_Request_instToStringHead___lam__6___closed__25;
                        v___y_2060_ = v___x_2242_;
                        v___y_2061_ = v___x_2241_;
                        v___y_2062_ = v___x_2311_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_instEncodeV11Head___lam__2(
    mut v___x_2360_: *mut leanh::LeanObject,
    mut v___x_2361_: *mut leanh::LeanObject,
    mut v___x_2362_: *mut leanh::LeanObject,
    mut v_name_2363_: *mut leanh::LeanObject,
    mut v___x_2364_: *mut leanh::LeanObject,
    mut v___x_2365_: u32,
    mut v___x_2366_: *mut leanh::LeanObject,
    mut v_it_2367_: *mut leanh::LeanObject,
    mut v_acc_2368_: *mut leanh::LeanObject,
    mut v_hP_2369_: *mut leanh::LeanObject,
    mut v_recur_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_it_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u32 = 0;
    let mut v___x_2394_: u32 = 0;
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: u32 = 0;
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u32 = 0;
    let mut v___x_2401_: u32 = 0;
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u32 = 0;
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2367_) == 0 {
                    v_currPos_2403_ = leanh::lean_ctor_get(v_it_2367_, 0);
                    v_searcher_2404_ = leanh::lean_ctor_get(v_it_2367_, 1);
                    v_isSharedCheck_2426_ = (!leanh::lean_is_exclusive(v_it_2367_)) as u8;
                    if v_isSharedCheck_2426_ == 0 {
                        v___x_2406_ = v_it_2367_;
                        v_isShared_2407_ = v_isSharedCheck_2426_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_2404_);
                        leanh::lean_inc(v_currPos_2403_);
                        leanh::lean_dec(v_it_2367_);
                        v___x_2406_ = leanh::lean_box(0);
                        v_isShared_2407_ = v_isSharedCheck_2426_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_recur_2370_);
                    leanh::lean_dec(v___x_2364_);
                    return v_acc_2368_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_acc_2368_) == 0 {
                    v___x_2374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2374_, 0, v_out_2373_);
                    v___x_2375_ = leanh::lean_apply_4(
                        v_recur_2370_,
                        v_it_2372_,
                        v___x_2374_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_2375_;
                } else {
                    v_val_2376_ = leanh::lean_ctor_get(v_acc_2368_, 0);
                    v_isSharedCheck_2387_ = (!leanh::lean_is_exclusive(v_acc_2368_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2378_ = v_acc_2368_;
                        v_isShared_2379_ = v_isSharedCheck_2387_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2376_);
                        leanh::lean_dec(v_acc_2368_);
                        v___x_2378_ = leanh::lean_box(0);
                        v_isShared_2379_ = v_isSharedCheck_2387_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2380_ = lean_string_utf8_extract(v___x_2360_, v___x_2361_, v___x_2362_);
                v___x_2381_ = lean_string_append(v_val_2376_, v___x_2380_);
                leanh::lean_dec_ref(v___x_2380_);
                v___x_2382_ = lean_string_append(v___x_2381_, v_out_2373_);
                leanh::lean_dec_ref(v_out_2373_);
                if v_isShared_2379_ == 0 {
                    leanh::lean_ctor_set(v___x_2378_, 0, v___x_2382_);
                    v___x_2384_ = v___x_2378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2382_);
                    v___x_2384_ = v_reuseFailAlloc_2386_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2385_ = leanh::lean_apply_4(
                    v_recur_2370_,
                    v_it_2372_,
                    v___x_2384_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_2385_;
            }
            4 => {
                v___x_2392_ = lean_string_utf8_extract(
                    v_name_2363_,
                    v_startInclusive_2390_,
                    v_endExclusive_2391_,
                );
                leanh::lean_dec(v_endExclusive_2391_);
                leanh::lean_dec(v_startInclusive_2390_);
                v___x_2393_ = lean_string_utf8_get(v___x_2392_, v___x_2361_);
                v___x_2394_ = 97;
                v___x_2395_ = lean_uint32_dec_le(v___x_2394_, v___x_2393_);
                if v___x_2395_ == 0 {
                    v___x_2396_ = lean_string_utf8_set(v___x_2392_, v___x_2361_, v___x_2393_);
                    v_it_2372_ = v_it_2389_;
                    v_out_2373_ = v___x_2396_;
                    state = 1;
                    continue;
                } else {
                    v___x_2397_ = 122;
                    v___x_2398_ = lean_uint32_dec_le(v___x_2393_, v___x_2397_);
                    if v___x_2398_ == 0 {
                        v___x_2399_ = lean_string_utf8_set(v___x_2392_, v___x_2361_, v___x_2393_);
                        v_it_2372_ = v_it_2389_;
                        v_out_2373_ = v___x_2399_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2400_ = 4294967264;
                        v___x_2401_ = lean_uint32_add(v___x_2393_, v___x_2400_);
                        v___x_2402_ = lean_string_utf8_set(v___x_2392_, v___x_2361_, v___x_2401_);
                        v_it_2372_ = v_it_2389_;
                        v_out_2373_ = v___x_2402_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2408_ = lean_nat_dec_eq(v_searcher_2404_, v___x_2364_);
                if v___x_2408_ == 0 {
                    leanh::lean_dec(v___x_2364_);
                    v___x_2409_ = lean_string_utf8_get_fast(v_name_2363_, v_searcher_2404_);
                    v___x_2410_ = lean_uint32_dec_eq(v___x_2409_, v___x_2365_);
                    if v___x_2410_ == 0 {
                        v___x_2411_ = lean_string_utf8_next_fast(v_name_2363_, v_searcher_2404_);
                        leanh::lean_dec(v_searcher_2404_);
                        if v_isShared_2407_ == 0 {
                            leanh::lean_ctor_set(v___x_2406_, 1, v___x_2411_);
                            v___x_2413_ = v___x_2406_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2415_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_currPos_2403_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2411_);
                            v___x_2413_ = v_reuseFailAlloc_2415_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_2416_ = lean_string_utf8_next_fast(v_name_2363_, v_searcher_2404_);
                        v___x_2417_ = lean_nat_sub(v___x_2416_, v_searcher_2404_);
                        v___x_2418_ = lean_nat_add(v_searcher_2404_, v___x_2417_);
                        leanh::lean_dec(v___x_2417_);
                        v_slice_2419_ = l_String_Slice_subslice_x21(
                            v___x_2366_,
                            v_currPos_2403_,
                            v_searcher_2404_,
                        );
                        leanh::lean_inc(v___x_2418_);
                        if v_isShared_2407_ == 0 {
                            leanh::lean_ctor_set(v___x_2406_, 1, v___x_2418_);
                            leanh::lean_ctor_set(v___x_2406_, 0, v___x_2418_);
                            v_nextIt_2421_ = v___x_2406_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2424_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2418_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 1, v___x_2418_);
                            v_nextIt_2421_ = v_reuseFailAlloc_2424_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2406_);
                    leanh::lean_dec(v_searcher_2404_);
                    v___x_2425_ = leanh::lean_box(1);
                    v_it_2389_ = v___x_2425_;
                    v_startInclusive_2390_ = v_currPos_2403_;
                    v_endExclusive_2391_ = v___x_2364_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2414_ = leanh::lean_apply_4(
                    v_recur_2370_,
                    v___x_2413_,
                    v_acc_2368_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_2414_;
            }
            7 => {
                v_startInclusive_2422_ = leanh::lean_ctor_get(v_slice_2419_, 0);
                leanh::lean_inc(v_startInclusive_2422_);
                v_endExclusive_2423_ = leanh::lean_ctor_get(v_slice_2419_, 1);
                leanh::lean_inc(v_endExclusive_2423_);
                leanh::lean_dec_ref(v_slice_2419_);
                v_it_2389_ = v_nextIt_2421_;
                v_startInclusive_2390_ = v_startInclusive_2422_;
                v_endExclusive_2391_ = v_endExclusive_2423_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_instEncodeV11Head___lam__2___boxed(
    mut v___x_2427_: *mut leanh::LeanObject,
    mut v___x_2428_: *mut leanh::LeanObject,
    mut v___x_2429_: *mut leanh::LeanObject,
    mut v_name_2430_: *mut leanh::LeanObject,
    mut v___x_2431_: *mut leanh::LeanObject,
    mut v___x_2432_: *mut leanh::LeanObject,
    mut v___x_2433_: *mut leanh::LeanObject,
    mut v_it_2434_: *mut leanh::LeanObject,
    mut v_acc_2435_: *mut leanh::LeanObject,
    mut v_hP_2436_: *mut leanh::LeanObject,
    mut v_recur_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3141__boxed_2438_: u32 = 0;
    let mut v_res_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3141__boxed_2438_ = leanh::lean_unbox_uint32(v___x_2432_);
    leanh::lean_dec(v___x_2432_);
    v_res_2439_ = l_Std_Http_Request_instEncodeV11Head___lam__2(
        v___x_2427_,
        v___x_2428_,
        v___x_2429_,
        v_name_2430_,
        v___x_2431_,
        v___x_3141__boxed_2438_,
        v___x_2433_,
        v_it_2434_,
        v_acc_2435_,
        v_hP_2436_,
        v_recur_2437_,
    );
    leanh::lean_dec_ref(v___x_2433_);
    leanh::lean_dec_ref(v_name_2430_);
    leanh::lean_dec(v___x_2429_);
    leanh::lean_dec(v___x_2428_);
    leanh::lean_dec_ref(v___x_2427_);
    return v_res_2439_;
}
pub unsafe fn l_Std_Http_Request_instEncodeV11Head___lam__0(
    mut v_buf_2440_: *mut leanh::LeanObject,
    mut v_name_2441_: *mut leanh::LeanObject,
    mut v_value_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v___f_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2463_ = l_Std_Http_Request_instToStringHead___lam__3___closed__1;
                v___x_2464_ = leanh::lean_unsigned_to_nat(0);
                v___x_2465_ = lean_string_utf8_byte_size(v_name_2441_);
                leanh::lean_inc_ref(v_name_2441_);
                v___x_2466_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2466_, 0, v_name_2441_);
                leanh::lean_ctor_set(v___x_2466_, 1, v___x_2464_);
                leanh::lean_ctor_set(v___x_2466_, 2, v___x_2465_);
                leanh::lean_inc_ref(v___x_2466_);
                v_it_2467_ = l_String_Slice_splitToSubslice___redArg(v___x_2466_, v___f_2463_);
                v___x_2468_ = l_Std_Http_Request_instToStringHead___lam__3___closed__2;
                v___x_2469_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instToStringHead___lam__3___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instToStringHead___lam__3___closed__3_once
                    ),
                    _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3,
                );
                v___x_2470_ = l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1;
                v___f_2471_ = leanh::lean_alloc_closure(
                    l_Std_Http_Request_instEncodeV11Head___lam__2___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_2471_, 0, v___x_2468_);
                leanh::lean_closure_set(v___f_2471_, 1, v___x_2464_);
                leanh::lean_closure_set(v___f_2471_, 2, v___x_2469_);
                leanh::lean_closure_set(v___f_2471_, 3, v_name_2441_);
                leanh::lean_closure_set(v___f_2471_, 4, v___x_2465_);
                leanh::lean_closure_set(v___f_2471_, 5, v___x_2470_);
                leanh::lean_closure_set(v___f_2471_, 6, v___x_2466_);
                v___x_2472_ = leanh::lean_box(0);
                v___x_2473_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2471_,
                    v_it_2467_,
                    v___x_2472_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2473_) == 0 {
                    v___x_2474_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2444_ = v___x_2474_;
                    state = 1;
                    continue;
                } else {
                    v_val_2475_ = leanh::lean_ctor_get(v___x_2473_, 0);
                    leanh::lean_inc(v_val_2475_);
                    leanh::lean_dec_ref_known(v___x_2473_, 1);
                    v___y_2444_ = v_val_2475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_2445_ = leanh::lean_ctor_get(v_buf_2440_, 0);
                v_size_2446_ = leanh::lean_ctor_get(v_buf_2440_, 1);
                v_isSharedCheck_2462_ = (!leanh::lean_is_exclusive(v_buf_2440_)) as u8;
                if v_isSharedCheck_2462_ == 0 {
                    v___x_2448_ = v_buf_2440_;
                    v_isShared_2449_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_size_2446_);
                    leanh::lean_inc(v_data_2445_);
                    leanh::lean_dec(v_buf_2440_);
                    v___x_2448_ = leanh::lean_box(0);
                    v_isShared_2449_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2450_ = l_Std_Http_Request_instToStringHead___lam__3___closed__0;
                v___x_2451_ = lean_string_append(v___y_2444_, v___x_2450_);
                v___x_2452_ = lean_string_append(v___x_2451_, v_value_2442_);
                v___x_2453_ = l_Std_Http_Request_instToStringHead___lam__6___closed__0;
                v___x_2454_ = lean_string_append(v___x_2452_, v___x_2453_);
                v___x_2455_ = lean_string_to_utf8(v___x_2454_);
                leanh::lean_dec_ref(v___x_2454_);
                leanh::lean_inc_ref(v___x_2455_);
                v___x_2456_ = lean_array_push(v_data_2445_, v___x_2455_);
                v___x_2457_ = lean_byte_array_size(v___x_2455_);
                leanh::lean_dec_ref(v___x_2455_);
                v___x_2458_ = lean_nat_add(v_size_2446_, v___x_2457_);
                leanh::lean_dec(v_size_2446_);
                if v_isShared_2449_ == 0 {
                    leanh::lean_ctor_set(v___x_2448_, 1, v___x_2458_);
                    leanh::lean_ctor_set(v___x_2448_, 0, v___x_2456_);
                    v___x_2460_ = v___x_2448_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2458_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(
    mut v_buf_2476_: *mut leanh::LeanObject,
    mut v_name_2477_: *mut leanh::LeanObject,
    mut v_value_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ =
        l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_2476_, v_name_2477_, v_value_2478_);
    leanh::lean_dec_ref(v_value_2478_);
    return v_res_2479_;
}
pub unsafe fn _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = l_Std_Http_Request_instToStringHead___lam__6___closed__0;
    v___x_2481_ = lean_string_to_utf8(v___x_2480_);
    return v___x_2481_;
}
pub unsafe fn _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once),
        _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0,
    );
    v___x_2483_ = lean_byte_array_size(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2() -> u8 {
    let mut v___x_2484_: u32 = 0;
    let mut v___x_2485_: u8 = 0;
    v___x_2484_ = 32;
    v___x_2485_ = lean_uint32_to_uint8(v___x_2484_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2_once),
        _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2,
    );
    v___x_2487_ = leanh::lean_unsigned_to_nat(1);
    v___x_2488_ = lean_mk_empty_array_with_capacity(v___x_2487_);
    v___x_2489_ = leanh::lean_box((v___x_2486_) as usize);
    v___x_2490_ = lean_array_push(v___x_2488_, v___x_2489_);
    v___x_2491_ = lean_byte_array_mk(v___x_2490_);
    return v___x_2491_;
}
pub unsafe fn _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once),
        _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3,
    );
    v___x_2493_ = lean_byte_array_size(v___x_2492_);
    return v___x_2493_;
}
pub unsafe fn l_Std_Http_Request_instEncodeV11Head___lam__4(
    mut v___f_2494_: *mut leanh::LeanObject,
    mut v___f_2495_: *mut leanh::LeanObject,
    mut v___f_2496_: *mut leanh::LeanObject,
    mut v___f_2497_: *mut leanh::LeanObject,
    mut v___f_2498_: *mut leanh::LeanObject,
    mut v_buffer_2499_: *mut leanh::LeanObject,
    mut v_req_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_2501_: u8 = 0;
    let mut v_version_2502_: u8 = 0;
    let mut v_uri_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v___y_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2566_: u16 = 0;
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_2652_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2692_: u16 = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_2753_: u8 = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2756_: usize = 0;
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_2501_ = leanh::lean_ctor_get_uint8(
                    v_req_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_2502_ = leanh::lean_ctor_get_uint8(
                    v_req_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_2503_ = leanh::lean_ctor_get(v_req_2500_, 0);
                leanh::lean_inc(v_uri_2503_);
                v_headers_2504_ = leanh::lean_ctor_get(v_req_2500_, 1);
                leanh::lean_inc_ref(v_headers_2504_);
                leanh::lean_dec_ref(v_req_2500_);
                match v_method_2501_ {
                    0 => {
                        v___x_2819_ = l_Std_Http_Request_instToStringHead___lam__6___closed__26;
                        v___y_2739_ = v___x_2819_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_2820_ = l_Std_Http_Request_instToStringHead___lam__6___closed__27;
                        v___y_2739_ = v___x_2820_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_2821_ = l_Std_Http_Request_instToStringHead___lam__6___closed__28;
                        v___y_2739_ = v___x_2821_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_2822_ = l_Std_Http_Request_instToStringHead___lam__6___closed__29;
                        v___y_2739_ = v___x_2822_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_2823_ = l_Std_Http_Request_instToStringHead___lam__6___closed__30;
                        v___y_2739_ = v___x_2823_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_2824_ = l_Std_Http_Request_instToStringHead___lam__6___closed__31;
                        v___y_2739_ = v___x_2824_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_2825_ = l_Std_Http_Request_instToStringHead___lam__6___closed__32;
                        v___y_2739_ = v___x_2825_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_2826_ = l_Std_Http_Request_instToStringHead___lam__6___closed__33;
                        v___y_2739_ = v___x_2826_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_2827_ = l_Std_Http_Request_instToStringHead___lam__6___closed__34;
                        v___y_2739_ = v___x_2827_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_2828_ = l_Std_Http_Request_instToStringHead___lam__6___closed__35;
                        v___y_2739_ = v___x_2828_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_2829_ = l_Std_Http_Request_instToStringHead___lam__6___closed__36;
                        v___y_2739_ = v___x_2829_;
                        state = 16;
                        continue;
                    }
                    11 => {
                        v___x_2830_ = l_Std_Http_Request_instToStringHead___lam__6___closed__37;
                        v___y_2739_ = v___x_2830_;
                        state = 16;
                        continue;
                    }
                    12 => {
                        v___x_2831_ = l_Std_Http_Request_instToStringHead___lam__6___closed__38;
                        v___y_2739_ = v___x_2831_;
                        state = 16;
                        continue;
                    }
                    13 => {
                        v___x_2832_ = l_Std_Http_Request_instToStringHead___lam__6___closed__39;
                        v___y_2739_ = v___x_2832_;
                        state = 16;
                        continue;
                    }
                    14 => {
                        v___x_2833_ = l_Std_Http_Request_instToStringHead___lam__6___closed__40;
                        v___y_2739_ = v___x_2833_;
                        state = 16;
                        continue;
                    }
                    15 => {
                        v___x_2834_ = l_Std_Http_Request_instToStringHead___lam__6___closed__41;
                        v___y_2739_ = v___x_2834_;
                        state = 16;
                        continue;
                    }
                    16 => {
                        v___x_2835_ = l_Std_Http_Request_instToStringHead___lam__6___closed__42;
                        v___y_2739_ = v___x_2835_;
                        state = 16;
                        continue;
                    }
                    17 => {
                        v___x_2836_ = l_Std_Http_Request_instToStringHead___lam__6___closed__43;
                        v___y_2739_ = v___x_2836_;
                        state = 16;
                        continue;
                    }
                    18 => {
                        v___x_2837_ = l_Std_Http_Request_instToStringHead___lam__6___closed__44;
                        v___y_2739_ = v___x_2837_;
                        state = 16;
                        continue;
                    }
                    19 => {
                        v___x_2838_ = l_Std_Http_Request_instToStringHead___lam__6___closed__45;
                        v___y_2739_ = v___x_2838_;
                        state = 16;
                        continue;
                    }
                    20 => {
                        v___x_2839_ = l_Std_Http_Request_instToStringHead___lam__6___closed__46;
                        v___y_2739_ = v___x_2839_;
                        state = 16;
                        continue;
                    }
                    21 => {
                        v___x_2840_ = l_Std_Http_Request_instToStringHead___lam__6___closed__47;
                        v___y_2739_ = v___x_2840_;
                        state = 16;
                        continue;
                    }
                    22 => {
                        v___x_2841_ = l_Std_Http_Request_instToStringHead___lam__6___closed__48;
                        v___y_2739_ = v___x_2841_;
                        state = 16;
                        continue;
                    }
                    23 => {
                        v___x_2842_ = l_Std_Http_Request_instToStringHead___lam__6___closed__49;
                        v___y_2739_ = v___x_2842_;
                        state = 16;
                        continue;
                    }
                    24 => {
                        v___x_2843_ = l_Std_Http_Request_instToStringHead___lam__6___closed__50;
                        v___y_2739_ = v___x_2843_;
                        state = 16;
                        continue;
                    }
                    25 => {
                        v___x_2844_ = l_Std_Http_Request_instToStringHead___lam__6___closed__51;
                        v___y_2739_ = v___x_2844_;
                        state = 16;
                        continue;
                    }
                    26 => {
                        v___x_2845_ = l_Std_Http_Request_instToStringHead___lam__6___closed__52;
                        v___y_2739_ = v___x_2845_;
                        state = 16;
                        continue;
                    }
                    27 => {
                        v___x_2846_ = l_Std_Http_Request_instToStringHead___lam__6___closed__53;
                        v___y_2739_ = v___x_2846_;
                        state = 16;
                        continue;
                    }
                    28 => {
                        v___x_2847_ = l_Std_Http_Request_instToStringHead___lam__6___closed__54;
                        v___y_2739_ = v___x_2847_;
                        state = 16;
                        continue;
                    }
                    29 => {
                        v___x_2848_ = l_Std_Http_Request_instToStringHead___lam__6___closed__55;
                        v___y_2739_ = v___x_2848_;
                        state = 16;
                        continue;
                    }
                    30 => {
                        v___x_2849_ = l_Std_Http_Request_instToStringHead___lam__6___closed__56;
                        v___y_2739_ = v___x_2849_;
                        state = 16;
                        continue;
                    }
                    31 => {
                        v___x_2850_ = l_Std_Http_Request_instToStringHead___lam__6___closed__57;
                        v___y_2739_ = v___x_2850_;
                        state = 16;
                        continue;
                    }
                    32 => {
                        v___x_2851_ = l_Std_Http_Request_instToStringHead___lam__6___closed__58;
                        v___y_2739_ = v___x_2851_;
                        state = 16;
                        continue;
                    }
                    33 => {
                        v___x_2852_ = l_Std_Http_Request_instToStringHead___lam__6___closed__59;
                        v___y_2739_ = v___x_2852_;
                        state = 16;
                        continue;
                    }
                    34 => {
                        v___x_2853_ = l_Std_Http_Request_instToStringHead___lam__6___closed__60;
                        v___y_2739_ = v___x_2853_;
                        state = 16;
                        continue;
                    }
                    35 => {
                        v___x_2854_ = l_Std_Http_Request_instToStringHead___lam__6___closed__61;
                        v___y_2739_ = v___x_2854_;
                        state = 16;
                        continue;
                    }
                    36 => {
                        v___x_2855_ = l_Std_Http_Request_instToStringHead___lam__6___closed__62;
                        v___y_2739_ = v___x_2855_;
                        state = 16;
                        continue;
                    }
                    37 => {
                        v___x_2856_ = l_Std_Http_Request_instToStringHead___lam__6___closed__63;
                        v___y_2739_ = v___x_2856_;
                        state = 16;
                        continue;
                    }
                    38 => {
                        v___x_2857_ = l_Std_Http_Request_instToStringHead___lam__6___closed__64;
                        v___y_2739_ = v___x_2857_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_2858_ = l_Std_Http_Request_instToStringHead___lam__6___closed__65;
                        v___y_2739_ = v___x_2858_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2509_ = lean_string_to_utf8(v___y_2508_);
                leanh::lean_inc_ref(v___x_2509_);
                v___x_2510_ = lean_array_push(v___y_2506_, v___x_2509_);
                v___x_2511_ = lean_byte_array_size(v___x_2509_);
                leanh::lean_dec_ref(v___x_2509_);
                v___x_2512_ = lean_nat_add(v___y_2507_, v___x_2511_);
                leanh::lean_dec(v___y_2507_);
                v___x_2513_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once
                    ),
                    _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0,
                );
                v___x_2514_ = lean_array_push(v___x_2510_, v___x_2513_);
                v___x_2515_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1_once
                    ),
                    _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1,
                );
                v___x_2516_ = lean_nat_add(v___x_2512_, v___x_2515_);
                leanh::lean_dec(v___x_2512_);
                v_buffer_2517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_buffer_2517_, 0, v___x_2514_);
                leanh::lean_ctor_set(v_buffer_2517_, 1, v___x_2516_);
                v_buffer_2518_ =
                    l_Std_Http_Headers_fold___redArg(v_headers_2504_, v_buffer_2517_, v___f_2494_);
                leanh::lean_dec_ref(v_headers_2504_);
                v_data_2519_ = leanh::lean_ctor_get(v_buffer_2518_, 0);
                v_size_2520_ = leanh::lean_ctor_get(v_buffer_2518_, 1);
                v_isSharedCheck_2529_ = (!leanh::lean_is_exclusive(v_buffer_2518_)) as u8;
                if v_isSharedCheck_2529_ == 0 {
                    v___x_2522_ = v_buffer_2518_;
                    v_isShared_2523_ = v_isSharedCheck_2529_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_size_2520_);
                    leanh::lean_inc(v_data_2519_);
                    leanh::lean_dec(v_buffer_2518_);
                    v___x_2522_ = leanh::lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2524_ = lean_array_push(v_data_2519_, v___x_2513_);
                v___x_2525_ = lean_nat_add(v_size_2520_, v___x_2515_);
                leanh::lean_dec(v_size_2520_);
                if v_isShared_2523_ == 0 {
                    leanh::lean_ctor_set(v___x_2522_, 1, v___x_2525_);
                    leanh::lean_ctor_set(v___x_2522_, 0, v___x_2524_);
                    v___x_2527_ = v___x_2522_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2525_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2527_;
            }
            4 => {
                v___x_2536_ = lean_string_to_utf8(v___y_2535_);
                leanh::lean_dec_ref(v___y_2535_);
                leanh::lean_inc_ref(v___x_2536_);
                v___x_2537_ = lean_array_push(v___y_2532_, v___x_2536_);
                v___x_2538_ = lean_byte_array_size(v___x_2536_);
                leanh::lean_dec_ref(v___x_2536_);
                v___x_2539_ = lean_nat_add(v___y_2534_, v___x_2538_);
                leanh::lean_dec(v___y_2534_);
                v___x_2540_ = lean_array_push(v___x_2537_, v___y_2533_);
                v___x_2541_ = lean_nat_add(v___x_2539_, v___y_2531_);
                leanh::lean_dec(v___x_2539_);
                match v_version_2502_ {
                    0 => {
                        v___x_2542_ = l_Std_Http_Request_instToStringHead___lam__6___closed__11;
                        v___y_2506_ = v___x_2540_;
                        v___y_2507_ = v___x_2541_;
                        v___y_2508_ = v___x_2542_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2543_ = l_Std_Http_Request_instToStringHead___lam__6___closed__12;
                        v___y_2506_ = v___x_2540_;
                        v___y_2507_ = v___x_2541_;
                        v___y_2508_ = v___x_2543_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_2544_ = l_Std_Http_Request_instToStringHead___lam__6___closed__13;
                        v___y_2506_ = v___x_2540_;
                        v___y_2507_ = v___x_2541_;
                        v___y_2508_ = v___x_2544_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2545_ = l_Std_Http_Request_instToStringHead___lam__6___closed__14;
                        v___y_2506_ = v___x_2540_;
                        v___y_2507_ = v___x_2541_;
                        v___y_2508_ = v___x_2545_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2554_ = lean_string_append(v___y_2552_, v___y_2551_);
                leanh::lean_dec_ref(v___y_2551_);
                v___x_2555_ = lean_string_append(v___x_2554_, v___y_2553_);
                leanh::lean_dec_ref(v___y_2553_);
                v___y_2531_ = v___y_2547_;
                v___y_2532_ = v___y_2548_;
                v___y_2533_ = v___y_2549_;
                v___y_2534_ = v___y_2550_;
                v___y_2535_ = v___x_2555_;
                state = 4;
                continue;
            }
            6 => match leanh::lean_obj_tag(v_port_2558_) {
                0 => {
                    v___x_2564_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2547_ = v___y_2557_;
                    v___y_2548_ = v___y_2559_;
                    v___y_2549_ = v___y_2560_;
                    v___y_2550_ = v___y_2561_;
                    v___y_2551_ = v___y_2563_;
                    v___y_2552_ = v___y_2562_;
                    v___y_2553_ = v___x_2564_;
                    state = 5;
                    continue;
                }
                1 => {
                    v___x_2565_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___y_2547_ = v___y_2557_;
                    v___y_2548_ = v___y_2559_;
                    v___y_2549_ = v___y_2560_;
                    v___y_2550_ = v___y_2561_;
                    v___y_2551_ = v___y_2563_;
                    v___y_2552_ = v___y_2562_;
                    v___y_2553_ = v___x_2565_;
                    state = 5;
                    continue;
                }
                _ => {
                    v_port_2566_ = leanh::lean_ctor_get_uint16(v_port_2558_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_2558_, 0);
                    v___x_2567_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___x_2568_ = lean_uint16_to_nat(v_port_2566_);
                    v___x_2569_ = l_Nat_reprFast(v___x_2568_);
                    v___x_2570_ = lean_string_append(v___x_2567_, v___x_2569_);
                    leanh::lean_dec_ref(v___x_2569_);
                    v___y_2547_ = v___y_2557_;
                    v___y_2548_ = v___y_2559_;
                    v___y_2549_ = v___y_2560_;
                    v___y_2550_ = v___y_2561_;
                    v___y_2551_ = v___y_2563_;
                    v___y_2552_ = v___y_2562_;
                    v___y_2553_ = v___x_2570_;
                    state = 5;
                    continue;
                }
            },
            7 => match leanh::lean_obj_tag(v_host_2573_) {
                0 => {
                    v_name_2579_ = leanh::lean_ctor_get(v_host_2573_, 0);
                    leanh::lean_inc_ref(v_name_2579_);
                    leanh::lean_dec_ref_known(v_host_2573_, 1);
                    v___y_2557_ = v___y_2572_;
                    v_port_2558_ = v_port_2574_;
                    v___y_2559_ = v___y_2575_;
                    v___y_2560_ = v___y_2576_;
                    v___y_2561_ = v___y_2577_;
                    v___y_2562_ = v___y_2578_;
                    v___y_2563_ = v_name_2579_;
                    state = 6;
                    continue;
                }
                1 => {
                    v_ipv4_2580_ = leanh::lean_ctor_get(v_host_2573_, 0);
                    leanh::lean_inc_ref(v_ipv4_2580_);
                    leanh::lean_dec_ref_known(v_host_2573_, 1);
                    v___x_2581_ = lean_uv_ntop_v4(v_ipv4_2580_);
                    leanh::lean_dec_ref(v_ipv4_2580_);
                    v___y_2557_ = v___y_2572_;
                    v_port_2558_ = v_port_2574_;
                    v___y_2559_ = v___y_2575_;
                    v___y_2560_ = v___y_2576_;
                    v___y_2561_ = v___y_2577_;
                    v___y_2562_ = v___y_2578_;
                    v___y_2563_ = v___x_2581_;
                    state = 6;
                    continue;
                }
                _ => {
                    v_ipv6_2582_ = leanh::lean_ctor_get(v_host_2573_, 0);
                    leanh::lean_inc_ref(v_ipv6_2582_);
                    leanh::lean_dec_ref_known(v_host_2573_, 1);
                    v___x_2583_ = l_Std_Http_Request_instToStringHead___lam__6___closed__20;
                    v___x_2584_ = lean_uv_ntop_v6(v_ipv6_2582_);
                    leanh::lean_dec_ref(v_ipv6_2582_);
                    v___x_2585_ = lean_string_append(v___x_2583_, v___x_2584_);
                    leanh::lean_dec_ref(v___x_2584_);
                    v___x_2586_ = l_Std_Http_Request_instToStringHead___lam__6___closed__21;
                    v___x_2587_ = lean_string_append(v___x_2585_, v___x_2586_);
                    v___y_2557_ = v___y_2572_;
                    v_port_2558_ = v_port_2574_;
                    v___y_2559_ = v___y_2575_;
                    v___y_2560_ = v___y_2576_;
                    v___y_2561_ = v___y_2577_;
                    v___y_2562_ = v___y_2578_;
                    v___y_2563_ = v___x_2587_;
                    state = 6;
                    continue;
                }
            },
            8 => {
                v___x_2598_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                v___x_2599_ = lean_string_append(v___y_2592_, v___x_2598_);
                v___x_2600_ = lean_string_append(v___x_2599_, v___y_2591_);
                leanh::lean_dec_ref(v___y_2591_);
                v___x_2601_ = lean_string_append(v___x_2600_, v___y_2590_);
                leanh::lean_dec_ref(v___y_2590_);
                v___x_2602_ = lean_string_append(v___x_2601_, v___y_2594_);
                leanh::lean_dec_ref(v___y_2594_);
                v___x_2603_ = lean_string_append(v___x_2602_, v___y_2597_);
                leanh::lean_dec_ref(v___y_2597_);
                v___y_2531_ = v___y_2589_;
                v___y_2532_ = v___y_2593_;
                v___y_2533_ = v___y_2595_;
                v___y_2534_ = v___y_2596_;
                v___y_2535_ = v___x_2603_;
                state = 4;
                continue;
            }
            9 => {
                if leanh::lean_obj_tag(v___y_2610_) == 0 {
                    v___x_2614_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2589_ = v___y_2606_;
                    v___y_2590_ = v___y_2605_;
                    v___y_2591_ = v___y_2608_;
                    v___y_2592_ = v___y_2607_;
                    v___y_2593_ = v___y_2609_;
                    v___y_2594_ = v___y_2613_;
                    v___y_2595_ = v___y_2611_;
                    v___y_2596_ = v___y_2612_;
                    v___y_2597_ = v___x_2614_;
                    state = 8;
                    continue;
                } else {
                    v_val_2615_ = leanh::lean_ctor_get(v___y_2610_, 0);
                    leanh::lean_inc(v_val_2615_);
                    leanh::lean_dec_ref_known(v___y_2610_, 1);
                    v___x_2616_ = l_Std_Http_Request_instToStringHead___lam__6___closed__18;
                    v___x_2617_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2615_);
                    leanh::lean_dec(v_val_2615_);
                    v___x_2618_ = lean_string_from_utf8_unchecked(v___x_2617_);
                    v___x_2619_ = lean_string_append(v___x_2616_, v___x_2618_);
                    leanh::lean_dec_ref(v___x_2618_);
                    v___y_2589_ = v___y_2606_;
                    v___y_2590_ = v___y_2605_;
                    v___y_2591_ = v___y_2608_;
                    v___y_2592_ = v___y_2607_;
                    v___y_2593_ = v___y_2609_;
                    v___y_2594_ = v___y_2613_;
                    v___y_2595_ = v___y_2611_;
                    v___y_2596_ = v___y_2612_;
                    v___y_2597_ = v___x_2619_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2630_ = lean_array_get_size(v___y_2628_);
                v___x_2631_ = leanh::lean_unsigned_to_nat(0);
                v___x_2632_ = lean_nat_dec_eq(v___x_2630_, v___x_2631_);
                if v___x_2632_ == 0 {
                    v___x_2633_ = lean_array_to_list(v___y_2628_);
                    v___x_2634_ = leanh::lean_box(0);
                    v_encodedParams_2635_ =
                        l_List_mapTR_loop___redArg(v___f_2495_, v___x_2633_, v___x_2634_);
                    v___x_2636_ = l_Std_Http_Request_instToStringHead___lam__6___closed__15;
                    v___x_2637_ = l_Std_Http_Request_instToStringHead___lam__6___closed__16;
                    v___x_2638_ = l_String_intercalate(v___x_2637_, v_encodedParams_2635_);
                    v___x_2639_ = lean_string_append(v___x_2636_, v___x_2638_);
                    leanh::lean_dec_ref(v___x_2638_);
                    v___y_2605_ = v___y_2629_;
                    v___y_2606_ = v___y_2621_;
                    v___y_2607_ = v___y_2623_;
                    v___y_2608_ = v___y_2622_;
                    v___y_2609_ = v___y_2624_;
                    v___y_2610_ = v___y_2626_;
                    v___y_2611_ = v___y_2625_;
                    v___y_2612_ = v___y_2627_;
                    v___y_2613_ = v___x_2639_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_2628_);
                    leanh::lean_dec_ref(v___f_2495_);
                    v___x_2640_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2605_ = v___y_2629_;
                    v___y_2606_ = v___y_2621_;
                    v___y_2607_ = v___y_2623_;
                    v___y_2608_ = v___y_2622_;
                    v___y_2609_ = v___y_2624_;
                    v___y_2610_ = v___y_2626_;
                    v___y_2611_ = v___y_2625_;
                    v___y_2612_ = v___y_2627_;
                    v___y_2613_ = v___x_2640_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_segments_2651_ = leanh::lean_ctor_get(v___y_2644_, 0);
                leanh::lean_inc_ref(v_segments_2651_);
                v_absolute_2652_ = leanh::lean_ctor_get_uint8(
                    v___y_2644_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v___y_2644_);
                v___x_2653_ = l_Std_Http_Request_instToStringHead___lam__6___closed__19;
                v___x_2654_ = l_Std_Http_Request_instToStringHead___lam__6___closed__10;
                v_sz_2655_ = lean_array_size(v_segments_2651_);
                v___x_2656_ = 0usize;
                v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2654_,
                    v___f_2496_,
                    v_sz_2655_,
                    v___x_2656_,
                    v_segments_2651_,
                );
                v___x_2658_ = lean_array_to_list(v___x_2657_);
                v_result_2659_ = l_String_intercalate(v___x_2653_, v___x_2658_);
                if v_absolute_2652_ == 0 {
                    v___y_2621_ = v___y_2642_;
                    v___y_2622_ = v___y_2650_;
                    v___y_2623_ = v___y_2643_;
                    v___y_2624_ = v___y_2645_;
                    v___y_2625_ = v___y_2647_;
                    v___y_2626_ = v___y_2646_;
                    v___y_2627_ = v___y_2648_;
                    v___y_2628_ = v___y_2649_;
                    v___y_2629_ = v_result_2659_;
                    state = 10;
                    continue;
                } else {
                    v___x_2660_ = lean_string_append(v___x_2653_, v_result_2659_);
                    leanh::lean_dec_ref(v_result_2659_);
                    v___y_2621_ = v___y_2642_;
                    v___y_2622_ = v___y_2650_;
                    v___y_2623_ = v___y_2643_;
                    v___y_2624_ = v___y_2645_;
                    v___y_2625_ = v___y_2647_;
                    v___y_2626_ = v___y_2646_;
                    v___y_2627_ = v___y_2648_;
                    v___y_2628_ = v___y_2649_;
                    v___y_2629_ = v___x_2660_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_2674_ = lean_string_append(v___y_2670_, v___y_2665_);
                leanh::lean_dec_ref(v___y_2665_);
                v___x_2675_ = lean_string_append(v___x_2674_, v___y_2673_);
                leanh::lean_dec_ref(v___y_2673_);
                leanh::lean_inc_ref(v___y_2672_);
                v___x_2676_ = lean_string_append(v___y_2672_, v___x_2675_);
                leanh::lean_dec_ref(v___x_2675_);
                v___y_2642_ = v___y_2662_;
                v___y_2643_ = v___y_2663_;
                v___y_2644_ = v___y_2664_;
                v___y_2645_ = v___y_2666_;
                v___y_2646_ = v___y_2668_;
                v___y_2647_ = v___y_2667_;
                v___y_2648_ = v___y_2669_;
                v___y_2649_ = v___y_2671_;
                v___y_2650_ = v___x_2676_;
                state = 11;
                continue;
            }
            13 => match leanh::lean_obj_tag(v_port_2680_) {
                0 => {
                    v___x_2690_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                    v___y_2662_ = v___y_2678_;
                    v___y_2663_ = v___y_2679_;
                    v___y_2664_ = v___y_2681_;
                    v___y_2665_ = v___y_2689_;
                    v___y_2666_ = v___y_2682_;
                    v___y_2667_ = v___y_2684_;
                    v___y_2668_ = v___y_2683_;
                    v___y_2669_ = v___y_2685_;
                    v___y_2670_ = v___y_2686_;
                    v___y_2671_ = v___y_2687_;
                    v___y_2672_ = v___y_2688_;
                    v___y_2673_ = v___x_2690_;
                    state = 12;
                    continue;
                }
                1 => {
                    v___x_2691_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___y_2662_ = v___y_2678_;
                    v___y_2663_ = v___y_2679_;
                    v___y_2664_ = v___y_2681_;
                    v___y_2665_ = v___y_2689_;
                    v___y_2666_ = v___y_2682_;
                    v___y_2667_ = v___y_2684_;
                    v___y_2668_ = v___y_2683_;
                    v___y_2669_ = v___y_2685_;
                    v___y_2670_ = v___y_2686_;
                    v___y_2671_ = v___y_2687_;
                    v___y_2672_ = v___y_2688_;
                    v___y_2673_ = v___x_2691_;
                    state = 12;
                    continue;
                }
                _ => {
                    v_port_2692_ = leanh::lean_ctor_get_uint16(v_port_2680_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_2680_, 0);
                    v___x_2693_ = l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                    v___x_2694_ = lean_uint16_to_nat(v_port_2692_);
                    v___x_2695_ = l_Nat_reprFast(v___x_2694_);
                    v___x_2696_ = lean_string_append(v___x_2693_, v___x_2695_);
                    leanh::lean_dec_ref(v___x_2695_);
                    v___y_2662_ = v___y_2678_;
                    v___y_2663_ = v___y_2679_;
                    v___y_2664_ = v___y_2681_;
                    v___y_2665_ = v___y_2689_;
                    v___y_2666_ = v___y_2682_;
                    v___y_2667_ = v___y_2684_;
                    v___y_2668_ = v___y_2683_;
                    v___y_2669_ = v___y_2685_;
                    v___y_2670_ = v___y_2686_;
                    v___y_2671_ = v___y_2687_;
                    v___y_2672_ = v___y_2688_;
                    v___y_2673_ = v___x_2696_;
                    state = 12;
                    continue;
                }
            },
            14 => match leanh::lean_obj_tag(v_host_2701_) {
                0 => {
                    v_name_2710_ = leanh::lean_ctor_get(v_host_2701_, 0);
                    leanh::lean_inc_ref(v_name_2710_);
                    leanh::lean_dec_ref_known(v_host_2701_, 1);
                    v___y_2678_ = v___y_2698_;
                    v___y_2679_ = v___y_2699_;
                    v_port_2680_ = v_port_2702_;
                    v___y_2681_ = v___y_2700_;
                    v___y_2682_ = v___y_2703_;
                    v___y_2683_ = v___y_2705_;
                    v___y_2684_ = v___y_2704_;
                    v___y_2685_ = v___y_2706_;
                    v___y_2686_ = v___y_2709_;
                    v___y_2687_ = v___y_2707_;
                    v___y_2688_ = v___y_2708_;
                    v___y_2689_ = v_name_2710_;
                    state = 13;
                    continue;
                }
                1 => {
                    v_ipv4_2711_ = leanh::lean_ctor_get(v_host_2701_, 0);
                    leanh::lean_inc_ref(v_ipv4_2711_);
                    leanh::lean_dec_ref_known(v_host_2701_, 1);
                    v___x_2712_ = lean_uv_ntop_v4(v_ipv4_2711_);
                    leanh::lean_dec_ref(v_ipv4_2711_);
                    v___y_2678_ = v___y_2698_;
                    v___y_2679_ = v___y_2699_;
                    v_port_2680_ = v_port_2702_;
                    v___y_2681_ = v___y_2700_;
                    v___y_2682_ = v___y_2703_;
                    v___y_2683_ = v___y_2705_;
                    v___y_2684_ = v___y_2704_;
                    v___y_2685_ = v___y_2706_;
                    v___y_2686_ = v___y_2709_;
                    v___y_2687_ = v___y_2707_;
                    v___y_2688_ = v___y_2708_;
                    v___y_2689_ = v___x_2712_;
                    state = 13;
                    continue;
                }
                _ => {
                    v_ipv6_2713_ = leanh::lean_ctor_get(v_host_2701_, 0);
                    leanh::lean_inc_ref(v_ipv6_2713_);
                    leanh::lean_dec_ref_known(v_host_2701_, 1);
                    v___x_2714_ = l_Std_Http_Request_instToStringHead___lam__6___closed__20;
                    v___x_2715_ = lean_uv_ntop_v6(v_ipv6_2713_);
                    leanh::lean_dec_ref(v_ipv6_2713_);
                    v___x_2716_ = lean_string_append(v___x_2714_, v___x_2715_);
                    leanh::lean_dec_ref(v___x_2715_);
                    v___x_2717_ = l_Std_Http_Request_instToStringHead___lam__6___closed__21;
                    v___x_2718_ = lean_string_append(v___x_2716_, v___x_2717_);
                    v___y_2678_ = v___y_2698_;
                    v___y_2679_ = v___y_2699_;
                    v_port_2680_ = v_port_2702_;
                    v___y_2681_ = v___y_2700_;
                    v___y_2682_ = v___y_2703_;
                    v___y_2683_ = v___y_2705_;
                    v___y_2684_ = v___y_2704_;
                    v___y_2685_ = v___y_2706_;
                    v___y_2686_ = v___y_2709_;
                    v___y_2687_ = v___y_2707_;
                    v___y_2688_ = v___y_2708_;
                    v___y_2689_ = v___x_2718_;
                    state = 13;
                    continue;
                }
            },
            15 => {
                if leanh::lean_obj_tag(v___y_2724_) == 0 {
                    leanh::lean_dec_ref(v___f_2497_);
                    v___y_2531_ = v___y_2720_;
                    v___y_2532_ = v___y_2721_;
                    v___y_2533_ = v___y_2722_;
                    v___y_2534_ = v___y_2723_;
                    v___y_2535_ = v___y_2725_;
                    state = 4;
                    continue;
                } else {
                    v_val_2726_ = leanh::lean_ctor_get(v___y_2724_, 0);
                    leanh::lean_inc(v_val_2726_);
                    leanh::lean_dec_ref_known(v___y_2724_, 1);
                    v___x_2727_ = lean_array_get_size(v_val_2726_);
                    v___x_2728_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2729_ = lean_nat_dec_eq(v___x_2727_, v___x_2728_);
                    if v___x_2729_ == 0 {
                        v___x_2730_ = lean_array_to_list(v_val_2726_);
                        v___x_2731_ = leanh::lean_box(0);
                        v_encodedParams_2732_ =
                            l_List_mapTR_loop___redArg(v___f_2497_, v___x_2730_, v___x_2731_);
                        v___x_2733_ = l_Std_Http_Request_instToStringHead___lam__6___closed__15;
                        v___x_2734_ = l_Std_Http_Request_instToStringHead___lam__6___closed__16;
                        v___x_2735_ = l_String_intercalate(v___x_2734_, v_encodedParams_2732_);
                        v___x_2736_ = lean_string_append(v___x_2733_, v___x_2735_);
                        leanh::lean_dec_ref(v___x_2735_);
                        v___x_2737_ = lean_string_append(v___y_2725_, v___x_2736_);
                        leanh::lean_dec_ref(v___x_2736_);
                        v___y_2531_ = v___y_2720_;
                        v___y_2532_ = v___y_2721_;
                        v___y_2533_ = v___y_2722_;
                        v___y_2534_ = v___y_2723_;
                        v___y_2535_ = v___x_2737_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_2726_);
                        leanh::lean_dec_ref(v___f_2497_);
                        v___y_2531_ = v___y_2720_;
                        v___y_2532_ = v___y_2721_;
                        v___y_2533_ = v___y_2722_;
                        v___y_2534_ = v___y_2723_;
                        v___y_2535_ = v___y_2725_;
                        state = 4;
                        continue;
                    }
                }
            }
            16 => {
                v_data_2740_ = leanh::lean_ctor_get(v_buffer_2499_, 0);
                leanh::lean_inc_ref(v_data_2740_);
                v_size_2741_ = leanh::lean_ctor_get(v_buffer_2499_, 1);
                leanh::lean_inc(v_size_2741_);
                leanh::lean_dec_ref(v_buffer_2499_);
                v___x_2742_ = lean_string_to_utf8(v___y_2739_);
                leanh::lean_inc_ref(v___x_2742_);
                v___x_2743_ = lean_array_push(v_data_2740_, v___x_2742_);
                v___x_2744_ = lean_byte_array_size(v___x_2742_);
                leanh::lean_dec_ref(v___x_2742_);
                v___x_2745_ = lean_nat_add(v_size_2741_, v___x_2744_);
                leanh::lean_dec(v_size_2741_);
                v___x_2746_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once
                    ),
                    _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3,
                );
                v___x_2747_ = lean_array_push(v___x_2743_, v___x_2746_);
                v___x_2748_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4_once
                    ),
                    _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4,
                );
                v___x_2749_ = lean_nat_add(v___x_2745_, v___x_2748_);
                leanh::lean_dec(v___x_2745_);
                match leanh::lean_obj_tag(v_uri_2503_) {
                    0 => {
                        leanh::lean_dec_ref(v___f_2496_);
                        leanh::lean_dec_ref(v___f_2495_);
                        v_path_2750_ = leanh::lean_ctor_get(v_uri_2503_, 0);
                        leanh::lean_inc_ref(v_path_2750_);
                        v_query_2751_ = leanh::lean_ctor_get(v_uri_2503_, 1);
                        leanh::lean_inc(v_query_2751_);
                        leanh::lean_dec_ref_known(v_uri_2503_, 2);
                        v_segments_2752_ = leanh::lean_ctor_get(v_path_2750_, 0);
                        leanh::lean_inc_ref(v_segments_2752_);
                        v_absolute_2753_ = leanh::lean_ctor_get_uint8(
                            v_path_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        leanh::lean_dec_ref(v_path_2750_);
                        v___x_2754_ = l_Std_Http_Request_instToStringHead___lam__6___closed__19;
                        v___x_2755_ = l_Std_Http_Request_instToStringHead___lam__6___closed__10;
                        v_sz_2756_ = lean_array_size(v_segments_2752_);
                        v___x_2757_ = 0usize;
                        v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2755_,
                            v___f_2498_,
                            v_sz_2756_,
                            v___x_2757_,
                            v_segments_2752_,
                        );
                        v___x_2759_ = lean_array_to_list(v___x_2758_);
                        v_result_2760_ = l_String_intercalate(v___x_2754_, v___x_2759_);
                        if v_absolute_2753_ == 0 {
                            v___y_2720_ = v___x_2748_;
                            v___y_2721_ = v___x_2747_;
                            v___y_2722_ = v___x_2746_;
                            v___y_2723_ = v___x_2749_;
                            v___y_2724_ = v_query_2751_;
                            v___y_2725_ = v_result_2760_;
                            state = 15;
                            continue;
                        } else {
                            v___x_2761_ = lean_string_append(v___x_2754_, v_result_2760_);
                            leanh::lean_dec_ref(v_result_2760_);
                            v___y_2720_ = v___x_2748_;
                            v___y_2721_ = v___x_2747_;
                            v___y_2722_ = v___x_2746_;
                            v___y_2723_ = v___x_2749_;
                            v___y_2724_ = v_query_2751_;
                            v___y_2725_ = v___x_2761_;
                            state = 15;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_dec_ref(v___f_2498_);
                        leanh::lean_dec_ref(v___f_2497_);
                        v_uri_2762_ = leanh::lean_ctor_get(v_uri_2503_, 0);
                        leanh::lean_inc_ref(v_uri_2762_);
                        leanh::lean_dec_ref_known(v_uri_2503_, 1);
                        v_authority_2763_ = leanh::lean_ctor_get(v_uri_2762_, 1);
                        if leanh::lean_obj_tag(v_authority_2763_) == 0 {
                            v_scheme_2764_ = leanh::lean_ctor_get(v_uri_2762_, 0);
                            leanh::lean_inc_ref(v_scheme_2764_);
                            v_path_2765_ = leanh::lean_ctor_get(v_uri_2762_, 2);
                            leanh::lean_inc_ref(v_path_2765_);
                            v_query_2766_ = leanh::lean_ctor_get(v_uri_2762_, 3);
                            leanh::lean_inc_ref(v_query_2766_);
                            v_fragment_2767_ = leanh::lean_ctor_get(v_uri_2762_, 4);
                            leanh::lean_inc(v_fragment_2767_);
                            leanh::lean_dec_ref(v_uri_2762_);
                            v___x_2768_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                            v___y_2642_ = v___x_2748_;
                            v___y_2643_ = v_scheme_2764_;
                            v___y_2644_ = v_path_2765_;
                            v___y_2645_ = v___x_2747_;
                            v___y_2646_ = v_fragment_2767_;
                            v___y_2647_ = v___x_2746_;
                            v___y_2648_ = v___x_2749_;
                            v___y_2649_ = v_query_2766_;
                            v___y_2650_ = v___x_2768_;
                            state = 11;
                            continue;
                        } else {
                            v_val_2769_ = leanh::lean_ctor_get(v_authority_2763_, 0);
                            leanh::lean_inc(v_val_2769_);
                            v_scheme_2770_ = leanh::lean_ctor_get(v_uri_2762_, 0);
                            leanh::lean_inc_ref(v_scheme_2770_);
                            v_path_2771_ = leanh::lean_ctor_get(v_uri_2762_, 2);
                            leanh::lean_inc_ref(v_path_2771_);
                            v_query_2772_ = leanh::lean_ctor_get(v_uri_2762_, 3);
                            leanh::lean_inc_ref(v_query_2772_);
                            v_fragment_2773_ = leanh::lean_ctor_get(v_uri_2762_, 4);
                            leanh::lean_inc(v_fragment_2773_);
                            leanh::lean_dec_ref(v_uri_2762_);
                            v_userInfo_2774_ = leanh::lean_ctor_get(v_val_2769_, 0);
                            leanh::lean_inc(v_userInfo_2774_);
                            v_host_2775_ = leanh::lean_ctor_get(v_val_2769_, 1);
                            leanh::lean_inc_ref(v_host_2775_);
                            v_port_2776_ = leanh::lean_ctor_get(v_val_2769_, 2);
                            leanh::lean_inc(v_port_2776_);
                            leanh::lean_dec(v_val_2769_);
                            v___x_2777_ = l_Std_Http_Request_instToStringHead___lam__6___closed__23;
                            if leanh::lean_obj_tag(v_userInfo_2774_) == 0 {
                                v___x_2778_ =
                                    l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                                v___y_2698_ = v___x_2748_;
                                v___y_2699_ = v_scheme_2770_;
                                v___y_2700_ = v_path_2771_;
                                v_host_2701_ = v_host_2775_;
                                v_port_2702_ = v_port_2776_;
                                v___y_2703_ = v___x_2747_;
                                v___y_2704_ = v___x_2746_;
                                v___y_2705_ = v_fragment_2773_;
                                v___y_2706_ = v___x_2749_;
                                v___y_2707_ = v_query_2772_;
                                v___y_2708_ = v___x_2777_;
                                v___y_2709_ = v___x_2778_;
                                state = 14;
                                continue;
                            } else {
                                v_val_2779_ = leanh::lean_ctor_get(v_userInfo_2774_, 0);
                                leanh::lean_inc(v_val_2779_);
                                leanh::lean_dec_ref_known(v_userInfo_2774_, 1);
                                v_password_2780_ = leanh::lean_ctor_get(v_val_2779_, 1);
                                if leanh::lean_obj_tag(v_password_2780_) == 0 {
                                    v_username_2781_ = leanh::lean_ctor_get(v_val_2779_, 0);
                                    leanh::lean_inc_ref(v_username_2781_);
                                    leanh::lean_dec(v_val_2779_);
                                    v___x_2782_ = lean_string_from_utf8_unchecked(v_username_2781_);
                                    v___x_2783_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                    v___x_2784_ = lean_string_append(v___x_2782_, v___x_2783_);
                                    v___y_2698_ = v___x_2748_;
                                    v___y_2699_ = v_scheme_2770_;
                                    v___y_2700_ = v_path_2771_;
                                    v_host_2701_ = v_host_2775_;
                                    v_port_2702_ = v_port_2776_;
                                    v___y_2703_ = v___x_2747_;
                                    v___y_2704_ = v___x_2746_;
                                    v___y_2705_ = v_fragment_2773_;
                                    v___y_2706_ = v___x_2749_;
                                    v___y_2707_ = v_query_2772_;
                                    v___y_2708_ = v___x_2777_;
                                    v___y_2709_ = v___x_2784_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc_ref(v_password_2780_);
                                    v_username_2785_ = leanh::lean_ctor_get(v_val_2779_, 0);
                                    leanh::lean_inc_ref(v_username_2785_);
                                    leanh::lean_dec(v_val_2779_);
                                    v_val_2786_ = leanh::lean_ctor_get(v_password_2780_, 0);
                                    leanh::lean_inc(v_val_2786_);
                                    leanh::lean_dec_ref_known(v_password_2780_, 1);
                                    v___x_2787_ = lean_string_from_utf8_unchecked(v_username_2785_);
                                    v___x_2788_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                                    v___x_2789_ = lean_string_append(v___x_2787_, v___x_2788_);
                                    v___x_2790_ = lean_string_from_utf8_unchecked(v_val_2786_);
                                    v___x_2791_ = lean_string_append(v___x_2789_, v___x_2790_);
                                    leanh::lean_dec_ref(v___x_2790_);
                                    v___x_2792_ =
                                        l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                    v___x_2793_ = lean_string_append(v___x_2791_, v___x_2792_);
                                    v___y_2698_ = v___x_2748_;
                                    v___y_2699_ = v_scheme_2770_;
                                    v___y_2700_ = v_path_2771_;
                                    v_host_2701_ = v_host_2775_;
                                    v_port_2702_ = v_port_2776_;
                                    v___y_2703_ = v___x_2747_;
                                    v___y_2704_ = v___x_2746_;
                                    v___y_2705_ = v_fragment_2773_;
                                    v___y_2706_ = v___x_2749_;
                                    v___y_2707_ = v_query_2772_;
                                    v___y_2708_ = v___x_2777_;
                                    v___y_2709_ = v___x_2793_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                    2 => {
                        leanh::lean_dec_ref(v___f_2498_);
                        leanh::lean_dec_ref(v___f_2497_);
                        leanh::lean_dec_ref(v___f_2496_);
                        leanh::lean_dec_ref(v___f_2495_);
                        v_authority_2794_ = leanh::lean_ctor_get(v_uri_2503_, 0);
                        leanh::lean_inc_ref(v_authority_2794_);
                        leanh::lean_dec_ref_known(v_uri_2503_, 1);
                        v_userInfo_2795_ = leanh::lean_ctor_get(v_authority_2794_, 0);
                        if leanh::lean_obj_tag(v_userInfo_2795_) == 0 {
                            v_host_2796_ = leanh::lean_ctor_get(v_authority_2794_, 1);
                            leanh::lean_inc_ref(v_host_2796_);
                            v_port_2797_ = leanh::lean_ctor_get(v_authority_2794_, 2);
                            leanh::lean_inc(v_port_2797_);
                            leanh::lean_dec_ref(v_authority_2794_);
                            v___x_2798_ = l_Std_Http_Request_instToStringHead___lam__3___closed__4;
                            v___y_2572_ = v___x_2748_;
                            v_host_2573_ = v_host_2796_;
                            v_port_2574_ = v_port_2797_;
                            v___y_2575_ = v___x_2747_;
                            v___y_2576_ = v___x_2746_;
                            v___y_2577_ = v___x_2749_;
                            v___y_2578_ = v___x_2798_;
                            state = 7;
                            continue;
                        } else {
                            v_val_2799_ = leanh::lean_ctor_get(v_userInfo_2795_, 0);
                            leanh::lean_inc(v_val_2799_);
                            v_password_2800_ = leanh::lean_ctor_get(v_val_2799_, 1);
                            if leanh::lean_obj_tag(v_password_2800_) == 0 {
                                v_host_2801_ = leanh::lean_ctor_get(v_authority_2794_, 1);
                                leanh::lean_inc_ref(v_host_2801_);
                                v_port_2802_ = leanh::lean_ctor_get(v_authority_2794_, 2);
                                leanh::lean_inc(v_port_2802_);
                                leanh::lean_dec_ref(v_authority_2794_);
                                v_username_2803_ = leanh::lean_ctor_get(v_val_2799_, 0);
                                leanh::lean_inc_ref(v_username_2803_);
                                leanh::lean_dec(v_val_2799_);
                                v___x_2804_ = lean_string_from_utf8_unchecked(v_username_2803_);
                                v___x_2805_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                v___x_2806_ = lean_string_append(v___x_2804_, v___x_2805_);
                                v___y_2572_ = v___x_2748_;
                                v_host_2573_ = v_host_2801_;
                                v_port_2574_ = v_port_2802_;
                                v___y_2575_ = v___x_2747_;
                                v___y_2576_ = v___x_2746_;
                                v___y_2577_ = v___x_2749_;
                                v___y_2578_ = v___x_2806_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_password_2800_);
                                v_host_2807_ = leanh::lean_ctor_get(v_authority_2794_, 1);
                                leanh::lean_inc_ref(v_host_2807_);
                                v_port_2808_ = leanh::lean_ctor_get(v_authority_2794_, 2);
                                leanh::lean_inc(v_port_2808_);
                                leanh::lean_dec_ref(v_authority_2794_);
                                v_username_2809_ = leanh::lean_ctor_get(v_val_2799_, 0);
                                leanh::lean_inc_ref(v_username_2809_);
                                leanh::lean_dec(v_val_2799_);
                                v_val_2810_ = leanh::lean_ctor_get(v_password_2800_, 0);
                                leanh::lean_inc(v_val_2810_);
                                leanh::lean_dec_ref_known(v_password_2800_, 1);
                                v___x_2811_ = lean_string_from_utf8_unchecked(v_username_2809_);
                                v___x_2812_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__17;
                                v___x_2813_ = lean_string_append(v___x_2811_, v___x_2812_);
                                v___x_2814_ = lean_string_from_utf8_unchecked(v_val_2810_);
                                v___x_2815_ = lean_string_append(v___x_2813_, v___x_2814_);
                                leanh::lean_dec_ref(v___x_2814_);
                                v___x_2816_ =
                                    l_Std_Http_Request_instToStringHead___lam__6___closed__24;
                                v___x_2817_ = lean_string_append(v___x_2815_, v___x_2816_);
                                v___y_2572_ = v___x_2748_;
                                v_host_2573_ = v_host_2807_;
                                v_port_2574_ = v_port_2808_;
                                v___y_2575_ = v___x_2747_;
                                v___y_2576_ = v___x_2746_;
                                v___y_2577_ = v___x_2749_;
                                v___y_2578_ = v___x_2817_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v___f_2498_);
                        leanh::lean_dec_ref(v___f_2497_);
                        leanh::lean_dec_ref(v___f_2496_);
                        leanh::lean_dec_ref(v___f_2495_);
                        v___x_2818_ = l_Std_Http_Request_instToStringHead___lam__6___closed__25;
                        v___y_2531_ = v___x_2748_;
                        v___y_2532_ = v___x_2747_;
                        v___y_2533_ = v___x_2746_;
                        v___y_2534_ = v___x_2749_;
                        v___y_2535_ = v___x_2818_;
                        state = 4;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Http_Request_new___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: u8 = 0;
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Std_Http_Headers_empty;
    v___x_2866_ = leanh::lean_box(3);
    v___x_2867_ = 1;
    v___x_2868_ = 8;
    v___x_2869_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
    leanh::lean_ctor_set(v___x_2869_, 0, v___x_2866_);
    leanh::lean_ctor_set(v___x_2869_, 1, v___x_2865_);
    leanh::lean_ctor_set_uint8(
        v___x_2869_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_2868_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2869_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
        v___x_2867_,
    );
    return v___x_2869_;
}
pub unsafe fn _init_l_Std_Http_Request_new___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ = l_Std_Http_Extensions_empty;
    v___x_2871_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_new___closed__0_once),
        _init_l_Std_Http_Request_new___closed__0,
    );
    v___x_2872_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2872_, 0, v___x_2871_);
    leanh::lean_ctor_set(v___x_2872_, 1, v___x_2870_);
    return v___x_2872_;
}
pub unsafe fn _init_l_Std_Http_Request_new() -> *mut leanh::LeanObject {
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2873_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_new___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_new___closed__1_once),
        _init_l_Std_Http_Request_new___closed__1,
    );
    return v___x_2873_;
}
pub unsafe fn l_Std_Http_Request_Builder_method(
    mut v_builder_2874_: *mut leanh::LeanObject,
    mut v_method_2875_: u8,
) -> *mut leanh::LeanObject {
    let mut v_line_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v_version_2881_: u8 = 0;
    let mut v_uri_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_2876_ = leanh::lean_ctor_get(v_builder_2874_, 0);
                v_extensions_2877_ = leanh::lean_ctor_get(v_builder_2874_, 1);
                v_isSharedCheck_2894_ = (!leanh::lean_is_exclusive(v_builder_2874_)) as u8;
                if v_isSharedCheck_2894_ == 0 {
                    v___x_2879_ = v_builder_2874_;
                    v_isShared_2880_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_2877_);
                    leanh::lean_inc(v_line_2876_);
                    leanh::lean_dec(v_builder_2874_);
                    v___x_2879_ = leanh::lean_box(0);
                    v_isShared_2880_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_version_2881_ = leanh::lean_ctor_get_uint8(
                    v_line_2876_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_2882_ = leanh::lean_ctor_get(v_line_2876_, 0);
                v_headers_2883_ = leanh::lean_ctor_get(v_line_2876_, 1);
                v_isSharedCheck_2893_ = (!leanh::lean_is_exclusive(v_line_2876_)) as u8;
                if v_isSharedCheck_2893_ == 0 {
                    v___x_2885_ = v_line_2876_;
                    v_isShared_2886_ = v_isSharedCheck_2893_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_headers_2883_);
                    leanh::lean_inc(v_uri_2882_);
                    leanh::lean_dec(v_line_2876_);
                    v___x_2885_ = leanh::lean_box(0);
                    v_isShared_2886_ = v_isSharedCheck_2893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2886_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_uri_2882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_headers_2883_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2892_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_2881_,
                    );
                    v___x_2888_ = v_reuseFailAlloc_2892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2888_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_method_2875_,
                );
                if v_isShared_2880_ == 0 {
                    leanh::lean_ctor_set(v___x_2879_, 0, v___x_2888_);
                    v___x_2890_ = v___x_2879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_extensions_2877_);
                    v___x_2890_ = v_reuseFailAlloc_2891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_method___boxed(
    mut v_builder_2895_: *mut leanh::LeanObject,
    mut v_method_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_boxed_2897_: u8 = 0;
    let mut v_res_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_method_boxed_2897_ = (leanh::lean_unbox(v_method_2896_) as u8);
    v_res_2898_ = l_Std_Http_Request_Builder_method(v_builder_2895_, v_method_boxed_2897_);
    return v_res_2898_;
}
pub unsafe fn l_Std_Http_Request_Builder_version(
    mut v_builder_2899_: *mut leanh::LeanObject,
    mut v_version_2900_: u8,
) -> *mut leanh::LeanObject {
    let mut v_line_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v_method_2906_: u8 = 0;
    let mut v_uri_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_2901_ = leanh::lean_ctor_get(v_builder_2899_, 0);
                v_extensions_2902_ = leanh::lean_ctor_get(v_builder_2899_, 1);
                v_isSharedCheck_2919_ = (!leanh::lean_is_exclusive(v_builder_2899_)) as u8;
                if v_isSharedCheck_2919_ == 0 {
                    v___x_2904_ = v_builder_2899_;
                    v_isShared_2905_ = v_isSharedCheck_2919_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_2902_);
                    leanh::lean_inc(v_line_2901_);
                    leanh::lean_dec(v_builder_2899_);
                    v___x_2904_ = leanh::lean_box(0);
                    v_isShared_2905_ = v_isSharedCheck_2919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_method_2906_ = leanh::lean_ctor_get_uint8(
                    v_line_2901_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_uri_2907_ = leanh::lean_ctor_get(v_line_2901_, 0);
                v_headers_2908_ = leanh::lean_ctor_get(v_line_2901_, 1);
                v_isSharedCheck_2918_ = (!leanh::lean_is_exclusive(v_line_2901_)) as u8;
                if v_isSharedCheck_2918_ == 0 {
                    v___x_2910_ = v_line_2901_;
                    v_isShared_2911_ = v_isSharedCheck_2918_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_headers_2908_);
                    leanh::lean_inc(v_uri_2907_);
                    leanh::lean_dec(v_line_2901_);
                    v___x_2910_ = leanh::lean_box(0);
                    v_isShared_2911_ = v_isSharedCheck_2918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2917_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_uri_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_headers_2908_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2917_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_2906_,
                    );
                    v___x_2913_ = v_reuseFailAlloc_2917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2913_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_version_2900_,
                );
                if v_isShared_2905_ == 0 {
                    leanh::lean_ctor_set(v___x_2904_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_extensions_2902_);
                    v___x_2915_ = v_reuseFailAlloc_2916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_version___boxed(
    mut v_builder_2920_: *mut leanh::LeanObject,
    mut v_version_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_version_boxed_2922_: u8 = 0;
    let mut v_res_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_version_boxed_2922_ = (leanh::lean_unbox(v_version_2921_) as u8);
    v_res_2923_ = l_Std_Http_Request_Builder_version(v_builder_2920_, v_version_boxed_2922_);
    return v_res_2923_;
}
pub unsafe fn l_Std_Http_Request_Builder_uri(
    mut v_builder_2924_: *mut leanh::LeanObject,
    mut v_uri_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v_method_2931_: u8 = 0;
    let mut v_version_2932_: u8 = 0;
    let mut v_headers_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_unused_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_2926_ = leanh::lean_ctor_get(v_builder_2924_, 0);
                v_extensions_2927_ = leanh::lean_ctor_get(v_builder_2924_, 1);
                v_isSharedCheck_2945_ = (!leanh::lean_is_exclusive(v_builder_2924_)) as u8;
                if v_isSharedCheck_2945_ == 0 {
                    v___x_2929_ = v_builder_2924_;
                    v_isShared_2930_ = v_isSharedCheck_2945_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_2927_);
                    leanh::lean_inc(v_line_2926_);
                    leanh::lean_dec(v_builder_2924_);
                    v___x_2929_ = leanh::lean_box(0);
                    v_isShared_2930_ = v_isSharedCheck_2945_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_method_2931_ = leanh::lean_ctor_get_uint8(
                    v_line_2926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_2932_ = leanh::lean_ctor_get_uint8(
                    v_line_2926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_headers_2933_ = leanh::lean_ctor_get(v_line_2926_, 1);
                v_isSharedCheck_2943_ = (!leanh::lean_is_exclusive(v_line_2926_)) as u8;
                if v_isSharedCheck_2943_ == 0 {
                    v_unused_2944_ = leanh::lean_ctor_get(v_line_2926_, 0);
                    leanh::lean_dec(v_unused_2944_);
                    v___x_2935_ = v_line_2926_;
                    v_isShared_2936_ = v_isSharedCheck_2943_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_headers_2933_);
                    leanh::lean_dec(v_line_2926_);
                    v___x_2935_ = leanh::lean_box(0);
                    v_isShared_2936_ = v_isSharedCheck_2943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2936_ == 0 {
                    leanh::lean_ctor_set(v___x_2935_, 0, v_uri_2925_);
                    v___x_2938_ = v___x_2935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_uri_2925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_headers_2933_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2942_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_2931_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2942_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_2932_,
                    );
                    v___x_2938_ = v_reuseFailAlloc_2942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2930_ == 0 {
                    leanh::lean_ctor_set(v___x_2929_, 0, v___x_2938_);
                    v___x_2940_ = v___x_2929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_extensions_2927_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(
    mut v_msg_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_Std_Http_instInhabitedRequestTarget_default;
    v___x_2948_ = lean_panic_fn_borrowed(v___x_2947_, v_msg_2946_);
    return v___x_2948_;
}
pub unsafe fn l_Std_Http_Request_Builder_uri_x21___lam__0(
    mut v___x_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2962_: u8 = 0;
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_unused_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2952_, v___y_2953_);
                if leanh::lean_obj_tag(v___x_2954_) == 0 {
                    v_pos_2955_ = leanh::lean_ctor_get(v___x_2954_, 0);
                    leanh::lean_inc(v_pos_2955_);
                    v_array_2956_ = leanh::lean_ctor_get(v_pos_2955_, 0);
                    v_idx_2957_ = leanh::lean_ctor_get(v_pos_2955_, 1);
                    v___x_2958_ = lean_byte_array_size(v_array_2956_);
                    v___x_2959_ = lean_nat_dec_lt(v_idx_2957_, v___x_2958_);
                    if v___x_2959_ == 0 {
                        leanh::lean_dec(v_pos_2955_);
                        return v___x_2954_;
                    } else {
                        v_isSharedCheck_2967_ =
                            (!leanh::lean_is_exclusive(v___x_2954_)) as u8;
                        if v_isSharedCheck_2967_ == 0 {
                            v_unused_2968_ = leanh::lean_ctor_get(v___x_2954_, 1);
                            leanh::lean_dec(v_unused_2968_);
                            v_unused_2969_ = leanh::lean_ctor_get(v___x_2954_, 0);
                            leanh::lean_dec(v_unused_2969_);
                            v___x_2961_ = v___x_2954_;
                            v_isShared_2962_ = v_isSharedCheck_2967_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2954_);
                            v___x_2961_ = leanh::lean_box(0);
                            v_isShared_2962_ = v_isSharedCheck_2967_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_2954_;
                }
            }
            1 => {
                v___x_2963_ = l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1;
                if v_isShared_2962_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2961_, 1);
                    leanh::lean_ctor_set(v___x_2961_, 1, v___x_2963_);
                    v___x_2965_ = v___x_2961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_pos_2955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2963_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Http_Request_Builder_uri_x21___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = l_Std_Http_Request_Builder_uri_x21___closed__4;
    v___x_2984_ = leanh::lean_unsigned_to_nat(12);
    v___x_2985_ = leanh::lean_unsigned_to_nat(45);
    v___x_2986_ = l_Std_Http_Request_Builder_uri_x21___closed__3;
    v___x_2987_ = l_Std_Http_Request_Builder_uri_x21___closed__2;
    v___x_2988_ = l_mkPanicMessageWithDecl(
        v___x_2987_,
        v___x_2986_,
        v___x_2985_,
        v___x_2984_,
        v___x_2983_,
    );
    return v___x_2988_;
}
pub unsafe fn l_Std_Http_Request_Builder_uri_x21(
    mut v_builder_2989_: *mut leanh::LeanObject,
    mut v_uri_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v_method_2998_: u8 = 0;
    let mut v_version_2999_: u8 = 0;
    let mut v_headers_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v_unused_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v___f_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3013_ = l_Std_Http_Request_Builder_uri_x21___closed__1;
                v___x_3014_ = lean_string_to_utf8(v_uri_2990_);
                v___x_3015_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_3013_, v___x_3014_);
                if leanh::lean_obj_tag(v___x_3015_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3015_, 1);
                    v___x_3016_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_uri_x21___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Request_Builder_uri_x21___closed__5_once
                        ),
                        _init_l_Std_Http_Request_Builder_uri_x21___closed__5,
                    );
                    v___x_3017_ =
                        l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_3016_);
                    v___y_2992_ = v___x_3017_;
                    state = 1;
                    continue;
                } else {
                    v_a_3018_ = leanh::lean_ctor_get(v___x_3015_, 0);
                    leanh::lean_inc(v_a_3018_);
                    leanh::lean_dec_ref_known(v___x_3015_, 1);
                    v___y_2992_ = v_a_3018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_line_2993_ = leanh::lean_ctor_get(v_builder_2989_, 0);
                v_extensions_2994_ = leanh::lean_ctor_get(v_builder_2989_, 1);
                v_isSharedCheck_3012_ = (!leanh::lean_is_exclusive(v_builder_2989_)) as u8;
                if v_isSharedCheck_3012_ == 0 {
                    v___x_2996_ = v_builder_2989_;
                    v_isShared_2997_ = v_isSharedCheck_3012_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_2994_);
                    leanh::lean_inc(v_line_2993_);
                    leanh::lean_dec(v_builder_2989_);
                    v___x_2996_ = leanh::lean_box(0);
                    v_isShared_2997_ = v_isSharedCheck_3012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_method_2998_ = leanh::lean_ctor_get_uint8(
                    v_line_2993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_2999_ = leanh::lean_ctor_get_uint8(
                    v_line_2993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_headers_3000_ = leanh::lean_ctor_get(v_line_2993_, 1);
                v_isSharedCheck_3010_ = (!leanh::lean_is_exclusive(v_line_2993_)) as u8;
                if v_isSharedCheck_3010_ == 0 {
                    v_unused_3011_ = leanh::lean_ctor_get(v_line_2993_, 0);
                    leanh::lean_dec(v_unused_3011_);
                    v___x_3002_ = v_line_2993_;
                    v_isShared_3003_ = v_isSharedCheck_3010_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_headers_3000_);
                    leanh::lean_dec(v_line_2993_);
                    v___x_3002_ = leanh::lean_box(0);
                    v_isShared_3003_ = v_isSharedCheck_3010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3003_ == 0 {
                    leanh::lean_ctor_set(v___x_3002_, 0, v___y_2992_);
                    v___x_3005_ = v___x_3002_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___y_2992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_headers_3000_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3009_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_2998_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3009_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_2999_,
                    );
                    v___x_3005_ = v_reuseFailAlloc_3009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2997_ == 0 {
                    leanh::lean_ctor_set(v___x_2996_, 0, v___x_3005_);
                    v___x_3007_ = v___x_2996_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3008_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_extensions_2994_);
                    v___x_3007_ = v_reuseFailAlloc_3008_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_uri_x21___boxed(
    mut v_builder_3019_: *mut leanh::LeanObject,
    mut v_uri_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Std_Http_Request_Builder_uri_x21(v_builder_3019_, v_uri_3020_);
    leanh::lean_dec_ref(v_uri_3020_);
    return v_res_3021_;
}
pub unsafe fn l_Std_Http_Request_Builder_headers(
    mut v_builder_3022_: *mut leanh::LeanObject,
    mut v_headers_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v_method_3029_: u8 = 0;
    let mut v_version_3030_: u8 = 0;
    let mut v_uri_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v_unused_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_3024_ = leanh::lean_ctor_get(v_builder_3022_, 0);
                v_extensions_3025_ = leanh::lean_ctor_get(v_builder_3022_, 1);
                v_isSharedCheck_3043_ = (!leanh::lean_is_exclusive(v_builder_3022_)) as u8;
                if v_isSharedCheck_3043_ == 0 {
                    v___x_3027_ = v_builder_3022_;
                    v_isShared_3028_ = v_isSharedCheck_3043_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_3025_);
                    leanh::lean_inc(v_line_3024_);
                    leanh::lean_dec(v_builder_3022_);
                    v___x_3027_ = leanh::lean_box(0);
                    v_isShared_3028_ = v_isSharedCheck_3043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_method_3029_ = leanh::lean_ctor_get_uint8(
                    v_line_3024_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_3030_ = leanh::lean_ctor_get_uint8(
                    v_line_3024_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_3031_ = leanh::lean_ctor_get(v_line_3024_, 0);
                v_isSharedCheck_3041_ = (!leanh::lean_is_exclusive(v_line_3024_)) as u8;
                if v_isSharedCheck_3041_ == 0 {
                    v_unused_3042_ = leanh::lean_ctor_get(v_line_3024_, 1);
                    leanh::lean_dec(v_unused_3042_);
                    v___x_3033_ = v_line_3024_;
                    v_isShared_3034_ = v_isSharedCheck_3041_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uri_3031_);
                    leanh::lean_dec(v_line_3024_);
                    v___x_3033_ = leanh::lean_box(0);
                    v_isShared_3034_ = v_isSharedCheck_3041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3034_ == 0 {
                    leanh::lean_ctor_set(v___x_3033_, 1, v_headers_3023_);
                    v___x_3036_ = v___x_3033_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3040_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_uri_3031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_headers_3023_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3040_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_3029_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3040_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_3030_,
                    );
                    v___x_3036_ = v_reuseFailAlloc_3040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3028_ == 0 {
                    leanh::lean_ctor_set(v___x_3027_, 0, v___x_3036_);
                    v___x_3038_ = v___x_3027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_extensions_3025_);
                    v___x_3038_ = v_reuseFailAlloc_3039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(
    mut v_i_3044_: *mut leanh::LeanObject,
    mut v_x_3045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3045_) == 0 {
                    v___x_3046_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3047_ = lean_mk_empty_array_with_capacity(v___x_3046_);
                    v___x_3048_ = lean_array_push(v___x_3047_, v_i_3044_);
                    v___x_3049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3049_, 0, v___x_3048_);
                    return v___x_3049_;
                } else {
                    v_val_3050_ = leanh::lean_ctor_get(v_x_3045_, 0);
                    v_isSharedCheck_3058_ = (!leanh::lean_is_exclusive(v_x_3045_)) as u8;
                    if v_isSharedCheck_3058_ == 0 {
                        v___x_3052_ = v_x_3045_;
                        v_isShared_3053_ = v_isSharedCheck_3058_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3050_);
                        leanh::lean_dec(v_x_3045_);
                        v___x_3052_ = leanh::lean_box(0);
                        v_isShared_3053_ = v_isSharedCheck_3058_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3054_ = lean_array_push(v_val_3050_, v_i_3044_);
                if v_isShared_3053_ == 0 {
                    leanh::lean_ctor_set(v___x_3052_, 0, v___x_3054_);
                    v___x_3056_ = v___x_3052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
                    v___x_3056_ = v_reuseFailAlloc_3057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(
    mut v_i_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
    mut v_x_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3072_: u8 = 0;
    let mut v_tail_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3061_) == 0 {
                    v___x_3062_ = leanh::lean_box(0);
                    v___x_3063_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_3059_, v___x_3062_);
                    v_val_3064_ = leanh::lean_ctor_get(v___x_3063_, 0);
                    leanh::lean_inc(v_val_3064_);
                    leanh::lean_dec(v___x_3063_);
                    v___x_3065_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3065_, 0, v_a_3060_);
                    leanh::lean_ctor_set(v___x_3065_, 1, v_val_3064_);
                    leanh::lean_ctor_set(v___x_3065_, 2, v_x_3061_);
                    return v___x_3065_;
                } else {
                    v_key_3066_ = leanh::lean_ctor_get(v_x_3061_, 0);
                    v_value_3067_ = leanh::lean_ctor_get(v_x_3061_, 1);
                    v_tail_3068_ = leanh::lean_ctor_get(v_x_3061_, 2);
                    v_isSharedCheck_3083_ = (!leanh::lean_is_exclusive(v_x_3061_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3070_ = v_x_3061_;
                        v_isShared_3071_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3068_);
                        leanh::lean_inc(v_value_3067_);
                        leanh::lean_inc(v_key_3066_);
                        leanh::lean_dec(v_x_3061_);
                        v___x_3070_ = leanh::lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3072_ = lean_string_dec_eq(v_key_3066_, v_a_3060_);
                if v___x_3072_ == 0 {
                    v_tail_3073_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_3059_, v_a_3060_, v_tail_3068_);
                    if v_isShared_3071_ == 0 {
                        leanh::lean_ctor_set(v___x_3070_, 2, v_tail_3073_);
                        v___x_3075_ = v___x_3070_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3076_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_key_3066_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_value_3067_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_tail_3073_);
                        v___x_3075_ = v_reuseFailAlloc_3076_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_3066_);
                    v___x_3077_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3077_, 0, v_value_3067_);
                    v___x_3078_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_3059_, v___x_3077_);
                    v_val_3079_ = leanh::lean_ctor_get(v___x_3078_, 0);
                    leanh::lean_inc(v_val_3079_);
                    leanh::lean_dec(v___x_3078_);
                    if v_isShared_3071_ == 0 {
                        leanh::lean_ctor_set(v___x_3070_, 1, v_val_3079_);
                        leanh::lean_ctor_set(v___x_3070_, 0, v_a_3060_);
                        v___x_3081_ = v___x_3070_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3082_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3060_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_val_3079_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 2, v_tail_3068_);
                        v___x_3081_ = v_reuseFailAlloc_3082_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3075_;
            }
            3 => {
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(
    mut v_a_3084_: *mut leanh::LeanObject,
    mut v_x_3085_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3086_: u8 = 0;
    let mut v_key_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3085_) == 0 {
                    v___x_3086_ = 0;
                    return v___x_3086_;
                } else {
                    v_key_3087_ = leanh::lean_ctor_get(v_x_3085_, 0);
                    v_tail_3088_ = leanh::lean_ctor_get(v_x_3085_, 2);
                    v___x_3089_ = lean_string_dec_eq(v_key_3087_, v_a_3084_);
                    if v___x_3089_ == 0 {
                        v_x_3085_ = v_tail_3088_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3089_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(
    mut v_a_3091_: *mut leanh::LeanObject,
    mut v_x_3092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3093_: u8 = 0;
    let mut v_r_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_3091_, v_x_3092_);
    leanh::lean_dec(v_x_3092_);
    leanh::lean_dec_ref(v_a_3091_);
    v_r_3094_ = leanh::lean_box((v_res_3093_) as usize);
    return v_r_3094_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3095_: *mut leanh::LeanObject,
    mut v_x_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u64 = 0;
    let mut v___x_3105_: u64 = 0;
    let mut v___x_3106_: u64 = 0;
    let mut v_fold_3107_: u64 = 0;
    let mut v___x_3108_: u64 = 0;
    let mut v___x_3109_: u64 = 0;
    let mut v___x_3110_: u64 = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: usize = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3096_) == 0 {
                    return v_x_3095_;
                } else {
                    v_key_3097_ = leanh::lean_ctor_get(v_x_3096_, 0);
                    v_value_3098_ = leanh::lean_ctor_get(v_x_3096_, 1);
                    v_tail_3099_ = leanh::lean_ctor_get(v_x_3096_, 2);
                    v_isSharedCheck_3122_ = (!leanh::lean_is_exclusive(v_x_3096_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3101_ = v_x_3096_;
                        v_isShared_3102_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3099_);
                        leanh::lean_inc(v_value_3098_);
                        leanh::lean_inc(v_key_3097_);
                        leanh::lean_dec(v_x_3096_);
                        v___x_3101_ = leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3103_ = lean_array_get_size(v_x_3095_);
                v___x_3104_ = lean_string_hash(v_key_3097_);
                v___x_3105_ = 32u64;
                v___x_3106_ = lean_uint64_shift_right(v___x_3104_, v___x_3105_);
                v_fold_3107_ = lean_uint64_xor(v___x_3104_, v___x_3106_);
                v___x_3108_ = 16u64;
                v___x_3109_ = lean_uint64_shift_right(v_fold_3107_, v___x_3108_);
                v___x_3110_ = lean_uint64_xor(v_fold_3107_, v___x_3109_);
                v___x_3111_ = lean_uint64_to_usize(v___x_3110_);
                v___x_3112_ = lean_usize_of_nat(v___x_3103_);
                v___x_3113_ = 1usize;
                v___x_3114_ = lean_usize_sub(v___x_3112_, v___x_3113_);
                v___x_3115_ = lean_usize_land(v___x_3111_, v___x_3114_);
                v___x_3116_ = lean_array_uget_borrowed(v_x_3095_, v___x_3115_);
                leanh::lean_inc(v___x_3116_);
                if v_isShared_3102_ == 0 {
                    leanh::lean_ctor_set(v___x_3101_, 2, v___x_3116_);
                    v___x_3118_ = v___x_3101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_key_3097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_value_3098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 2, v___x_3116_);
                    v___x_3118_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3119_ = lean_array_uset(v_x_3095_, v___x_3115_, v___x_3118_);
                v_x_3095_ = v___x_3119_;
                v_x_3096_ = v_tail_3099_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(
    mut v_i_3123_: *mut leanh::LeanObject,
    mut v_source_3124_: *mut leanh::LeanObject,
    mut v_target_3125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v_es_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3126_ = lean_array_get_size(v_source_3124_);
                v___x_3127_ = lean_nat_dec_lt(v_i_3123_, v___x_3126_);
                if v___x_3127_ == 0 {
                    leanh::lean_dec_ref(v_source_3124_);
                    leanh::lean_dec(v_i_3123_);
                    return v_target_3125_;
                } else {
                    v_es_3128_ = lean_array_fget(v_source_3124_, v_i_3123_);
                    v___x_3129_ = leanh::lean_box(0);
                    v_source_3130_ = lean_array_fset(v_source_3124_, v_i_3123_, v___x_3129_);
                    v_target_3131_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3125_, v_es_3128_);
                    v___x_3132_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3133_ = lean_nat_add(v_i_3123_, v___x_3132_);
                    leanh::lean_dec(v_i_3123_);
                    v_i_3123_ = v___x_3133_;
                    v_source_3124_ = v_source_3130_;
                    v_target_3125_ = v_target_3131_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(
    mut v_data_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3136_ = lean_array_get_size(v_data_3135_);
    v___x_3137_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3138_ = lean_nat_mul(v___x_3136_, v___x_3137_);
    v___x_3139_ = leanh::lean_unsigned_to_nat(0);
    v___x_3140_ = leanh::lean_box(0);
    v___x_3141_ = lean_mk_array(v_nbuckets_3138_, v___x_3140_);
    v___x_3142_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_3139_, v_data_3135_, v___x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(
    mut v_i_3143_: *mut leanh::LeanObject,
    mut v_m_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u64 = 0;
    let mut v___x_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v_fold_3155_: u64 = 0;
    let mut v___x_3156_: u64 = 0;
    let mut v___x_3157_: u64 = 0;
    let mut v___x_3158_: u64 = 0;
    let mut v___x_3159_: usize = 0;
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v_bkt_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v_val_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3146_ = leanh::lean_ctor_get(v_m_3144_, 0);
                v_buckets_3147_ = leanh::lean_ctor_get(v_m_3144_, 1);
                v_isSharedCheck_3197_ = (!leanh::lean_is_exclusive(v_m_3144_)) as u8;
                if v_isSharedCheck_3197_ == 0 {
                    v___x_3149_ = v_m_3144_;
                    v_isShared_3150_ = v_isSharedCheck_3197_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3147_);
                    leanh::lean_inc(v_size_3146_);
                    leanh::lean_dec(v_m_3144_);
                    v___x_3149_ = leanh::lean_box(0);
                    v_isShared_3150_ = v_isSharedCheck_3197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3151_ = lean_array_get_size(v_buckets_3147_);
                v___x_3152_ = lean_string_hash(v_a_3145_);
                v___x_3153_ = 32u64;
                v___x_3154_ = lean_uint64_shift_right(v___x_3152_, v___x_3153_);
                v_fold_3155_ = lean_uint64_xor(v___x_3152_, v___x_3154_);
                v___x_3156_ = 16u64;
                v___x_3157_ = lean_uint64_shift_right(v_fold_3155_, v___x_3156_);
                v___x_3158_ = lean_uint64_xor(v_fold_3155_, v___x_3157_);
                v___x_3159_ = lean_uint64_to_usize(v___x_3158_);
                v___x_3160_ = lean_usize_of_nat(v___x_3151_);
                v___x_3161_ = 1usize;
                v___x_3162_ = lean_usize_sub(v___x_3160_, v___x_3161_);
                v___x_3163_ = lean_usize_land(v___x_3159_, v___x_3162_);
                v_bkt_3164_ = lean_array_uget_borrowed(v_buckets_3147_, v___x_3163_);
                v___x_3165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_3145_, v_bkt_3164_);
                if v___x_3165_ == 0 {
                    v___x_3166_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3167_ = lean_mk_empty_array_with_capacity(v___x_3166_);
                    v___x_3168_ = lean_array_push(v___x_3167_, v_i_3143_);
                    v_size_x27_3169_ = lean_nat_add(v_size_3146_, v___x_3166_);
                    leanh::lean_dec(v_size_3146_);
                    leanh::lean_inc(v_bkt_3164_);
                    v___x_3170_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3170_, 0, v_a_3145_);
                    leanh::lean_ctor_set(v___x_3170_, 1, v___x_3168_);
                    leanh::lean_ctor_set(v___x_3170_, 2, v_bkt_3164_);
                    v_buckets_x27_3171_ =
                        lean_array_uset(v_buckets_3147_, v___x_3163_, v___x_3170_);
                    v___x_3172_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3173_ = lean_nat_mul(v_size_x27_3169_, v___x_3172_);
                    v___x_3174_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3175_ = lean_nat_div(v___x_3173_, v___x_3174_);
                    leanh::lean_dec(v___x_3173_);
                    v___x_3176_ = lean_array_get_size(v_buckets_x27_3171_);
                    v___x_3177_ = lean_nat_dec_le(v___x_3175_, v___x_3176_);
                    leanh::lean_dec(v___x_3175_);
                    if v___x_3177_ == 0 {
                        v_val_3178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_3171_);
                        if v_isShared_3150_ == 0 {
                            leanh::lean_ctor_set(v___x_3149_, 1, v_val_3178_);
                            leanh::lean_ctor_set(v___x_3149_, 0, v_size_x27_3169_);
                            v___x_3180_ = v___x_3149_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3181_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3181_,
                                0,
                                v_size_x27_3169_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_val_3178_);
                            v___x_3180_ = v_reuseFailAlloc_3181_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3150_ == 0 {
                            leanh::lean_ctor_set(v___x_3149_, 1, v_buckets_x27_3171_);
                            leanh::lean_ctor_set(v___x_3149_, 0, v_size_x27_3169_);
                            v___x_3183_ = v___x_3149_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3184_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3184_,
                                0,
                                v_size_x27_3169_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3184_,
                                1,
                                v_buckets_x27_3171_,
                            );
                            v___x_3183_ = v_reuseFailAlloc_3184_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3164_);
                    v___x_3185_ = leanh::lean_box(0);
                    v_buckets_x27_3186_ =
                        lean_array_uset(v_buckets_3147_, v___x_3163_, v___x_3185_);
                    leanh::lean_inc_ref(v_a_3145_);
                    v_bkt_x27_3187_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_3143_, v_a_3145_, v_bkt_3164_);
                    v___x_3194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_3145_, v_bkt_x27_3187_);
                    leanh::lean_dec_ref(v_a_3145_);
                    if v___x_3194_ == 0 {
                        v___x_3195_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3196_ = lean_nat_sub(v_size_3146_, v___x_3195_);
                        leanh::lean_dec(v_size_3146_);
                        v___y_3189_ = v___x_3196_;
                        state = 4;
                        continue;
                    } else {
                        v___y_3189_ = v_size_3146_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3180_;
            }
            3 => {
                return v___x_3183_;
            }
            4 => {
                v___x_3190_ = lean_array_uset(v_buckets_x27_3186_, v___x_3163_, v_bkt_x27_3187_);
                if v_isShared_3150_ == 0 {
                    leanh::lean_ctor_set(v___x_3149_, 1, v___x_3190_);
                    leanh::lean_ctor_set(v___x_3149_, 0, v___y_3189_);
                    v___x_3192_ = v___x_3149_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___y_3189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3190_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_header(
    mut v_builder_3198_: *mut leanh::LeanObject,
    mut v_key_3199_: *mut leanh::LeanObject,
    mut v_value_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v_method_3207_: u8 = 0;
    let mut v_version_3208_: u8 = 0;
    let mut v_uri_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v_entries_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v_i_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_unused_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_unused_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_3201_ = leanh::lean_ctor_get(v_builder_3198_, 0);
                leanh::lean_inc_ref(v_line_3201_);
                v_headers_3202_ = leanh::lean_ctor_get(v_line_3201_, 1);
                leanh::lean_inc_ref(v_headers_3202_);
                v_extensions_3203_ = leanh::lean_ctor_get(v_builder_3198_, 1);
                v_isSharedCheck_3234_ = (!leanh::lean_is_exclusive(v_builder_3198_)) as u8;
                if v_isSharedCheck_3234_ == 0 {
                    v_unused_3235_ = leanh::lean_ctor_get(v_builder_3198_, 0);
                    leanh::lean_dec(v_unused_3235_);
                    v___x_3205_ = v_builder_3198_;
                    v_isShared_3206_ = v_isSharedCheck_3234_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_3203_);
                    leanh::lean_dec(v_builder_3198_);
                    v___x_3205_ = leanh::lean_box(0);
                    v_isShared_3206_ = v_isSharedCheck_3234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_method_3207_ = leanh::lean_ctor_get_uint8(
                    v_line_3201_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_3208_ = leanh::lean_ctor_get_uint8(
                    v_line_3201_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_3209_ = leanh::lean_ctor_get(v_line_3201_, 0);
                v_isSharedCheck_3232_ = (!leanh::lean_is_exclusive(v_line_3201_)) as u8;
                if v_isSharedCheck_3232_ == 0 {
                    v_unused_3233_ = leanh::lean_ctor_get(v_line_3201_, 1);
                    leanh::lean_dec(v_unused_3233_);
                    v___x_3211_ = v_line_3201_;
                    v_isShared_3212_ = v_isSharedCheck_3232_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uri_3209_);
                    leanh::lean_dec(v_line_3201_);
                    v___x_3211_ = leanh::lean_box(0);
                    v_isShared_3212_ = v_isSharedCheck_3232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_3213_ = leanh::lean_ctor_get(v_headers_3202_, 0);
                v_indexes_3214_ = leanh::lean_ctor_get(v_headers_3202_, 1);
                v_isSharedCheck_3231_ = (!leanh::lean_is_exclusive(v_headers_3202_)) as u8;
                if v_isSharedCheck_3231_ == 0 {
                    v___x_3216_ = v_headers_3202_;
                    v_isShared_3217_ = v_isSharedCheck_3231_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_3214_);
                    leanh::lean_inc(v_entries_3213_);
                    leanh::lean_dec(v_headers_3202_);
                    v___x_3216_ = leanh::lean_box(0);
                    v_isShared_3217_ = v_isSharedCheck_3231_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_3218_ = lean_array_get_size(v_entries_3213_);
                leanh::lean_inc_ref(v_key_3199_);
                v___x_3219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3219_, 0, v_key_3199_);
                leanh::lean_ctor_set(v___x_3219_, 1, v_value_3200_);
                v_entries_3220_ = lean_array_push(v_entries_3213_, v___x_3219_);
                v_indexes_3221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_3218_, v_indexes_3214_, v_key_3199_);
                if v_isShared_3217_ == 0 {
                    leanh::lean_ctor_set(v___x_3216_, 1, v_indexes_3221_);
                    leanh::lean_ctor_set(v___x_3216_, 0, v_entries_3220_);
                    v___x_3223_ = v___x_3216_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_entries_3220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_indexes_3221_);
                    v___x_3223_ = v_reuseFailAlloc_3230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3212_ == 0 {
                    leanh::lean_ctor_set(v___x_3211_, 1, v___x_3223_);
                    v___x_3225_ = v___x_3211_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_uri_3209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3223_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3229_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_3207_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3229_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_3208_,
                    );
                    v___x_3225_ = v_reuseFailAlloc_3229_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3206_ == 0 {
                    leanh::lean_ctor_set(v___x_3205_, 0, v___x_3225_);
                    v___x_3227_ = v___x_3205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3228_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_extensions_3203_);
                    v___x_3227_ = v_reuseFailAlloc_3228_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(
    mut v_00_u03b2_3236_: *mut leanh::LeanObject,
    mut v_a_3237_: *mut leanh::LeanObject,
    mut v_x_3238_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3239_: u8 = 0;
    v___x_3239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_3237_, v_x_3238_);
    return v___x_3239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(
    mut v_00_u03b2_3240_: *mut leanh::LeanObject,
    mut v_a_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3243_: u8 = 0;
    let mut v_r_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_3240_, v_a_3241_, v_x_3242_);
    leanh::lean_dec(v_x_3242_);
    leanh::lean_dec_ref(v_a_3241_);
    v_r_3244_ = leanh::lean_box((v_res_3243_) as usize);
    return v_r_3244_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(
    mut v_00_u03b2_3245_: *mut leanh::LeanObject,
    mut v_data_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_3246_);
    return v___x_3247_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3248_: *mut leanh::LeanObject,
    mut v_i_3249_: *mut leanh::LeanObject,
    mut v_source_3250_: *mut leanh::LeanObject,
    mut v_target_3251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_3249_, v_source_3250_, v_target_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3253_: *mut leanh::LeanObject,
    mut v_x_3254_: *mut leanh::LeanObject,
    mut v_x_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3254_, v_x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Std_Http_Request_Builder_header_x21(
    mut v_builder_3257_: *mut leanh::LeanObject,
    mut v_key_3258_: *mut leanh::LeanObject,
    mut v_value_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v_method_3266_: u8 = 0;
    let mut v_version_3267_: u8 = 0;
    let mut v_uri_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v_entries_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v_key_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_unused_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_3260_ = leanh::lean_ctor_get(v_builder_3257_, 0);
                leanh::lean_inc_ref(v_line_3260_);
                v_headers_3261_ = leanh::lean_ctor_get(v_line_3260_, 1);
                leanh::lean_inc_ref(v_headers_3261_);
                v_extensions_3262_ = leanh::lean_ctor_get(v_builder_3257_, 1);
                v_isSharedCheck_3295_ = (!leanh::lean_is_exclusive(v_builder_3257_)) as u8;
                if v_isSharedCheck_3295_ == 0 {
                    v_unused_3296_ = leanh::lean_ctor_get(v_builder_3257_, 0);
                    leanh::lean_dec(v_unused_3296_);
                    v___x_3264_ = v_builder_3257_;
                    v_isShared_3265_ = v_isSharedCheck_3295_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_3262_);
                    leanh::lean_dec(v_builder_3257_);
                    v___x_3264_ = leanh::lean_box(0);
                    v_isShared_3265_ = v_isSharedCheck_3295_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_method_3266_ = leanh::lean_ctor_get_uint8(
                    v_line_3260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_3267_ = leanh::lean_ctor_get_uint8(
                    v_line_3260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_3268_ = leanh::lean_ctor_get(v_line_3260_, 0);
                v_isSharedCheck_3293_ = (!leanh::lean_is_exclusive(v_line_3260_)) as u8;
                if v_isSharedCheck_3293_ == 0 {
                    v_unused_3294_ = leanh::lean_ctor_get(v_line_3260_, 1);
                    leanh::lean_dec(v_unused_3294_);
                    v___x_3270_ = v_line_3260_;
                    v_isShared_3271_ = v_isSharedCheck_3293_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uri_3268_);
                    leanh::lean_dec(v_line_3260_);
                    v___x_3270_ = leanh::lean_box(0);
                    v_isShared_3271_ = v_isSharedCheck_3293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_3272_ = leanh::lean_ctor_get(v_headers_3261_, 0);
                v_indexes_3273_ = leanh::lean_ctor_get(v_headers_3261_, 1);
                v_isSharedCheck_3292_ = (!leanh::lean_is_exclusive(v_headers_3261_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v___x_3275_ = v_headers_3261_;
                    v_isShared_3276_ = v_isSharedCheck_3292_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_3273_);
                    leanh::lean_inc(v_entries_3272_);
                    leanh::lean_dec(v_headers_3261_);
                    v___x_3275_ = leanh::lean_box(0);
                    v_isShared_3276_ = v_isSharedCheck_3292_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_key_3277_ = l_Std_Http_Header_Name_ofString_x21(v_key_3258_);
                v_value_3278_ = l_Std_Http_Header_Value_ofString_x21(v_value_3259_);
                v_i_3279_ = lean_array_get_size(v_entries_3272_);
                leanh::lean_inc_ref(v_key_3277_);
                v___x_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3280_, 0, v_key_3277_);
                leanh::lean_ctor_set(v___x_3280_, 1, v_value_3278_);
                v_entries_3281_ = lean_array_push(v_entries_3272_, v___x_3280_);
                v_indexes_3282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_3279_, v_indexes_3273_, v_key_3277_);
                if v_isShared_3276_ == 0 {
                    leanh::lean_ctor_set(v___x_3275_, 1, v_indexes_3282_);
                    leanh::lean_ctor_set(v___x_3275_, 0, v_entries_3281_);
                    v___x_3284_ = v___x_3275_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_entries_3281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_indexes_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3291_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3271_ == 0 {
                    leanh::lean_ctor_set(v___x_3270_, 1, v___x_3284_);
                    v___x_3286_ = v___x_3270_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_uri_3268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 1, v___x_3284_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3290_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_3266_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3290_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_3267_,
                    );
                    v___x_3286_ = v_reuseFailAlloc_3290_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3265_ == 0 {
                    leanh::lean_ctor_set(v___x_3264_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3264_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_extensions_3262_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_header_x3f(
    mut v_builder_3297_: *mut leanh::LeanObject,
    mut v_key_3298_: *mut leanh::LeanObject,
    mut v_value_3299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v_extensions_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v_method_3315_: u8 = 0;
    let mut v_version_3316_: u8 = 0;
    let mut v_uri_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v_entries_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v_i_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut v_isSharedCheck_3343_: u8 = 0;
    let mut v_unused_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v_unused_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3300_ = l_Std_Http_Header_Name_ofString_x3f(v_key_3298_);
                if leanh::lean_obj_tag(v___x_3300_) == 0 {
                    leanh::lean_dec_ref(v_value_3299_);
                    leanh::lean_dec_ref(v_builder_3297_);
                    v___x_3301_ = leanh::lean_box(0);
                    return v___x_3301_;
                } else {
                    v_val_3302_ = leanh::lean_ctor_get(v___x_3300_, 0);
                    leanh::lean_inc(v_val_3302_);
                    leanh::lean_dec_ref_known(v___x_3300_, 1);
                    v___x_3303_ = l_Std_Http_Header_Value_ofString_x3f(v_value_3299_);
                    if leanh::lean_obj_tag(v___x_3303_) == 0 {
                        leanh::lean_dec(v_val_3302_);
                        leanh::lean_dec_ref(v_builder_3297_);
                        v___x_3304_ = leanh::lean_box(0);
                        return v___x_3304_;
                    } else {
                        v_line_3305_ = leanh::lean_ctor_get(v_builder_3297_, 0);
                        leanh::lean_inc_ref(v_line_3305_);
                        v_headers_3306_ = leanh::lean_ctor_get(v_line_3305_, 1);
                        leanh::lean_inc_ref(v_headers_3306_);
                        v_val_3307_ = leanh::lean_ctor_get(v___x_3303_, 0);
                        v_isSharedCheck_3347_ =
                            (!leanh::lean_is_exclusive(v___x_3303_)) as u8;
                        if v_isSharedCheck_3347_ == 0 {
                            v___x_3309_ = v___x_3303_;
                            v_isShared_3310_ = v_isSharedCheck_3347_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3307_);
                            leanh::lean_dec(v___x_3303_);
                            v___x_3309_ = leanh::lean_box(0);
                            v_isShared_3310_ = v_isSharedCheck_3347_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_extensions_3311_ = leanh::lean_ctor_get(v_builder_3297_, 1);
                v_isSharedCheck_3345_ = (!leanh::lean_is_exclusive(v_builder_3297_)) as u8;
                if v_isSharedCheck_3345_ == 0 {
                    v_unused_3346_ = leanh::lean_ctor_get(v_builder_3297_, 0);
                    leanh::lean_dec(v_unused_3346_);
                    v___x_3313_ = v_builder_3297_;
                    v_isShared_3314_ = v_isSharedCheck_3345_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_3311_);
                    leanh::lean_dec(v_builder_3297_);
                    v___x_3313_ = leanh::lean_box(0);
                    v_isShared_3314_ = v_isSharedCheck_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_method_3315_ = leanh::lean_ctor_get_uint8(
                    v_line_3305_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_3316_ = leanh::lean_ctor_get_uint8(
                    v_line_3305_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_3317_ = leanh::lean_ctor_get(v_line_3305_, 0);
                v_isSharedCheck_3343_ = (!leanh::lean_is_exclusive(v_line_3305_)) as u8;
                if v_isSharedCheck_3343_ == 0 {
                    v_unused_3344_ = leanh::lean_ctor_get(v_line_3305_, 1);
                    leanh::lean_dec(v_unused_3344_);
                    v___x_3319_ = v_line_3305_;
                    v_isShared_3320_ = v_isSharedCheck_3343_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_uri_3317_);
                    leanh::lean_dec(v_line_3305_);
                    v___x_3319_ = leanh::lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_entries_3321_ = leanh::lean_ctor_get(v_headers_3306_, 0);
                v_indexes_3322_ = leanh::lean_ctor_get(v_headers_3306_, 1);
                v_isSharedCheck_3342_ = (!leanh::lean_is_exclusive(v_headers_3306_)) as u8;
                if v_isSharedCheck_3342_ == 0 {
                    v___x_3324_ = v_headers_3306_;
                    v_isShared_3325_ = v_isSharedCheck_3342_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_3322_);
                    leanh::lean_inc(v_entries_3321_);
                    leanh::lean_dec(v_headers_3306_);
                    v___x_3324_ = leanh::lean_box(0);
                    v_isShared_3325_ = v_isSharedCheck_3342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_i_3326_ = lean_array_get_size(v_entries_3321_);
                leanh::lean_inc(v_val_3302_);
                v___x_3327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3327_, 0, v_val_3302_);
                leanh::lean_ctor_set(v___x_3327_, 1, v_val_3307_);
                v_entries_3328_ = lean_array_push(v_entries_3321_, v___x_3327_);
                v_indexes_3329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_3326_, v_indexes_3322_, v_val_3302_);
                if v_isShared_3325_ == 0 {
                    leanh::lean_ctor_set(v___x_3324_, 1, v_indexes_3329_);
                    leanh::lean_ctor_set(v___x_3324_, 0, v_entries_3328_);
                    v___x_3331_ = v___x_3324_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_entries_3328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_indexes_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3341_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3320_ == 0 {
                    leanh::lean_ctor_set(v___x_3319_, 1, v___x_3331_);
                    v___x_3333_ = v___x_3319_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_uri_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3331_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3340_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_3315_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3340_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_3316_,
                    );
                    v___x_3333_ = v_reuseFailAlloc_3340_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3314_ == 0 {
                    leanh::lean_ctor_set(v___x_3313_, 0, v___x_3333_);
                    v___x_3335_ = v___x_3313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_extensions_3311_);
                    v___x_3335_ = v_reuseFailAlloc_3339_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3310_ == 0 {
                    leanh::lean_ctor_set(v___x_3309_, 0, v___x_3335_);
                    v___x_3337_ = v___x_3309_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3338_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
                    v___x_3337_ = v_reuseFailAlloc_3338_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_headerOpt(
    mut v_builder_3348_: *mut leanh::LeanObject,
    mut v_key_3349_: *mut leanh::LeanObject,
    mut v_value_3350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_value_3350_) == 0 {
        leanh::lean_dec_ref(v_key_3349_);
        return v_builder_3348_;
    } else {
        let mut v_val_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3351_ = leanh::lean_ctor_get(v_value_3350_, 0);
        leanh::lean_inc(v_val_3351_);
        leanh::lean_dec_ref_known(v_value_3350_, 1);
        v___x_3352_ = l_Std_Http_Request_Builder_header(v_builder_3348_, v_key_3349_, v_val_3351_);
        return v___x_3352_;
    }
}
pub unsafe fn l_Std_Http_Request_Builder_extension___redArg(
    mut v_builder_3354_: *mut leanh::LeanObject,
    mut v_inst_3355_: *mut leanh::LeanObject,
    mut v_data_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v_dyn_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_3357_ = leanh::lean_ctor_get(v_builder_3354_, 0);
                v_extensions_3358_ = leanh::lean_ctor_get(v_builder_3354_, 1);
                v_isSharedCheck_3369_ = (!leanh::lean_is_exclusive(v_builder_3354_)) as u8;
                if v_isSharedCheck_3369_ == 0 {
                    v___x_3360_ = v_builder_3354_;
                    v_isShared_3361_ = v_isSharedCheck_3369_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_3358_);
                    leanh::lean_inc(v_line_3357_);
                    leanh::lean_dec(v_builder_3354_);
                    v___x_3360_ = leanh::lean_box(0);
                    v_isShared_3361_ = v_isSharedCheck_3369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dyn_3362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_dyn_3362_, 0, v_inst_3355_);
                leanh::lean_ctor_set(v_dyn_3362_, 1, v_data_3356_);
                v___x_3363_ = l_Std_Http_Request_Builder_extension___redArg___closed__0;
                v___x_3364_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_3362_);
                v___x_3365_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_3363_,
                    v___x_3364_,
                    v_dyn_3362_,
                    v_extensions_3358_,
                );
                if v_isShared_3361_ == 0 {
                    leanh::lean_ctor_set(v___x_3360_, 1, v___x_3365_);
                    v___x_3367_ = v___x_3360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_line_3357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3365_);
                    v___x_3367_ = v_reuseFailAlloc_3368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_extension(
    mut v_00_u03b1_3370_: *mut leanh::LeanObject,
    mut v_builder_3371_: *mut leanh::LeanObject,
    mut v_inst_3372_: *mut leanh::LeanObject,
    mut v_data_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3374_ =
        l_Std_Http_Request_Builder_extension___redArg(v_builder_3371_, v_inst_3372_, v_data_3373_);
    return v___x_3374_;
}
pub unsafe fn l_Std_Http_Request_Builder_body___redArg(
    mut v_builder_3375_: *mut leanh::LeanObject,
    mut v_body_3376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_line_3377_ = leanh::lean_ctor_get(v_builder_3375_, 0);
    v_extensions_3378_ = leanh::lean_ctor_get(v_builder_3375_, 1);
    leanh::lean_inc(v_extensions_3378_);
    leanh::lean_inc_ref(v_line_3377_);
    v___x_3379_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3379_, 0, v_line_3377_);
    leanh::lean_ctor_set(v___x_3379_, 1, v_body_3376_);
    leanh::lean_ctor_set(v___x_3379_, 2, v_extensions_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Std_Http_Request_Builder_body___redArg___boxed(
    mut v_builder_3380_: *mut leanh::LeanObject,
    mut v_body_3381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3382_ = l_Std_Http_Request_Builder_body___redArg(v_builder_3380_, v_body_3381_);
    leanh::lean_dec_ref(v_builder_3380_);
    return v_res_3382_;
}
pub unsafe fn l_Std_Http_Request_Builder_body(
    mut v_t_3383_: *mut leanh::LeanObject,
    mut v_builder_3384_: *mut leanh::LeanObject,
    mut v_body_3385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3386_ = l_Std_Http_Request_Builder_body___redArg(v_builder_3384_, v_body_3385_);
    return v___x_3386_;
}
pub unsafe fn l_Std_Http_Request_Builder_body___boxed(
    mut v_t_3387_: *mut leanh::LeanObject,
    mut v_builder_3388_: *mut leanh::LeanObject,
    mut v_body_3389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3390_ = l_Std_Http_Request_Builder_body(v_t_3387_, v_builder_3388_, v_body_3389_);
    leanh::lean_dec_ref(v_builder_3388_);
    return v_res_3390_;
}
pub unsafe fn _init_l_Std_Http_Request_get___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = 8;
    v___x_3392_ = l_Std_Http_Request_new;
    v___x_3393_ = l_Std_Http_Request_Builder_method(v___x_3392_, v___x_3391_);
    return v___x_3393_;
}
pub unsafe fn l_Std_Http_Request_get(
    mut v_uri_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_get___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_get___closed__0_once),
        _init_l_Std_Http_Request_get___closed__0,
    );
    v___x_3396_ = l_Std_Http_Request_Builder_uri(v___x_3395_, v_uri_3394_);
    return v___x_3396_;
}
pub unsafe fn _init_l_Std_Http_Request_post___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = 23;
    v___x_3398_ = l_Std_Http_Request_new;
    v___x_3399_ = l_Std_Http_Request_Builder_method(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn l_Std_Http_Request_post(
    mut v_uri_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_post___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_post___closed__0_once),
        _init_l_Std_Http_Request_post___closed__0,
    );
    v___x_3402_ = l_Std_Http_Request_Builder_uri(v___x_3401_, v_uri_3400_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Std_Http_Request_put___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = 27;
    v___x_3404_ = l_Std_Http_Request_new;
    v___x_3405_ = l_Std_Http_Request_Builder_method(v___x_3404_, v___x_3403_);
    return v___x_3405_;
}
pub unsafe fn l_Std_Http_Request_put(
    mut v_uri_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_put___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_put___closed__0_once),
        _init_l_Std_Http_Request_put___closed__0,
    );
    v___x_3408_ = l_Std_Http_Request_Builder_uri(v___x_3407_, v_uri_3406_);
    return v___x_3408_;
}
pub unsafe fn _init_l_Std_Http_Request_delete___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = 7;
    v___x_3410_ = l_Std_Http_Request_new;
    v___x_3411_ = l_Std_Http_Request_Builder_method(v___x_3410_, v___x_3409_);
    return v___x_3411_;
}
pub unsafe fn l_Std_Http_Request_delete(
    mut v_uri_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_delete___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_delete___closed__0_once),
        _init_l_Std_Http_Request_delete___closed__0,
    );
    v___x_3414_ = l_Std_Http_Request_Builder_uri(v___x_3413_, v_uri_3412_);
    return v___x_3414_;
}
pub unsafe fn _init_l_Std_Http_Request_patch___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = 22;
    v___x_3416_ = l_Std_Http_Request_new;
    v___x_3417_ = l_Std_Http_Request_Builder_method(v___x_3416_, v___x_3415_);
    return v___x_3417_;
}
pub unsafe fn l_Std_Http_Request_patch(
    mut v_uri_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_patch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_patch___closed__0_once),
        _init_l_Std_Http_Request_patch___closed__0,
    );
    v___x_3420_ = l_Std_Http_Request_Builder_uri(v___x_3419_, v_uri_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l_Std_Http_Request_head___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3421_: u8 = 0;
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = 9;
    v___x_3422_ = l_Std_Http_Request_new;
    v___x_3423_ = l_Std_Http_Request_Builder_method(v___x_3422_, v___x_3421_);
    return v___x_3423_;
}
pub unsafe fn l_Std_Http_Request_head(
    mut v_uri_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_head___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_head___closed__0_once),
        _init_l_Std_Http_Request_head___closed__0,
    );
    v___x_3426_ = l_Std_Http_Request_Builder_uri(v___x_3425_, v_uri_3424_);
    return v___x_3426_;
}
pub unsafe fn _init_l_Std_Http_Request_options___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = 20;
    v___x_3428_ = l_Std_Http_Request_new;
    v___x_3429_ = l_Std_Http_Request_Builder_method(v___x_3428_, v___x_3427_);
    return v___x_3429_;
}
pub unsafe fn l_Std_Http_Request_options(
    mut v_uri_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_options___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_options___closed__0_once),
        _init_l_Std_Http_Request_options___closed__0,
    );
    v___x_3432_ = l_Std_Http_Request_Builder_uri(v___x_3431_, v_uri_3430_);
    return v___x_3432_;
}
pub unsafe fn _init_l_Std_Http_Request_connect___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = 5;
    v___x_3434_ = l_Std_Http_Request_new;
    v___x_3435_ = l_Std_Http_Request_Builder_method(v___x_3434_, v___x_3433_);
    return v___x_3435_;
}
pub unsafe fn l_Std_Http_Request_connect(
    mut v_uri_3436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_connect___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_connect___closed__0_once),
        _init_l_Std_Http_Request_connect___closed__0,
    );
    v___x_3438_ = l_Std_Http_Request_Builder_uri(v___x_3437_, v_uri_3436_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Std_Http_Request_trace___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = 32;
    v___x_3440_ = l_Std_Http_Request_new;
    v___x_3441_ = l_Std_Http_Request_Builder_method(v___x_3440_, v___x_3439_);
    return v___x_3441_;
}
pub unsafe fn l_Std_Http_Request_trace(
    mut v_uri_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_trace___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Request_trace___closed__0_once),
        _init_l_Std_Http_Request_trace___closed__0,
    );
    v___x_3444_ = l_Std_Http_Request_Builder_uri(v___x_3443_, v_uri_3442_);
    return v___x_3444_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Request(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Method(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Http_Request_instInhabitedHead_default =
        _init_l_Std_Http_Request_instInhabitedHead_default();
    leanh::lean_mark_persistent(l_Std_Http_Request_instInhabitedHead_default);
    l_Std_Http_Request_instInhabitedHead = _init_l_Std_Http_Request_instInhabitedHead();
    leanh::lean_mark_persistent(l_Std_Http_Request_instInhabitedHead);
    l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1 =
        _init_l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1,
    );
    l_Std_Http_Request_new = _init_l_Std_Http_Request_new();
    leanh::lean_mark_persistent(l_Std_Http_Request_new);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Request(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Request(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Method(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_URI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Request(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Request(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Request(builtin);
}