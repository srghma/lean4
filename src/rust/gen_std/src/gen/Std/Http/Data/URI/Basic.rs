// Lean compiler output
// Module: Std.Http.Data.URI.Basic
// Imports: Init.Data.ToString Std.Net Std.Http.Internal Std.Http.Data.URI.Encoding Init.Data.String.Search Init.Data.String.Length
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_pop, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_sarray_dec_eq,
    lean_string_append, lean_string_data, lean_string_dec_eq, lean_string_from_utf8_unchecked,
    lean_string_length, lean_string_to_utf8, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set, lean_uint8_dec_eq,
    lean_uint8_dec_le, lean_uint16_dec_eq, lean_uint16_to_nat, lean_uint32_add, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_nat, lean_uint32_to_uint8, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat, lean_uv_ntop_v4, lean_uv_ntop_v6,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
    l_Array_isEqvAux___redArg, l_Array_repr___redArg,
};
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_decEq___boxed;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_eraseDupsBy___redArg, l_List_getLast_x3f___redArg, l_List_head_x3f___redArg,
    l_List_mapTR_loop___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Option_repr___boxed, l_Prod_repr___boxed,
    l_Repr_addAppParen, l_String_quote, l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Prelude::{l_Char_utf8Size, l_List_lengthTR___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Http::Data::URI::Encoding::{
    initialize_Std_Http_Data_URI_Encoding, l_Std_Http_URI_EncodedFragment_encode,
    l_Std_Http_URI_EncodedQueryParam_decode, l_Std_Http_URI_EncodedQueryParam_encode,
    l_Std_Http_URI_EncodedSegment_decode, l_Std_Http_URI_EncodedSegment_encode,
    l_Std_Http_URI_EncodedString_empty, l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed,
    l_Std_Http_URI_EncodedUserInfo_decode, l_Std_Http_URI_EncodedUserInfo_encode,
    runtime_initialize_Std_Http_Data_URI_Encoding,
};
use crate::r#gen::Std::Http::Internal::LowerCase::l_Std_Http_Internal_instDecidableIsLowerCase;
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Net::Addr::{
    l_Std_Net_instDecidableEqIPv4Addr_decEq, l_Std_Net_instDecidableEqIPv6Addr_decEq,
    l_Std_Net_instInhabitedIPv4Addr_default,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
pub static l_Std_Http_URI_instInhabitedScheme___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [104, 116, 116, 112, 0],
    };
static mut l_Std_Http_URI_instInhabitedScheme___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedScheme___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedScheme: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedScheme___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Scheme_ofString_x21___closed__0_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 85, 82, 73, 46, 66, 97, 115,
        105, 99, 0,
    ],
};
static mut l_Std_Http_URI_Scheme_ofString_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Scheme_ofString_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Scheme_ofString_x21___closed__1_value: leanh::LeanStringObject<
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 83, 99, 104, 101, 109, 101, 46,
        111, 102, 83, 116, 114, 105, 110, 103, 33, 0,
    ],
};
static mut l_Std_Http_URI_Scheme_ofString_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Scheme_ofString_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Scheme_ofString_x21___closed__2_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 85, 82, 73, 32, 115, 99, 104, 101, 109, 101, 58, 32,
        0,
    ],
};
static mut l_Std_Http_URI_Scheme_ofString_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Scheme_ofString_x21___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Scheme_defaultPort___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [104, 116, 116, 112, 115, 0],
    };
static mut l_Std_Http_URI_Scheme_defaultPort___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Scheme_defaultPort___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20: u8 = 0;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21: u8 = 0;
pub static l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_value:
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
    m_fun: l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedUserInfo_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedUserInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedUserInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value:
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
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value:
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
    m_data: [117, 115, 101, 114, 110, 97, 109, 101, 0],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value:
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
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value:
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
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value:
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
    m_data: [112, 97, 115, 115, 119, 111, 114, 100, 0],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value:
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
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprUserInfo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprUserInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprUserInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprUserInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqUserInfo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instBEqUserInfo_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instBEqUserInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqUserInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instBEqUserInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqUserInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instInhabitedHost_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_instInhabitedHost_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedHost_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedHost: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_instBEqHost___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instBEqHost_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instBEqHost___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instBEqHost: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprHost___lam__0___closed__0_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_URI_instReprHost___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprHost___lam__0___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_URI_instReprHost___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprHost___lam__0___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_URI_instReprHost___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprHost___lam__0___closed__3_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_URI_instReprHost___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instReprHost___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_instReprHost___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_URI_instReprHost___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_instReprHost___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_instReprHost___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprHost___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprHost___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprHost: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringHost___lam__0___closed__0_value:
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
static mut l_Std_Http_URI_instToStringHost___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringHost___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringHost___lam__0___closed__1_value:
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
static mut l_Std_Http_URI_instToStringHost___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringHost___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringHost___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instToStringHost___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instToStringHost___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instToStringHost: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringHost___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedPort_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedPort: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_instReprPort_repr___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 80, 111, 114, 116, 46, 101,
            109, 112, 116, 121, 0,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__2_value: leanh::LeanStringObject<26> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 80, 111, 114, 116, 46, 111,
            109, 105, 116, 116, 101, 100, 0,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__4_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 80, 111, 114, 116, 46, 118,
            97, 108, 117, 101, 0,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort_repr___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__5_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_instReprPort_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPort___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprPort_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprPort___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprPort: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPort___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instInhabitedAuthority_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedAuthority_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_URI_instInhabitedAuthority: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value:
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
    m_data: [117, 115, 101, 114, 73, 110, 102, 111, 0],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value:
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
    m_data: [104, 111, 115, 116, 0],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value:
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
    m_data: [112, 111, 114, 116, 0],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprAuthority___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprAuthority_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprAuthority___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprAuthority: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqAuthority___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instBEqAuthority_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instBEqAuthority___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instBEqAuthority: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value:
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
static mut l_Std_Http_URI_instToStringAuthority___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value:
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
static mut l_Std_Http_URI_instToStringAuthority___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringAuthority___lam__0___closed__2_value:
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
static mut l_Std_Http_URI_instToStringAuthority___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringAuthority___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_URI_instToStringAuthority___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instToStringAuthority___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instToStringAuthority: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringAuthority___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instInhabitedPath_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_URI_instInhabitedPath_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instInhabitedPath_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__0_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instInhabitedPath_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedPath_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedPath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instToStringHost___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value:
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
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value:
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
    m_data: [115, 101, 103, 109, 101, 110, 116, 115, 0],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value:
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
    m_data: [97, 98, 115, 111, 108, 117, 116, 101, 0],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprPath_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprPath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprPath_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprPath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqPath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instBEqPath_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instBEqPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instBEqPath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__0_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__1_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__2_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__3_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__4_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__5_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__6_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__7_value:
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
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__8_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___lam__1___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instToStringPath___lam__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instToStringPath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instToStringPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instToStringPath___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_URI_instToStringPath___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_instToStringPath___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instToStringPath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 46, 0]};
static mut l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value:
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
    m_fun: l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_repr___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprTupleOfRepr___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Prod_repr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instReprQuery___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instReprQuery___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instReprQuery___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instReprQuery: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instReprQuery___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedQuery___aux__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedQuery: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_ByteArray_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instBEqQuery___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqQuery___aux__1___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instBEqQuery___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqQuery___aux__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instBEqQuery___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_instBEqQuery___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_instBEqQuery___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqQuery___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instBEqQuery: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instBEqQuery___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_formatQueryParam___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [61, 0],
};
static mut l_Std_Http_URI_Query_formatQueryParam___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_formatQueryParam___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_empty___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Http_URI_Query_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Query_empty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_get___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value
        ) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_URI_Query_get___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_get___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_toRawString___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Std_Http_URI_Query_toRawString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_toRawString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Query_instEmptyCollection: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_instSingletonProdString___closed__0_value:
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
    m_fun: l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_Query_instSingletonProdString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instSingletonProdString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Query_instSingletonProdString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instSingletonProdString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_instInsertProdString___closed__0_value:
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
    m_fun: l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_Query_instInsertProdString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instInsertProdString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Query_instInsertProdString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instInsertProdString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_instToString___lam__1___closed__0_value:
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
static mut l_Std_Http_URI_Query_instToString___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_URI_Query_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_URI_Query_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Query_instToString___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_URI_Query_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Query_instToString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Query_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__0_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 99, 104, 101, 109, 101, 0],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_instReprURI_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprURI_repr___redArg___closed__5_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 117, 116, 104, 111, 114, 105, 116, 121, 0],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_instReprURI_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprURI_repr___redArg___closed__8_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 97, 116, 104, 0],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__10_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [113, 117, 101, 114, 121, 0],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__11_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_instReprURI_repr___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprURI_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprURI_repr___redArg___closed__13_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 114, 97, 103, 109, 101, 110, 116, 0],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI_repr___redArg___closed__14_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprURI_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprURI___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprURI_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprURI___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Std_Http_instReprURI: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprURI___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Http_instInhabitedURI_default___closed__0_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_instInhabitedScheme___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instInhabitedURI_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedURI_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedURI_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedURI_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedURI: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedURI_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instBEqURI___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instBEqURI_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instBEqURI___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqURI___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Std_Http_instBEqURI: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqURI___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Http_instToStringURI___lam__2___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
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
static mut l_Std_Http_instToStringURI___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instToStringURI___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instToStringURI___lam__2___closed__1_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
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
static mut l_Std_Http_instToStringURI___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instToStringURI___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instToStringURI___closed__0_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_instToStringURI___lam__2 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instToStringURI___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instToStringURI___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instToStringURI: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instToStringURI___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_URI_instInhabitedBuilder_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value:
    leanh::LeanCtorObject<7> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instInhabitedBuilder_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedBuilder_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_instInhabitedBuilder: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_URI_Builder_empty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Builder_setScheme_x21___closed__0_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 66, 117, 105, 108, 100, 101, 114,
        46, 115, 101, 116, 83, 99, 104, 101, 109, 101, 33, 0,
    ],
};
static mut l_Std_Http_URI_Builder_setScheme_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Builder_setScheme_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Builder_setHost_x21___closed__0_value: leanh::LeanStringObject<
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 66, 117, 105, 108, 100, 101, 114,
        46, 115, 101, 116, 72, 111, 115, 116, 33, 0,
    ],
};
static mut l_Std_Http_URI_Builder_setHost_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Builder_setHost_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_Builder_setHost_x21___closed__1_value: leanh::LeanStringObject<
    22,
> = leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 109, 97, 105, 110, 32, 110, 97, 109, 101,
        58, 32, 0,
    ],
};
static mut l_Std_Http_URI_Builder_setHost_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Builder_setHost_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instInhabitedRequestTarget_default___closed__0_value:
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
        core::ptr::addr_of!(l_Std_Http_URI_instInhabitedPath_default___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instInhabitedRequestTarget_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedRequestTarget_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedRequestTarget_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedRequestTarget_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedRequestTarget: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedRequestTarget_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__0_value: leanh::LeanStringObject<
    36,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 97, 115, 116, 101, 114, 105, 115, 107, 70, 111, 114, 109, 0,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__2_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 111, 114, 105, 103, 105, 110, 70, 111, 114, 109, 0,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__4_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__3_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__5_value: leanh::LeanStringObject<
    36,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 97, 98, 115, 111, 108, 117, 116, 101, 70, 111, 114, 109, 0,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__6_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__7_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__6_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__8_value: leanh::LeanStringObject<
    37,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 97, 117, 116, 104, 111, 114, 105, 116, 121, 70, 111, 114, 109, 0,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget_repr___closed__10_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprRequestTarget_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprRequestTarget___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprRequestTarget_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprRequestTarget___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instReprRequestTarget: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprRequestTarget___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_RequestTarget_path___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Http_RequestTarget_path___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_path___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_RequestTarget_path___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_RequestTarget_path___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_RequestTarget_path___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_path___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_RequestTarget_instToString___lam__4___closed__0_value:
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
static mut l_Std_Http_RequestTarget_instToString___lam__4___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_instToString___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_RequestTarget_instToString___closed__0_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_RequestTarget_instToString___lam__4 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_RequestTarget_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_RequestTarget_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_RequestTarget_instEncodeV11___closed__0_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_RequestTarget_instEncodeV11___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_Query_instToString___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instToStringPath___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_RequestTarget_instEncodeV11___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_instEncodeV11___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_RequestTarget_instEncodeV11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_instEncodeV11___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(
    mut v_s_3546_: *mut leanh::LeanObject,
    mut v_p_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3549_: u32 = 0;
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: u32 = 0;
    let mut v___x_3557_: u32 = 0;
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: u32 = 0;
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: u32 = 0;
    let mut v___x_3562_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3554_ = lean_string_utf8_byte_size(v_s_3546_);
                v___x_3555_ = lean_nat_dec_eq(v_p_3547_, v___x_3554_);
                if v___x_3555_ == 0 {
                    v___x_3556_ = lean_string_utf8_get_fast(v_s_3546_, v_p_3547_);
                    v___x_3557_ = 65;
                    v___x_3558_ = lean_uint32_dec_le(v___x_3557_, v___x_3556_);
                    if v___x_3558_ == 0 {
                        v___y_3549_ = v___x_3556_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3559_ = 90;
                        v___x_3560_ = lean_uint32_dec_le(v___x_3556_, v___x_3559_);
                        if v___x_3560_ == 0 {
                            v___y_3549_ = v___x_3556_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3561_ = 32;
                            v___x_3562_ = lean_uint32_add(v___x_3556_, v___x_3561_);
                            v___y_3549_ = v___x_3562_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_p_3547_);
                    return v_s_3546_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_3547_);
                v___x_3550_ = lean_string_utf8_set(v_s_3546_, v_p_3547_, v___y_3549_);
                v___x_3551_ = l_Char_utf8Size(v___y_3549_);
                v___x_3552_ = lean_nat_add(v_p_3547_, v___x_3551_);
                leanh::lean_dec(v___x_3551_);
                leanh::lean_dec(v_p_3547_);
                v_s_3546_ = v___x_3550_;
                v_p_3547_ = v___x_3552_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(
    mut v_x_3563_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3564_: u8 = 0;
    let mut v_head_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: u8 = 0;
    let mut v___x_3569_: u32 = 0;
    let mut v___x_3570_: u32 = 0;
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: u32 = 0;
    let mut v___x_3573_: u32 = 0;
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: u32 = 0;
    let mut v___x_3576_: u32 = 0;
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3583_: u32 = 0;
    let mut v___x_3584_: u32 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u32 = 0;
    let mut v___x_3587_: u32 = 0;
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: u32 = 0;
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___y_3594_: u8 = 0;
    let mut v___x_3595_: u32 = 0;
    let mut v___x_3596_: u32 = 0;
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: u32 = 0;
    let mut v___x_3599_: u32 = 0;
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3602_: u32 = 0;
    let mut v___x_3603_: u32 = 0;
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: u32 = 0;
    let mut v___x_3606_: u32 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3563_) == 0 {
                    v___x_3564_ = 1;
                    return v___x_3564_;
                } else {
                    v_head_3565_ = leanh::lean_ctor_get(v_x_3563_, 0);
                    v_tail_3566_ = leanh::lean_ctor_get(v_x_3563_, 1);
                    v___x_3589_ = leanh::lean_unbox_uint32(v_head_3565_);
                    v___x_3590_ = lean_uint32_to_nat(v___x_3589_);
                    v___x_3591_ = leanh::lean_unsigned_to_nat(128);
                    v___x_3592_ = lean_nat_dec_lt(v___x_3590_, v___x_3591_);
                    leanh::lean_dec(v___x_3590_);
                    if v___x_3592_ == 0 {
                        v___y_3568_ = v___x_3592_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3602_ = 48;
                        v___x_3603_ = leanh::lean_unbox_uint32(v_head_3565_);
                        v___x_3604_ = lean_uint32_dec_le(v___x_3602_, v___x_3603_);
                        if v___x_3604_ == 0 {
                            v___y_3594_ = v___x_3604_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3605_ = 57;
                            v___x_3606_ = leanh::lean_unbox_uint32(v_head_3565_);
                            v___x_3607_ = lean_uint32_dec_le(v___x_3606_, v___x_3605_);
                            v___y_3594_ = v___x_3607_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_3568_ == 0 {
                    v___x_3569_ = 43;
                    v___x_3570_ = leanh::lean_unbox_uint32(v_head_3565_);
                    v___x_3571_ = lean_uint32_dec_eq(v___x_3570_, v___x_3569_);
                    if v___x_3571_ == 0 {
                        v___x_3572_ = 45;
                        v___x_3573_ = leanh::lean_unbox_uint32(v_head_3565_);
                        v___x_3574_ = lean_uint32_dec_eq(v___x_3573_, v___x_3572_);
                        if v___x_3574_ == 0 {
                            v___x_3575_ = 46;
                            v___x_3576_ = leanh::lean_unbox_uint32(v_head_3565_);
                            v___x_3577_ = lean_uint32_dec_eq(v___x_3576_, v___x_3575_);
                            if v___x_3577_ == 0 {
                                return v___y_3568_;
                            } else {
                                v_x_3563_ = v_tail_3566_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_3563_ = v_tail_3566_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_3563_ = v_tail_3566_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_x_3563_ = v_tail_3566_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3583_ = 97;
                v___x_3584_ = leanh::lean_unbox_uint32(v_head_3565_);
                v___x_3585_ = lean_uint32_dec_le(v___x_3583_, v___x_3584_);
                if v___x_3585_ == 0 {
                    v___y_3568_ = v___x_3585_;
                    state = 1;
                    continue;
                } else {
                    v___x_3586_ = 122;
                    v___x_3587_ = leanh::lean_unbox_uint32(v_head_3565_);
                    v___x_3588_ = lean_uint32_dec_le(v___x_3587_, v___x_3586_);
                    v___y_3568_ = v___x_3588_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_3594_ == 0 {
                    v___x_3595_ = 65;
                    v___x_3596_ = leanh::lean_unbox_uint32(v_head_3565_);
                    v___x_3597_ = lean_uint32_dec_le(v___x_3595_, v___x_3596_);
                    if v___x_3597_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_3598_ = 90;
                        v___x_3599_ = leanh::lean_unbox_uint32(v_head_3565_);
                        v___x_3600_ = lean_uint32_dec_le(v___x_3599_, v___x_3598_);
                        if v___x_3600_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_3568_ = v___x_3592_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_x_3563_ = v_tail_3566_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(
    mut v_x_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3609_: u8 = 0;
    let mut v_r_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_3608_);
    leanh::lean_dec(v_x_3608_);
    v_r_3610_ = leanh::lean_box((v_res_3609_) as usize);
    return v_r_3610_;
}
pub unsafe fn l_Std_Http_URI_Scheme_ofString_x3f(
    mut v_s_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3615_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: u8 = 0;
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u32 = 0;
    let mut v___x_3628_: u32 = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: u32 = 0;
    let mut v___x_3631_: u32 = 0;
    let mut v___x_3632_: u8 = 0;
    let mut v___x_3633_: u32 = 0;
    let mut v___x_3634_: u32 = 0;
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3636_: u32 = 0;
    let mut v___x_3637_: u32 = 0;
    let mut v___x_3638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3612_ = leanh::lean_unsigned_to_nat(0);
                v_lower_3613_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(
                    v_s_3611_,
                    v___x_3612_,
                );
                leanh::lean_inc_ref(v_lower_3613_);
                v___x_3618_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_3613_);
                if v___x_3618_ == 0 {
                    leanh::lean_dec_ref(v_lower_3613_);
                    v___x_3619_ = leanh::lean_box(0);
                    return v___x_3619_;
                } else {
                    leanh::lean_inc_ref(v_lower_3613_);
                    v___x_3620_ = lean_string_data(v_lower_3613_);
                    v___x_3621_ =
                        l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_3620_);
                    if v___x_3621_ == 0 {
                        leanh::lean_dec(v___x_3620_);
                        leanh::lean_dec_ref(v_lower_3613_);
                        v___x_3622_ = leanh::lean_box(0);
                        return v___x_3622_;
                    } else {
                        v___x_3623_ = l_List_head_x3f___redArg(v___x_3620_);
                        leanh::lean_dec(v___x_3620_);
                        if leanh::lean_obj_tag(v___x_3623_) == 0 {
                            leanh::lean_dec_ref(v_lower_3613_);
                            v___x_3624_ = leanh::lean_box(0);
                            return v___x_3624_;
                        } else {
                            v_val_3625_ = leanh::lean_ctor_get(v___x_3623_, 0);
                            leanh::lean_inc(v_val_3625_);
                            leanh::lean_dec_ref_known(v___x_3623_, 1);
                            v___x_3633_ = 65;
                            v___x_3634_ = leanh::lean_unbox_uint32(v_val_3625_);
                            v___x_3635_ = lean_uint32_dec_le(v___x_3633_, v___x_3634_);
                            if v___x_3635_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v___x_3636_ = 90;
                                v___x_3637_ = leanh::lean_unbox_uint32(v_val_3625_);
                                v___x_3638_ = lean_uint32_dec_le(v___x_3637_, v___x_3636_);
                                if v___x_3638_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_val_3625_);
                                    v_val_3615_ = v___x_3621_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_val_3615_ == 0 {
                    leanh::lean_dec_ref(v_lower_3613_);
                    v___x_3616_ = leanh::lean_box(0);
                    return v___x_3616_;
                } else {
                    v___x_3617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3617_, 0, v_lower_3613_);
                    return v___x_3617_;
                }
            }
            2 => {
                v___x_3627_ = 97;
                v___x_3628_ = leanh::lean_unbox_uint32(v_val_3625_);
                v___x_3629_ = lean_uint32_dec_le(v___x_3627_, v___x_3628_);
                if v___x_3629_ == 0 {
                    leanh::lean_dec(v_val_3625_);
                    v_val_3615_ = v___x_3629_;
                    state = 1;
                    continue;
                } else {
                    v___x_3630_ = 122;
                    v___x_3631_ = leanh::lean_unbox_uint32(v_val_3625_);
                    leanh::lean_dec(v_val_3625_);
                    v___x_3632_ = lean_uint32_dec_le(v___x_3631_, v___x_3630_);
                    v_val_3615_ = v___x_3632_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(
    mut v_msg_3639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3640_ = l_Std_Http_URI_instInhabitedScheme___closed__0;
    v___x_3641_ = lean_panic_fn_borrowed(v___x_3640_, v_msg_3639_);
    return v___x_3641_;
}
pub unsafe fn l_Std_Http_URI_Scheme_ofString_x21(
    mut v_s_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_s_3645_);
    v___x_3646_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_3645_);
    if leanh::lean_obj_tag(v___x_3646_) == 0 {
        let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3647_ = l_Std_Http_URI_Scheme_ofString_x21___closed__0;
        v___x_3648_ = l_Std_Http_URI_Scheme_ofString_x21___closed__1;
        v___x_3649_ = leanh::lean_unsigned_to_nat(84);
        v___x_3650_ = leanh::lean_unsigned_to_nat(12);
        v___x_3651_ = l_Std_Http_URI_Scheme_ofString_x21___closed__2;
        v___x_3652_ = l_String_quote(v_s_3645_);
        v___x_3653_ = lean_string_append(v___x_3651_, v___x_3652_);
        leanh::lean_dec_ref(v___x_3652_);
        v___x_3654_ = l_mkPanicMessageWithDecl(
            v___x_3647_,
            v___x_3648_,
            v___x_3649_,
            v___x_3650_,
            v___x_3653_,
        );
        leanh::lean_dec_ref(v___x_3653_);
        v___x_3655_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_3654_);
        return v___x_3655_;
    } else {
        let mut v_val_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_3645_);
        v_val_3656_ = leanh::lean_ctor_get(v___x_3646_, 0);
        leanh::lean_inc(v_val_3656_);
        leanh::lean_dec_ref_known(v___x_3646_, 1);
        return v_val_3656_;
    }
}
pub unsafe fn l_Std_Http_URI_Scheme_defaultPort(
    mut v_scheme_3658_: *mut leanh::LeanObject,
) -> u16 {
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    v___x_3659_ = l_Std_Http_URI_Scheme_defaultPort___closed__0;
    v___x_3660_ = lean_string_dec_eq(v_scheme_3658_, v___x_3659_);
    if v___x_3660_ == 0 {
        let mut v___x_3661_: u16 = 0;
        v___x_3661_ = 80;
        return v___x_3661_;
    } else {
        let mut v___x_3662_: u16 = 0;
        v___x_3662_ = 443;
        return v___x_3662_;
    }
}
pub unsafe fn l_Std_Http_URI_Scheme_defaultPort___boxed(
    mut v_scheme_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3664_: u16 = 0;
    let mut v_r_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3663_);
    leanh::lean_dec_ref(v_scheme_3663_);
    v_r_3665_ = leanh::lean_box((v_res_3664_) as usize);
    return v_r_3665_;
}
pub unsafe fn l_Std_Http_URI_Scheme_ofPort(mut v_port_3666_: u16) -> *mut leanh::LeanObject {
    let mut v___x_3667_: u16 = 0;
    let mut v___x_3668_: u8 = 0;
    v___x_3667_ = 443;
    v___x_3668_ = lean_uint16_dec_eq(v_port_3666_, v___x_3667_);
    if v___x_3668_ == 0 {
        let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3669_ = l_Std_Http_URI_instInhabitedScheme___closed__0;
        return v___x_3669_;
    } else {
        let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3670_ = l_Std_Http_URI_Scheme_defaultPort___closed__0;
        return v___x_3670_;
    }
}
pub unsafe fn l_Std_Http_URI_Scheme_ofPort___boxed(
    mut v_port_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_port_boxed_3672_: u16 = 0;
    let mut v_res_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_port_boxed_3672_ = (leanh::lean_unbox(v_port_3671_) as u16);
    v_res_3673_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_3672_);
    return v_res_3673_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0() -> u8 {
    let mut v___x_3674_: u32 = 0;
    let mut v___x_3675_: u8 = 0;
    v___x_3674_ = 58;
    v___x_3675_ = lean_uint32_to_uint8(v___x_3674_);
    return v___x_3675_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1() -> u8 {
    let mut v___x_3676_: u32 = 0;
    let mut v___x_3677_: u8 = 0;
    v___x_3676_ = 38;
    v___x_3677_ = lean_uint32_to_uint8(v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2() -> u8 {
    let mut v___x_3678_: u32 = 0;
    let mut v___x_3679_: u8 = 0;
    v___x_3678_ = 39;
    v___x_3679_ = lean_uint32_to_uint8(v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3() -> u8 {
    let mut v___x_3680_: u32 = 0;
    let mut v___x_3681_: u8 = 0;
    v___x_3680_ = 40;
    v___x_3681_ = lean_uint32_to_uint8(v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4() -> u8 {
    let mut v___x_3682_: u32 = 0;
    let mut v___x_3683_: u8 = 0;
    v___x_3682_ = 41;
    v___x_3683_ = lean_uint32_to_uint8(v___x_3682_);
    return v___x_3683_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5() -> u8 {
    let mut v___x_3684_: u32 = 0;
    let mut v___x_3685_: u8 = 0;
    v___x_3684_ = 42;
    v___x_3685_ = lean_uint32_to_uint8(v___x_3684_);
    return v___x_3685_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6() -> u8 {
    let mut v___x_3686_: u32 = 0;
    let mut v___x_3687_: u8 = 0;
    v___x_3686_ = 43;
    v___x_3687_ = lean_uint32_to_uint8(v___x_3686_);
    return v___x_3687_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7() -> u8 {
    let mut v___x_3688_: u32 = 0;
    let mut v___x_3689_: u8 = 0;
    v___x_3688_ = 44;
    v___x_3689_ = lean_uint32_to_uint8(v___x_3688_);
    return v___x_3689_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8() -> u8 {
    let mut v___x_3690_: u32 = 0;
    let mut v___x_3691_: u8 = 0;
    v___x_3690_ = 59;
    v___x_3691_ = lean_uint32_to_uint8(v___x_3690_);
    return v___x_3691_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9() -> u8 {
    let mut v___x_3692_: u32 = 0;
    let mut v___x_3693_: u8 = 0;
    v___x_3692_ = 61;
    v___x_3693_ = lean_uint32_to_uint8(v___x_3692_);
    return v___x_3693_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10() -> u8 {
    let mut v___x_3694_: u32 = 0;
    let mut v___x_3695_: u8 = 0;
    v___x_3694_ = 33;
    v___x_3695_ = lean_uint32_to_uint8(v___x_3694_);
    return v___x_3695_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11() -> u8 {
    let mut v___x_3696_: u32 = 0;
    let mut v___x_3697_: u8 = 0;
    v___x_3696_ = 36;
    v___x_3697_ = lean_uint32_to_uint8(v___x_3696_);
    return v___x_3697_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12() -> u8 {
    let mut v___x_3698_: u32 = 0;
    let mut v___x_3699_: u8 = 0;
    v___x_3698_ = 95;
    v___x_3699_ = lean_uint32_to_uint8(v___x_3698_);
    return v___x_3699_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13() -> u8 {
    let mut v___x_3700_: u32 = 0;
    let mut v___x_3701_: u8 = 0;
    v___x_3700_ = 126;
    v___x_3701_ = lean_uint32_to_uint8(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14() -> u8 {
    let mut v___x_3702_: u32 = 0;
    let mut v___x_3703_: u8 = 0;
    v___x_3702_ = 45;
    v___x_3703_ = lean_uint32_to_uint8(v___x_3702_);
    return v___x_3703_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15() -> u8 {
    let mut v___x_3704_: u32 = 0;
    let mut v___x_3705_: u8 = 0;
    v___x_3704_ = 46;
    v___x_3705_ = lean_uint32_to_uint8(v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16() -> u8 {
    let mut v___x_3706_: u32 = 0;
    let mut v___x_3707_: u8 = 0;
    v___x_3706_ = 65;
    v___x_3707_ = lean_uint32_to_uint8(v___x_3706_);
    return v___x_3707_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17() -> u8 {
    let mut v___x_3708_: u32 = 0;
    let mut v___x_3709_: u8 = 0;
    v___x_3708_ = 90;
    v___x_3709_ = lean_uint32_to_uint8(v___x_3708_);
    return v___x_3709_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18() -> u8 {
    let mut v___x_3710_: u32 = 0;
    let mut v___x_3711_: u8 = 0;
    v___x_3710_ = 97;
    v___x_3711_ = lean_uint32_to_uint8(v___x_3710_);
    return v___x_3711_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19() -> u8 {
    let mut v___x_3712_: u32 = 0;
    let mut v___x_3713_: u8 = 0;
    v___x_3712_ = 122;
    v___x_3713_ = lean_uint32_to_uint8(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20() -> u8 {
    let mut v___x_3714_: u32 = 0;
    let mut v___x_3715_: u8 = 0;
    v___x_3714_ = 48;
    v___x_3715_ = lean_uint32_to_uint8(v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21() -> u8 {
    let mut v___x_3716_: u32 = 0;
    let mut v___x_3717_: u8 = 0;
    v___x_3716_ = 57;
    v___x_3717_ = lean_uint32_to_uint8(v___x_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(mut v___y_3718_: u8) -> u8 {
    let mut v___y_3720_: u8 = 0;
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: u8 = 0;
    let mut v___y_3724_: u8 = 0;
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: u8 = 0;
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___y_3744_: u8 = 0;
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: u8 = 0;
    let mut v___y_3750_: u8 = 0;
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: u8 = 0;
    let mut v___y_3756_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___y_3762_: u8 = 0;
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: u8 = 0;
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: u8 = 0;
    let mut v___y_3768_: u8 = 0;
    let mut v___x_3769_: u8 = 0;
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: u8 = 0;
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3773_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once
                    ),
                    _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20,
                );
                v___x_3774_ = lean_uint8_dec_le(v___x_3773_, v___y_3718_);
                if v___x_3774_ == 0 {
                    v___y_3768_ = v___x_3774_;
                    state = 7;
                    continue;
                } else {
                    v___x_3775_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21,
                    );
                    v___x_3776_ = lean_uint8_dec_le(v___y_3718_, v___x_3775_);
                    v___y_3768_ = v___x_3776_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_3720_ == 0 {
                    v___x_3721_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0,
                    );
                    v___x_3722_ = lean_uint8_dec_eq(v___y_3718_, v___x_3721_);
                    return v___x_3722_;
                } else {
                    return v___y_3720_;
                }
            }
            2 => {
                if v___y_3724_ == 0 {
                    v___x_3725_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1,
                    );
                    v___x_3726_ = lean_uint8_dec_eq(v___y_3718_, v___x_3725_);
                    if v___x_3726_ == 0 {
                        v___x_3727_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2);
                        v___x_3728_ = lean_uint8_dec_eq(v___y_3718_, v___x_3727_);
                        if v___x_3728_ == 0 {
                            v___x_3729_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3);
                            v___x_3730_ = lean_uint8_dec_eq(v___y_3718_, v___x_3729_);
                            if v___x_3730_ == 0 {
                                v___x_3731_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4);
                                v___x_3732_ = lean_uint8_dec_eq(v___y_3718_, v___x_3731_);
                                if v___x_3732_ == 0 {
                                    v___x_3733_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5);
                                    v___x_3734_ = lean_uint8_dec_eq(v___y_3718_, v___x_3733_);
                                    if v___x_3734_ == 0 {
                                        v___x_3735_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6);
                                        v___x_3736_ = lean_uint8_dec_eq(v___y_3718_, v___x_3735_);
                                        if v___x_3736_ == 0 {
                                            v___x_3737_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7);
                                            v___x_3738_ =
                                                lean_uint8_dec_eq(v___y_3718_, v___x_3737_);
                                            if v___x_3738_ == 0 {
                                                v___x_3739_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8);
                                                v___x_3740_ =
                                                    lean_uint8_dec_eq(v___y_3718_, v___x_3739_);
                                                if v___x_3740_ == 0 {
                                                    v___x_3741_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9);
                                                    v___x_3742_ =
                                                        lean_uint8_dec_eq(v___y_3718_, v___x_3741_);
                                                    v___y_3720_ = v___x_3742_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_3720_ = v___x_3740_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_3720_ = v___x_3738_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_3720_ = v___x_3736_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_3720_ = v___x_3734_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_3720_ = v___x_3732_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_3720_ = v___x_3730_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_3720_ = v___x_3728_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_3720_ = v___x_3726_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_3724_;
                }
            }
            3 => {
                if v___y_3744_ == 0 {
                    v___x_3745_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10,
                    );
                    v___x_3746_ = lean_uint8_dec_eq(v___y_3718_, v___x_3745_);
                    if v___x_3746_ == 0 {
                        v___x_3747_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11);
                        v___x_3748_ = lean_uint8_dec_eq(v___y_3718_, v___x_3747_);
                        v___y_3724_ = v___x_3748_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3724_ = v___x_3746_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_3744_;
                }
            }
            4 => {
                if v___y_3750_ == 0 {
                    v___x_3751_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12,
                    );
                    v___x_3752_ = lean_uint8_dec_eq(v___y_3718_, v___x_3751_);
                    if v___x_3752_ == 0 {
                        v___x_3753_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13);
                        v___x_3754_ = lean_uint8_dec_eq(v___y_3718_, v___x_3753_);
                        v___y_3744_ = v___x_3754_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3744_ = v___x_3752_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_3750_;
                }
            }
            5 => {
                if v___y_3756_ == 0 {
                    v___x_3757_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14,
                    );
                    v___x_3758_ = lean_uint8_dec_eq(v___y_3718_, v___x_3757_);
                    if v___x_3758_ == 0 {
                        v___x_3759_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15);
                        v___x_3760_ = lean_uint8_dec_eq(v___y_3718_, v___x_3759_);
                        v___y_3750_ = v___x_3760_;
                        state = 4;
                        continue;
                    } else {
                        v___y_3750_ = v___x_3758_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_3756_;
                }
            }
            6 => {
                if v___y_3762_ == 0 {
                    v___x_3763_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16,
                    );
                    v___x_3764_ = lean_uint8_dec_le(v___x_3763_, v___y_3718_);
                    if v___x_3764_ == 0 {
                        v___y_3756_ = v___x_3764_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3765_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17);
                        v___x_3766_ = lean_uint8_dec_le(v___y_3718_, v___x_3765_);
                        v___y_3756_ = v___x_3766_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_3762_;
                }
            }
            7 => {
                if v___y_3768_ == 0 {
                    v___x_3769_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once
                        ),
                        _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18,
                    );
                    v___x_3770_ = lean_uint8_dec_le(v___x_3769_, v___y_3718_);
                    if v___x_3770_ == 0 {
                        v___y_3762_ = v___x_3770_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3771_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19), core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once), _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19);
                        v___x_3772_ = lean_uint8_dec_le(v___y_3718_, v___x_3771_);
                        v___y_3762_ = v___x_3772_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_3768_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed(
    mut v___y_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_322__boxed_3778_: u8 = 0;
    let mut v_res_3779_: u8 = 0;
    let mut v_r_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_322__boxed_3778_ = (leanh::lean_unbox(v___y_3777_) as u8);
    v_res_3779_ = l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(v___y_322__boxed_3778_);
    v_r_3780_ = leanh::lean_box((v_res_3779_) as usize);
    return v_r_3780_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3782_ = l_Std_Http_URI_instInhabitedUserInfo_default___closed__0;
    v___x_3783_ = l_Std_Http_URI_EncodedString_empty(v___f_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = leanh::lean_box(0);
    v___x_3785_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once),
        _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1,
    );
    v___x_3786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
    leanh::lean_ctor_set(v___x_3786_, 1, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo_default() -> *mut leanh::LeanObject
{
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once),
        _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2,
    );
    return v___x_3787_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedUserInfo() -> *mut leanh::LeanObject {
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3788_ = l_Std_Http_URI_instInhabitedUserInfo_default;
    return v___x_3788_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(
    mut v_x_3795_: *mut leanh::LeanObject,
    mut v_x_3796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3795_) == 0 {
                    v___x_3797_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
                    return v___x_3797_;
                } else {
                    v_val_3798_ = leanh::lean_ctor_get(v_x_3795_, 0);
                    v_isSharedCheck_3810_ = (!leanh::lean_is_exclusive(v_x_3795_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v___x_3800_ = v_x_3795_;
                        v_isShared_3801_ = v_isSharedCheck_3810_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3798_);
                        leanh::lean_dec(v_x_3795_);
                        v___x_3800_ = leanh::lean_box(0);
                        v_isShared_3801_ = v_isSharedCheck_3810_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3802_ =
                    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
                v___x_3803_ = lean_string_from_utf8_unchecked(v_val_3798_);
                v___x_3804_ = l_String_quote(v___x_3803_);
                if v_isShared_3801_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3800_, 3);
                    leanh::lean_ctor_set(v___x_3800_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3804_);
                    v___x_3806_ = v_reuseFailAlloc_3809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3807_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3807_, 0, v___x_3802_);
                leanh::lean_ctor_set(v___x_3807_, 1, v___x_3806_);
                v___x_3808_ = l_Repr_addAppParen(v___x_3807_, v_x_3796_);
                return v___x_3808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(
    mut v_x_3811_: *mut leanh::LeanObject,
    mut v_x_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ =
        l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_3811_, v_x_3812_);
    leanh::lean_dec(v_x_3812_);
    return v_res_3813_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(
    mut v_a_3814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = lean_nat_to_int(v_a_3814_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3829_ = leanh::lean_unsigned_to_nat(12);
    v___x_3830_ = lean_nat_to_int(v___x_3829_);
    return v___x_3830_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3838_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0;
    v___x_3839_ = lean_string_length(v___x_3838_);
    return v___x_3839_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3840_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once),
        _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13,
    );
    v___x_3841_ = lean_nat_to_int(v___x_3840_);
    return v___x_3841_;
}
pub unsafe fn l_Std_Http_URI_instReprUserInfo_repr___redArg(
    mut v_x_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_username_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_username_3847_ = leanh::lean_ctor_get(v_x_3846_, 0);
                v_password_3848_ = leanh::lean_ctor_get(v_x_3846_, 1);
                v_isSharedCheck_3883_ = (!leanh::lean_is_exclusive(v_x_3846_)) as u8;
                if v_isSharedCheck_3883_ == 0 {
                    v___x_3850_ = v_x_3846_;
                    v_isShared_3851_ = v_isSharedCheck_3883_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_password_3848_);
                    leanh::lean_inc(v_username_3847_);
                    leanh::lean_dec(v_x_3846_);
                    v___x_3850_ = leanh::lean_box(0);
                    v_isShared_3851_ = v_isSharedCheck_3883_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3852_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5;
                v___x_3853_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6;
                v___x_3854_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7,
                );
                v___x_3855_ = lean_string_from_utf8_unchecked(v_username_3847_);
                v___x_3856_ = l_String_quote(v___x_3855_);
                v___x_3857_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3857_, 0, v___x_3856_);
                if v_isShared_3851_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3850_, 4);
                    leanh::lean_ctor_set(v___x_3850_, 1, v___x_3857_);
                    leanh::lean_ctor_set(v___x_3850_, 0, v___x_3854_);
                    v___x_3859_ = v___x_3850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 1, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3860_ = 0;
                v___x_3861_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3861_, 0, v___x_3859_);
                leanh::lean_ctor_set_uint8(
                    v___x_3861_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3860_,
                );
                v___x_3862_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3862_, 0, v___x_3853_);
                leanh::lean_ctor_set(v___x_3862_, 1, v___x_3861_);
                v___x_3863_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9;
                v___x_3864_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3864_, 0, v___x_3862_);
                leanh::lean_ctor_set(v___x_3864_, 1, v___x_3863_);
                v___x_3865_ = leanh::lean_box(1);
                v___x_3866_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                leanh::lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                v___x_3867_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11;
                v___x_3868_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3868_, 0, v___x_3866_);
                leanh::lean_ctor_set(v___x_3868_, 1, v___x_3867_);
                v___x_3869_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3869_, 0, v___x_3868_);
                leanh::lean_ctor_set(v___x_3869_, 1, v___x_3852_);
                v___x_3870_ = leanh::lean_unsigned_to_nat(0);
                v___x_3871_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(
                    v_password_3848_,
                    v___x_3870_,
                );
                v___x_3872_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3872_, 0, v___x_3854_);
                leanh::lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                v___x_3873_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3873_, 0, v___x_3872_);
                leanh::lean_ctor_set_uint8(
                    v___x_3873_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3860_,
                );
                v___x_3874_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3874_, 0, v___x_3869_);
                leanh::lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                v___x_3875_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14,
                );
                v___x_3876_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15;
                v___x_3877_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3877_, 0, v___x_3876_);
                leanh::lean_ctor_set(v___x_3877_, 1, v___x_3874_);
                v___x_3878_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16;
                v___x_3879_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3879_, 0, v___x_3877_);
                leanh::lean_ctor_set(v___x_3879_, 1, v___x_3878_);
                v___x_3880_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3880_, 0, v___x_3875_);
                leanh::lean_ctor_set(v___x_3880_, 1, v___x_3879_);
                v___x_3881_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3881_, 0, v___x_3880_);
                leanh::lean_ctor_set_uint8(
                    v___x_3881_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3860_,
                );
                return v___x_3881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instReprUserInfo_repr(
    mut v_x_3884_: *mut leanh::LeanObject,
    mut v_prec_3885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_3884_);
    return v___x_3886_;
}
pub unsafe fn l_Std_Http_URI_instReprUserInfo_repr___boxed(
    mut v_x_3887_: *mut leanh::LeanObject,
    mut v_prec_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_3887_, v_prec_3888_);
    leanh::lean_dec(v_prec_3888_);
    return v_res_3889_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(
    mut v_x_3892_: *mut leanh::LeanObject,
    mut v_x_3893_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3892_) == 0 {
        if leanh::lean_obj_tag(v_x_3893_) == 0 {
            let mut v___x_3894_: u8 = 0;
            v___x_3894_ = 1;
            return v___x_3894_;
        } else {
            let mut v___x_3895_: u8 = 0;
            v___x_3895_ = 0;
            return v___x_3895_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_3893_) == 0 {
            let mut v___x_3896_: u8 = 0;
            v___x_3896_ = 0;
            return v___x_3896_;
        } else {
            let mut v_val_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3899_: u8 = 0;
            v_val_3897_ = leanh::lean_ctor_get(v_x_3892_, 0);
            v_val_3898_ = leanh::lean_ctor_get(v_x_3893_, 0);
            v___x_3899_ = lean_sarray_dec_eq(v_val_3897_, v_val_3898_);
            return v___x_3899_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(
    mut v_x_3900_: *mut leanh::LeanObject,
    mut v_x_3901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3902_: u8 = 0;
    let mut v_r_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(
        v_x_3900_, v_x_3901_,
    );
    leanh::lean_dec(v_x_3901_);
    leanh::lean_dec(v_x_3900_);
    v_r_3903_ = leanh::lean_box((v_res_3902_) as usize);
    return v_r_3903_;
}
pub unsafe fn l_Std_Http_URI_instBEqUserInfo_beq(
    mut v_x_3904_: *mut leanh::LeanObject,
    mut v_x_3905_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_username_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    v_username_3906_ = leanh::lean_ctor_get(v_x_3904_, 0);
    v_password_3907_ = leanh::lean_ctor_get(v_x_3904_, 1);
    v_username_3908_ = leanh::lean_ctor_get(v_x_3905_, 0);
    v_password_3909_ = leanh::lean_ctor_get(v_x_3905_, 1);
    v___x_3910_ = lean_sarray_dec_eq(v_username_3906_, v_username_3908_);
    if v___x_3910_ == 0 {
        return v___x_3910_;
    } else {
        let mut v___x_3911_: u8 = 0;
        v___x_3911_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(
            v_password_3907_,
            v_password_3909_,
        );
        return v___x_3911_;
    }
}
pub unsafe fn l_Std_Http_URI_instBEqUserInfo_beq___boxed(
    mut v_x_3912_: *mut leanh::LeanObject,
    mut v_x_3913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3914_: u8 = 0;
    let mut v_r_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3914_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_3912_, v_x_3913_);
    leanh::lean_dec_ref(v_x_3913_);
    leanh::lean_dec_ref(v_x_3912_);
    v_r_3915_ = leanh::lean_box((v_res_3914_) as usize);
    return v_r_3915_;
}
pub unsafe fn l_Std_Http_URI_UserInfo_ofStrings(
    mut v_username_3918_: *mut leanh::LeanObject,
    mut v_password_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_3918_);
                if leanh::lean_obj_tag(v_password_3919_) == 0 {
                    v___x_3921_ = leanh::lean_box(0);
                    v___x_3922_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3922_, 0, v___x_3920_);
                    leanh::lean_ctor_set(v___x_3922_, 1, v___x_3921_);
                    return v___x_3922_;
                } else {
                    v_val_3923_ = leanh::lean_ctor_get(v_password_3919_, 0);
                    v_isSharedCheck_3932_ =
                        (!leanh::lean_is_exclusive(v_password_3919_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3925_ = v_password_3919_;
                        v_isShared_3926_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3923_);
                        leanh::lean_dec(v_password_3919_);
                        v___x_3925_ = leanh::lean_box(0);
                        v_isShared_3926_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3927_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_3923_);
                leanh::lean_dec(v_val_3923_);
                if v_isShared_3926_ == 0 {
                    leanh::lean_ctor_set(v___x_3925_, 0, v___x_3927_);
                    v___x_3929_ = v___x_3925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3927_);
                    v___x_3929_ = v_reuseFailAlloc_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3930_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3930_, 0, v___x_3920_);
                leanh::lean_ctor_set(v___x_3930_, 1, v___x_3929_);
                return v___x_3930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_UserInfo_ofStrings___boxed(
    mut v_username_3933_: *mut leanh::LeanObject,
    mut v_password_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_3933_, v_password_3934_);
    leanh::lean_dec_ref(v_username_3933_);
    return v_res_3935_;
}
pub unsafe fn l_Std_Http_URI_UserInfo_username_x3f(
    mut v_ui_3936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_username_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_username_3937_ = leanh::lean_ctor_get(v_ui_3936_, 0);
    v___x_3938_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_3937_);
    return v___x_3938_;
}
pub unsafe fn l_Std_Http_URI_UserInfo_username_x3f___boxed(
    mut v_ui_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_3939_);
    leanh::lean_dec_ref(v_ui_3939_);
    return v_res_3940_;
}
pub unsafe fn l_Std_Http_URI_UserInfo_password_x3f(
    mut v_ui_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_password_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_password_3942_ = leanh::lean_ctor_get(v_ui_3941_, 1);
    if leanh::lean_obj_tag(v_password_3942_) == 0 {
        let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3943_ = leanh::lean_box(0);
        return v___x_3943_;
    } else {
        let mut v_val_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3944_ = leanh::lean_ctor_get(v_password_3942_, 0);
        v___x_3945_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_3944_);
        return v___x_3945_;
    }
}
pub unsafe fn l_Std_Http_URI_UserInfo_password_x3f___boxed(
    mut v_ui_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_3946_);
    leanh::lean_dec_ref(v_ui_3946_);
    return v_res_3947_;
}
pub unsafe fn l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(
    mut v___x_3948_: *mut leanh::LeanObject,
    mut v_x_3949_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3950_: u8 = 0;
    let mut v_head_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: u8 = 0;
    let mut v___y_3958_: u8 = 0;
    let mut v___x_3959_: u32 = 0;
    let mut v___x_3960_: u32 = 0;
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3963_: u32 = 0;
    let mut v___x_3964_: u32 = 0;
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: u32 = 0;
    let mut v___x_3967_: u32 = 0;
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: u32 = 0;
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: u8 = 0;
    let mut v___y_3974_: u8 = 0;
    let mut v___x_3975_: u32 = 0;
    let mut v___x_3976_: u32 = 0;
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: u32 = 0;
    let mut v___x_3979_: u32 = 0;
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: u32 = 0;
    let mut v___x_3982_: u32 = 0;
    let mut v___x_3983_: u8 = 0;
    let mut v___x_3984_: u32 = 0;
    let mut v___x_3985_: u32 = 0;
    let mut v___x_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3949_) == 0 {
                    v___x_3950_ = 1;
                    return v___x_3950_;
                } else {
                    v_head_3951_ = leanh::lean_ctor_get(v_x_3949_, 0);
                    v_tail_3952_ = leanh::lean_ctor_get(v_x_3949_, 1);
                    v___x_3953_ = leanh::lean_unsigned_to_nat(63);
                    v___x_3954_ = lean_nat_dec_le(v___x_3948_, v___x_3953_);
                    v___x_3969_ = leanh::lean_unbox_uint32(v_head_3951_);
                    v___x_3970_ = lean_uint32_to_nat(v___x_3969_);
                    v___x_3971_ = leanh::lean_unsigned_to_nat(128);
                    v___x_3972_ = lean_nat_dec_lt(v___x_3970_, v___x_3971_);
                    leanh::lean_dec(v___x_3970_);
                    if v___x_3972_ == 0 {
                        v___y_3958_ = v___x_3972_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3981_ = 48;
                        v___x_3982_ = leanh::lean_unbox_uint32(v_head_3951_);
                        v___x_3983_ = lean_uint32_dec_le(v___x_3981_, v___x_3982_);
                        if v___x_3983_ == 0 {
                            v___y_3974_ = v___x_3983_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3984_ = 57;
                            v___x_3985_ = leanh::lean_unbox_uint32(v_head_3951_);
                            v___x_3986_ = lean_uint32_dec_le(v___x_3985_, v___x_3984_);
                            v___y_3974_ = v___x_3986_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___x_3954_ == 0 {
                    return v___x_3954_;
                } else {
                    v_x_3949_ = v_tail_3952_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_3958_ == 0 {
                    v___x_3959_ = 45;
                    v___x_3960_ = leanh::lean_unbox_uint32(v_head_3951_);
                    v___x_3961_ = lean_uint32_dec_eq(v___x_3960_, v___x_3959_);
                    if v___x_3961_ == 0 {
                        return v___y_3958_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3963_ = 97;
                v___x_3964_ = leanh::lean_unbox_uint32(v_head_3951_);
                v___x_3965_ = lean_uint32_dec_le(v___x_3963_, v___x_3964_);
                if v___x_3965_ == 0 {
                    v___y_3958_ = v___x_3965_;
                    state = 2;
                    continue;
                } else {
                    v___x_3966_ = 122;
                    v___x_3967_ = leanh::lean_unbox_uint32(v_head_3951_);
                    v___x_3968_ = lean_uint32_dec_le(v___x_3967_, v___x_3966_);
                    v___y_3958_ = v___x_3968_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_3974_ == 0 {
                    v___x_3975_ = 65;
                    v___x_3976_ = leanh::lean_unbox_uint32(v_head_3951_);
                    v___x_3977_ = lean_uint32_dec_le(v___x_3975_, v___x_3976_);
                    if v___x_3977_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_3978_ = 90;
                        v___x_3979_ = leanh::lean_unbox_uint32(v_head_3951_);
                        v___x_3980_ = lean_uint32_dec_le(v___x_3979_, v___x_3978_);
                        if v___x_3980_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___y_3958_ = v___x_3972_;
                            state = 2;
                            continue;
                        }
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
pub unsafe fn l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(
    mut v___x_3987_: *mut leanh::LeanObject,
    mut v_x_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3989_: u8 = 0;
    let mut v_r_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3989_ =
        l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v___x_3987_, v_x_3988_);
    leanh::lean_dec(v_x_3988_);
    leanh::lean_dec(v___x_3987_);
    v_r_3990_ = leanh::lean_box((v_res_3989_) as usize);
    return v_r_3990_;
}
pub unsafe fn l_Std_Http_URI_isValidDomainLabel(
    mut v_s_3991_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3993_: u32 = 0;
    let mut v___x_3994_: u32 = 0;
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3996_: u32 = 0;
    let mut v___x_3997_: u8 = 0;
    let mut v___y_3999_: u8 = 0;
    let mut v___y_4000_: u32 = 0;
    let mut v___y_4001_: u8 = 0;
    let mut v___x_4002_: u32 = 0;
    let mut v___x_4003_: u8 = 0;
    let mut v___x_4004_: u32 = 0;
    let mut v___x_4005_: u8 = 0;
    let mut v_chars_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: u8 = 0;
    let mut v_val_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u32 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: u32 = 0;
    let mut v___x_4016_: u32 = 0;
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: u32 = 0;
    let mut v___x_4019_: u32 = 0;
    let mut v___x_4020_: u32 = 0;
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u32 = 0;
    let mut v___y_4024_: u8 = 0;
    let mut v___y_4026_: u32 = 0;
    let mut v___x_4027_: u32 = 0;
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: u32 = 0;
    let mut v___x_4030_: u8 = 0;
    let mut v___y_4032_: u8 = 0;
    let mut v___y_4033_: u32 = 0;
    let mut v___y_4034_: u8 = 0;
    let mut v___x_4035_: u32 = 0;
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: u32 = 0;
    let mut v___x_4038_: u8 = 0;
    let mut v___y_4040_: u8 = 0;
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: u8 = 0;
    let mut v_val_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u32 = 0;
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4048_: u32 = 0;
    let mut v___x_4049_: u32 = 0;
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: u32 = 0;
    let mut v___x_4052_: u32 = 0;
    let mut v___x_4053_: u32 = 0;
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: u32 = 0;
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    let mut v___x_4059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_chars_4006_ = lean_string_data(v_s_3991_);
                v___x_4056_ = l_List_lengthTR___redArg(v_chars_4006_);
                v___x_4057_ = leanh::lean_unsigned_to_nat(63);
                v___x_4058_ = lean_nat_dec_le(v___x_4056_, v___x_4057_);
                if v___x_4058_ == 0 {
                    leanh::lean_dec(v___x_4056_);
                    v___y_4040_ = v___x_4058_;
                    state = 7;
                    continue;
                } else {
                    v___x_4059_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(
                        v___x_4056_,
                        v_chars_4006_,
                    );
                    leanh::lean_dec(v___x_4056_);
                    v___y_4040_ = v___x_4059_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_3994_ = 97;
                v___x_3995_ = lean_uint32_dec_le(v___x_3994_, v___y_3993_);
                if v___x_3995_ == 0 {
                    return v___x_3995_;
                } else {
                    v___x_3996_ = 122;
                    v___x_3997_ = lean_uint32_dec_le(v___y_3993_, v___x_3996_);
                    return v___x_3997_;
                }
            }
            2 => {
                if v___y_4001_ == 0 {
                    v___x_4002_ = 65;
                    v___x_4003_ = lean_uint32_dec_le(v___x_4002_, v___y_4000_);
                    if v___x_4003_ == 0 {
                        v___y_3993_ = v___y_4000_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4004_ = 90;
                        v___x_4005_ = lean_uint32_dec_le(v___y_4000_, v___x_4004_);
                        if v___x_4005_ == 0 {
                            v___y_3993_ = v___y_4000_;
                            state = 1;
                            continue;
                        } else {
                            return v___y_3999_;
                        }
                    }
                } else {
                    return v___y_4001_;
                }
            }
            3 => {
                v___x_4008_ = l_List_getLast_x3f___redArg(v_chars_4006_);
                leanh::lean_dec(v_chars_4006_);
                if leanh::lean_obj_tag(v___x_4008_) == 0 {
                    v___x_4009_ = 0;
                    return v___x_4009_;
                } else {
                    v_val_4010_ = leanh::lean_ctor_get(v___x_4008_, 0);
                    leanh::lean_inc(v_val_4010_);
                    leanh::lean_dec_ref_known(v___x_4008_, 1);
                    v___x_4011_ = leanh::lean_unbox_uint32(v_val_4010_);
                    v___x_4012_ = lean_uint32_to_nat(v___x_4011_);
                    v___x_4013_ = leanh::lean_unsigned_to_nat(128);
                    v___x_4014_ = lean_nat_dec_lt(v___x_4012_, v___x_4013_);
                    leanh::lean_dec(v___x_4012_);
                    if v___x_4014_ == 0 {
                        leanh::lean_dec(v_val_4010_);
                        return v___x_4014_;
                    } else {
                        v___x_4015_ = 48;
                        v___x_4016_ = leanh::lean_unbox_uint32(v_val_4010_);
                        v___x_4017_ = lean_uint32_dec_le(v___x_4015_, v___x_4016_);
                        if v___x_4017_ == 0 {
                            v___x_4018_ = leanh::lean_unbox_uint32(v_val_4010_);
                            leanh::lean_dec(v_val_4010_);
                            v___y_3999_ = v___x_4014_;
                            v___y_4000_ = v___x_4018_;
                            v___y_4001_ = v___x_4017_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4019_ = 57;
                            v___x_4020_ = leanh::lean_unbox_uint32(v_val_4010_);
                            v___x_4021_ = lean_uint32_dec_le(v___x_4020_, v___x_4019_);
                            v___x_4022_ = leanh::lean_unbox_uint32(v_val_4010_);
                            leanh::lean_dec(v_val_4010_);
                            v___y_3999_ = v___x_4014_;
                            v___y_4000_ = v___x_4022_;
                            v___y_4001_ = v___x_4021_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___y_4024_ == 0 {
                    leanh::lean_dec(v_chars_4006_);
                    return v___y_4024_;
                } else {
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_4027_ = 97;
                v___x_4028_ = lean_uint32_dec_le(v___x_4027_, v___y_4026_);
                if v___x_4028_ == 0 {
                    v___y_4024_ = v___x_4028_;
                    state = 4;
                    continue;
                } else {
                    v___x_4029_ = 122;
                    v___x_4030_ = lean_uint32_dec_le(v___y_4026_, v___x_4029_);
                    v___y_4024_ = v___x_4030_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_4034_ == 0 {
                    v___x_4035_ = 65;
                    v___x_4036_ = lean_uint32_dec_le(v___x_4035_, v___y_4033_);
                    if v___x_4036_ == 0 {
                        v___y_4026_ = v___y_4033_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4037_ = 90;
                        v___x_4038_ = lean_uint32_dec_le(v___y_4033_, v___x_4037_);
                        if v___x_4038_ == 0 {
                            v___y_4026_ = v___y_4033_;
                            state = 5;
                            continue;
                        } else {
                            v___y_4024_ = v___y_4032_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v___y_4040_ == 0 {
                    leanh::lean_dec(v_chars_4006_);
                    return v___y_4040_;
                } else {
                    v___x_4041_ = l_List_head_x3f___redArg(v_chars_4006_);
                    if leanh::lean_obj_tag(v___x_4041_) == 0 {
                        leanh::lean_dec(v_chars_4006_);
                        v___x_4042_ = 0;
                        return v___x_4042_;
                    } else {
                        v_val_4043_ = leanh::lean_ctor_get(v___x_4041_, 0);
                        leanh::lean_inc(v_val_4043_);
                        leanh::lean_dec_ref_known(v___x_4041_, 1);
                        v___x_4044_ = leanh::lean_unbox_uint32(v_val_4043_);
                        v___x_4045_ = lean_uint32_to_nat(v___x_4044_);
                        v___x_4046_ = leanh::lean_unsigned_to_nat(128);
                        v___x_4047_ = lean_nat_dec_lt(v___x_4045_, v___x_4046_);
                        leanh::lean_dec(v___x_4045_);
                        if v___x_4047_ == 0 {
                            leanh::lean_dec(v_val_4043_);
                            v___y_4024_ = v___x_4047_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4048_ = 48;
                            v___x_4049_ = leanh::lean_unbox_uint32(v_val_4043_);
                            v___x_4050_ = lean_uint32_dec_le(v___x_4048_, v___x_4049_);
                            if v___x_4050_ == 0 {
                                v___x_4051_ = leanh::lean_unbox_uint32(v_val_4043_);
                                leanh::lean_dec(v_val_4043_);
                                v___y_4032_ = v___x_4047_;
                                v___y_4033_ = v___x_4051_;
                                v___y_4034_ = v___x_4050_;
                                state = 6;
                                continue;
                            } else {
                                v___x_4052_ = 57;
                                v___x_4053_ = leanh::lean_unbox_uint32(v_val_4043_);
                                v___x_4054_ = lean_uint32_dec_le(v___x_4053_, v___x_4052_);
                                v___x_4055_ = leanh::lean_unbox_uint32(v_val_4043_);
                                leanh::lean_dec(v_val_4043_);
                                v___y_4032_ = v___x_4047_;
                                v___y_4033_ = v___x_4055_;
                                v___y_4034_ = v___x_4054_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_isValidDomainLabel___boxed(
    mut v_s_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4061_: u8 = 0;
    let mut v_r_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Std_Http_URI_isValidDomainLabel(v_s_4060_);
    v_r_4062_ = leanh::lean_box((v_res_4061_) as usize);
    return v_r_4062_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(
    mut v_s_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0;
    return v___x_4066_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(
    mut v_s_4067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4068_ =
        l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(
            v_s_4067_,
        );
    leanh::lean_dec_ref(v_s_4067_);
    return v_res_4068_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(
    mut v___x_4069_: *mut leanh::LeanObject,
    mut v_lower_4070_: *mut leanh::LeanObject,
    mut v___x_4071_: *mut leanh::LeanObject,
    mut v_a_4072_: *mut leanh::LeanObject,
    mut v_b_4073_: u8,
) -> u8 {
    let mut v_currPos_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v_startInclusive_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: u32 = 0;
    let mut v___x_4086_: u32 = 0;
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4072_) == 0 {
                    v_currPos_4074_ = leanh::lean_ctor_get(v_a_4072_, 0);
                    v_searcher_4075_ = leanh::lean_ctor_get(v_a_4072_, 1);
                    v_isSharedCheck_4093_ = (!leanh::lean_is_exclusive(v_a_4072_)) as u8;
                    if v_isSharedCheck_4093_ == 0 {
                        v___x_4077_ = v_a_4072_;
                        v_isShared_4078_ = v_isSharedCheck_4093_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_4075_);
                        leanh::lean_inc(v_currPos_4074_);
                        leanh::lean_dec(v_a_4072_);
                        v___x_4077_ = leanh::lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4093_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4073_;
                }
            }
            1 => {
                v_startInclusive_4079_ = leanh::lean_ctor_get(v___x_4071_, 1);
                v_endExclusive_4080_ = leanh::lean_ctor_get(v___x_4071_, 2);
                v___x_4081_ = leanh::lean_unsigned_to_nat(0);
                v___x_4082_ = lean_nat_dec_eq(v___x_4069_, v___x_4081_);
                v___x_4083_ = lean_nat_sub(v_endExclusive_4080_, v_startInclusive_4079_);
                v___x_4084_ = lean_nat_dec_eq(v_searcher_4075_, v___x_4083_);
                leanh::lean_dec(v___x_4083_);
                if v___x_4084_ == 0 {
                    v___x_4085_ = 46;
                    v___x_4086_ = lean_string_utf8_get_fast(v_lower_4070_, v_searcher_4075_);
                    v___x_4087_ = lean_uint32_dec_eq(v___x_4086_, v___x_4085_);
                    if v___x_4087_ == 0 {
                        v___x_4088_ = lean_string_utf8_next_fast(v_lower_4070_, v_searcher_4075_);
                        leanh::lean_dec(v_searcher_4075_);
                        if v_isShared_4078_ == 0 {
                            leanh::lean_ctor_set(v___x_4077_, 1, v___x_4088_);
                            v___x_4090_ = v___x_4077_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4092_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_currPos_4074_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4088_);
                            v___x_4090_ = v_reuseFailAlloc_4092_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4077_);
                        leanh::lean_dec(v_searcher_4075_);
                        leanh::lean_dec(v_currPos_4074_);
                        return v___x_4082_;
                    }
                } else {
                    leanh::lean_del_object(v___x_4077_);
                    leanh::lean_dec(v_searcher_4075_);
                    leanh::lean_dec(v_currPos_4074_);
                    return v___x_4082_;
                }
            }
            2 => {
                v_a_4072_ = v___x_4090_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(
    mut v___x_4094_: *mut leanh::LeanObject,
    mut v_lower_4095_: *mut leanh::LeanObject,
    mut v___x_4096_: *mut leanh::LeanObject,
    mut v_a_4097_: *mut leanh::LeanObject,
    mut v_b_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4099_: u8 = 0;
    let mut v_res_4100_: u8 = 0;
    let mut v_r_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4099_ = (leanh::lean_unbox(v_b_4098_) as u8);
    v_res_4100_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_4094_, v_lower_4095_, v___x_4096_, v_a_4097_, v_b_boxed_4099_);
    leanh::lean_dec_ref(v___x_4096_);
    leanh::lean_dec_ref(v_lower_4095_);
    leanh::lean_dec(v___x_4094_);
    v_r_4101_ = leanh::lean_box((v_res_4100_) as usize);
    return v_r_4101_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(
    mut v_lower_4102_: *mut leanh::LeanObject,
    mut v___x_4103_: *mut leanh::LeanObject,
    mut v___x_4104_: *mut leanh::LeanObject,
    mut v_a_4105_: *mut leanh::LeanObject,
    mut v_b_4106_: u8,
) -> u8 {
    let mut v_currPos_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4111_: u8 = 0;
    let mut v_startInclusive_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    let mut v_it_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: u32 = 0;
    let mut v___x_4125_: u32 = 0;
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4105_) == 0 {
                    v_currPos_4107_ = leanh::lean_ctor_get(v_a_4105_, 0);
                    v_searcher_4108_ = leanh::lean_ctor_get(v_a_4105_, 1);
                    v_isSharedCheck_4142_ = (!leanh::lean_is_exclusive(v_a_4105_)) as u8;
                    if v_isSharedCheck_4142_ == 0 {
                        v___x_4110_ = v_a_4105_;
                        v_isShared_4111_ = v_isSharedCheck_4142_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_4108_);
                        leanh::lean_inc(v_currPos_4107_);
                        leanh::lean_dec(v_a_4105_);
                        v___x_4110_ = leanh::lean_box(0);
                        v_isShared_4111_ = v_isSharedCheck_4142_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4104_);
                    return v_b_4106_;
                }
            }
            1 => {
                v_startInclusive_4112_ = leanh::lean_ctor_get(v___x_4103_, 1);
                v_endExclusive_4113_ = leanh::lean_ctor_get(v___x_4103_, 2);
                v___x_4114_ = 1;
                v___x_4122_ = lean_nat_sub(v_endExclusive_4113_, v_startInclusive_4112_);
                v___x_4123_ = lean_nat_dec_eq(v_searcher_4108_, v___x_4122_);
                leanh::lean_dec(v___x_4122_);
                if v___x_4123_ == 0 {
                    v___x_4124_ = 46;
                    v___x_4125_ = lean_string_utf8_get_fast(v_lower_4102_, v_searcher_4108_);
                    v___x_4126_ = lean_uint32_dec_eq(v___x_4125_, v___x_4124_);
                    if v___x_4126_ == 0 {
                        v___x_4127_ = lean_string_utf8_next_fast(v_lower_4102_, v_searcher_4108_);
                        leanh::lean_dec(v_searcher_4108_);
                        if v_isShared_4111_ == 0 {
                            leanh::lean_ctor_set(v___x_4110_, 1, v___x_4127_);
                            v___x_4129_ = v___x_4110_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4131_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_currPos_4107_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4127_);
                            v___x_4129_ = v_reuseFailAlloc_4131_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4132_ = lean_string_utf8_next_fast(v_lower_4102_, v_searcher_4108_);
                        v___x_4133_ = lean_nat_sub(v___x_4132_, v_searcher_4108_);
                        v___x_4134_ = lean_nat_add(v_searcher_4108_, v___x_4133_);
                        leanh::lean_dec(v___x_4133_);
                        v_slice_4135_ = l_String_Slice_subslice_x21(
                            v___x_4103_,
                            v_currPos_4107_,
                            v_searcher_4108_,
                        );
                        leanh::lean_inc(v___x_4134_);
                        if v_isShared_4111_ == 0 {
                            leanh::lean_ctor_set(v___x_4110_, 1, v___x_4134_);
                            leanh::lean_ctor_set(v___x_4110_, 0, v___x_4134_);
                            v_nextIt_4137_ = v___x_4110_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4140_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4134_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4134_);
                            v_nextIt_4137_ = v_reuseFailAlloc_4140_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4110_);
                    leanh::lean_dec(v_searcher_4108_);
                    v___x_4141_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_4104_);
                    v_it_4116_ = v___x_4141_;
                    v_startInclusive_4117_ = v_currPos_4107_;
                    v_endExclusive_4118_ = v___x_4104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4119_ = lean_string_utf8_extract(
                    v_lower_4102_,
                    v_startInclusive_4117_,
                    v_endExclusive_4118_,
                );
                leanh::lean_dec(v_endExclusive_4118_);
                leanh::lean_dec(v_startInclusive_4117_);
                v___x_4120_ = l_Std_Http_URI_isValidDomainLabel(v___x_4119_);
                if v___x_4120_ == 0 {
                    leanh::lean_dec(v_it_4116_);
                    leanh::lean_dec(v___x_4104_);
                    return v___x_4120_;
                } else {
                    v_a_4105_ = v_it_4116_;
                    v_b_4106_ = v___x_4114_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v_a_4105_ = v___x_4129_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_4138_ = leanh::lean_ctor_get(v_slice_4135_, 0);
                leanh::lean_inc(v_startInclusive_4138_);
                v_endExclusive_4139_ = leanh::lean_ctor_get(v_slice_4135_, 1);
                leanh::lean_inc(v_endExclusive_4139_);
                leanh::lean_dec_ref(v_slice_4135_);
                v_it_4116_ = v_nextIt_4137_;
                v_startInclusive_4117_ = v_startInclusive_4138_;
                v_endExclusive_4118_ = v_endExclusive_4139_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(
    mut v_lower_4143_: *mut leanh::LeanObject,
    mut v___x_4144_: *mut leanh::LeanObject,
    mut v___x_4145_: *mut leanh::LeanObject,
    mut v_a_4146_: *mut leanh::LeanObject,
    mut v_b_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4148_: u8 = 0;
    let mut v_res_4149_: u8 = 0;
    let mut v_r_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4148_ = (leanh::lean_unbox(v_b_4147_) as u8);
    v_res_4149_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_4143_, v___x_4144_, v___x_4145_, v_a_4146_, v_b_boxed_4148_);
    leanh::lean_dec_ref(v___x_4144_);
    leanh::lean_dec_ref(v_lower_4143_);
    v_r_4150_ = leanh::lean_box((v_res_4149_) as usize);
    return v_r_4150_;
}
pub unsafe fn l_Std_Http_URI_DomainName_ofString_x3f(
    mut v_s_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    v___x_4152_ = leanh::lean_unsigned_to_nat(0);
    v_lower_4153_ =
        l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_4151_, v___x_4152_);
    v___x_4154_ = lean_string_utf8_byte_size(v_lower_4153_);
    v___x_4155_ = lean_nat_dec_eq(v___x_4154_, v___x_4152_);
    if v___x_4155_ == 0 {
        let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: u8 = 0;
        let mut v___x_4159_: u8 = 0;
        leanh::lean_inc_ref(v_lower_4153_);
        v___x_4156_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_4156_, 0, v_lower_4153_);
        leanh::lean_ctor_set(v___x_4156_, 1, v___x_4152_);
        leanh::lean_ctor_set(v___x_4156_, 2, v___x_4154_);
        v___x_4157_ =
            l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(
                v___x_4156_,
            );
        v___x_4158_ = 1;
        leanh::lean_inc(v___x_4157_);
        v___x_4159_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_4154_, v_lower_4153_, v___x_4156_, v___x_4157_, v___x_4158_);
        if v___x_4159_ == 0 {
            let mut v___x_4160_: u8 = 0;
            v___x_4160_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_4153_, v___x_4156_, v___x_4154_, v___x_4157_, v___x_4158_);
            leanh::lean_dec_ref_known(v___x_4156_, 3);
            if v___x_4160_ == 0 {
                let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_lower_4153_);
                v___x_4161_ = leanh::lean_box(0);
                return v___x_4161_;
            } else {
                let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4164_: u8 = 0;
                v___x_4162_ = lean_string_length(v_lower_4153_);
                v___x_4163_ = leanh::lean_unsigned_to_nat(255);
                v___x_4164_ = lean_nat_dec_le(v___x_4162_, v___x_4163_);
                if v___x_4164_ == 0 {
                    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_lower_4153_);
                    v___x_4165_ = leanh::lean_box(0);
                    return v___x_4165_;
                } else {
                    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4166_, 0, v_lower_4153_);
                    return v___x_4166_;
                }
            }
        } else {
            let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4157_);
            leanh::lean_dec_ref_known(v___x_4156_, 3);
            leanh::lean_dec_ref(v_lower_4153_);
            v___x_4167_ = leanh::lean_box(0);
            return v___x_4167_;
        }
    } else {
        let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_lower_4153_);
        v___x_4168_ = leanh::lean_box(0);
        return v___x_4168_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(
    mut v_lower_4169_: *mut leanh::LeanObject,
    mut v___x_4170_: *mut leanh::LeanObject,
    mut v___x_4171_: *mut leanh::LeanObject,
    mut v_inst_4172_: *mut leanh::LeanObject,
    mut v_R_4173_: *mut leanh::LeanObject,
    mut v_a_4174_: *mut leanh::LeanObject,
    mut v_b_4175_: u8,
    mut v_c_4176_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4177_: u8 = 0;
    v___x_4177_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_4169_, v___x_4170_, v___x_4171_, v_a_4174_, v_b_4175_);
    return v___x_4177_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(
    mut v_lower_4178_: *mut leanh::LeanObject,
    mut v___x_4179_: *mut leanh::LeanObject,
    mut v___x_4180_: *mut leanh::LeanObject,
    mut v_inst_4181_: *mut leanh::LeanObject,
    mut v_R_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_b_4184_: *mut leanh::LeanObject,
    mut v_c_4185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4186_: u8 = 0;
    let mut v_res_4187_: u8 = 0;
    let mut v_r_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4186_ = (leanh::lean_unbox(v_b_4184_) as u8);
    v_res_4187_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(
            v_lower_4178_,
            v___x_4179_,
            v___x_4180_,
            v_inst_4181_,
            v_R_4182_,
            v_a_4183_,
            v_b_boxed_4186_,
            v_c_4185_,
        );
    leanh::lean_dec_ref(v___x_4179_);
    leanh::lean_dec_ref(v_lower_4178_);
    v_r_4188_ = leanh::lean_box((v_res_4187_) as usize);
    return v_r_4188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(
    mut v___x_4189_: *mut leanh::LeanObject,
    mut v_lower_4190_: *mut leanh::LeanObject,
    mut v___x_4191_: *mut leanh::LeanObject,
    mut v___x_4192_: *mut leanh::LeanObject,
    mut v_inst_4193_: *mut leanh::LeanObject,
    mut v_R_4194_: *mut leanh::LeanObject,
    mut v_a_4195_: *mut leanh::LeanObject,
    mut v_b_4196_: u8,
    mut v_c_4197_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4198_: u8 = 0;
    v___x_4198_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_4189_, v_lower_4190_, v___x_4191_, v_a_4195_, v_b_4196_);
    return v___x_4198_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(
    mut v___x_4199_: *mut leanh::LeanObject,
    mut v_lower_4200_: *mut leanh::LeanObject,
    mut v___x_4201_: *mut leanh::LeanObject,
    mut v___x_4202_: *mut leanh::LeanObject,
    mut v_inst_4203_: *mut leanh::LeanObject,
    mut v_R_4204_: *mut leanh::LeanObject,
    mut v_a_4205_: *mut leanh::LeanObject,
    mut v_b_4206_: *mut leanh::LeanObject,
    mut v_c_4207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4208_: u8 = 0;
    let mut v_res_4209_: u8 = 0;
    let mut v_r_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4208_ = (leanh::lean_unbox(v_b_4206_) as u8);
    v_res_4209_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(
            v___x_4199_,
            v_lower_4200_,
            v___x_4201_,
            v___x_4202_,
            v_inst_4203_,
            v_R_4204_,
            v_a_4205_,
            v_b_boxed_4208_,
            v_c_4207_,
        );
    leanh::lean_dec(v___x_4202_);
    leanh::lean_dec_ref(v___x_4201_);
    leanh::lean_dec_ref(v_lower_4200_);
    leanh::lean_dec(v___x_4199_);
    v_r_4210_ = leanh::lean_box((v_res_4209_) as usize);
    return v_r_4210_;
}
pub unsafe fn l_Std_Http_URI_Host_ctorIdx(
    mut v_x_4211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4211_) {
        0 => {
            let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4212_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4212_;
        }
        1 => {
            let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4213_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4213_;
        }
        _ => {
            let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4214_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4214_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_Host_ctorIdx___boxed(
    mut v_x_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4216_ = l_Std_Http_URI_Host_ctorIdx(v_x_4215_);
    leanh::lean_dec_ref(v_x_4215_);
    return v_res_4216_;
}
pub unsafe fn l_Std_Http_URI_Host_ctorElim___redArg(
    mut v_t_4217_: *mut leanh::LeanObject,
    mut v_k_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4219_ = leanh::lean_ctor_get(v_t_4217_, 0);
    leanh::lean_inc_ref(v_name_4219_);
    leanh::lean_dec_ref(v_t_4217_);
    v___x_4220_ = leanh::lean_apply_1(v_k_4218_, v_name_4219_);
    return v___x_4220_;
}
pub unsafe fn l_Std_Http_URI_Host_ctorElim(
    mut v_motive_4221_: *mut leanh::LeanObject,
    mut v_ctorIdx_4222_: *mut leanh::LeanObject,
    mut v_t_4223_: *mut leanh::LeanObject,
    mut v_h_4224_: *mut leanh::LeanObject,
    mut v_k_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4226_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4223_, v_k_4225_);
    return v___x_4226_;
}
pub unsafe fn l_Std_Http_URI_Host_ctorElim___boxed(
    mut v_motive_4227_: *mut leanh::LeanObject,
    mut v_ctorIdx_4228_: *mut leanh::LeanObject,
    mut v_t_4229_: *mut leanh::LeanObject,
    mut v_h_4230_: *mut leanh::LeanObject,
    mut v_k_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4232_ = l_Std_Http_URI_Host_ctorElim(
        v_motive_4227_,
        v_ctorIdx_4228_,
        v_t_4229_,
        v_h_4230_,
        v_k_4231_,
    );
    leanh::lean_dec(v_ctorIdx_4228_);
    return v_res_4232_;
}
pub unsafe fn l_Std_Http_URI_Host_name_elim___redArg(
    mut v_t_4233_: *mut leanh::LeanObject,
    mut v_name_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4233_, v_name_4234_);
    return v___x_4235_;
}
pub unsafe fn l_Std_Http_URI_Host_name_elim(
    mut v_motive_4236_: *mut leanh::LeanObject,
    mut v_t_4237_: *mut leanh::LeanObject,
    mut v_h_4238_: *mut leanh::LeanObject,
    mut v_name_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4240_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4237_, v_name_4239_);
    return v___x_4240_;
}
pub unsafe fn l_Std_Http_URI_Host_ipv4_elim___redArg(
    mut v_t_4241_: *mut leanh::LeanObject,
    mut v_ipv4_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4243_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4241_, v_ipv4_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Std_Http_URI_Host_ipv4_elim(
    mut v_motive_4244_: *mut leanh::LeanObject,
    mut v_t_4245_: *mut leanh::LeanObject,
    mut v_h_4246_: *mut leanh::LeanObject,
    mut v_ipv4_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4248_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4245_, v_ipv4_4247_);
    return v___x_4248_;
}
pub unsafe fn l_Std_Http_URI_Host_ipv6_elim___redArg(
    mut v_t_4249_: *mut leanh::LeanObject,
    mut v_ipv6_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4249_, v_ipv6_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Std_Http_URI_Host_ipv6_elim(
    mut v_motive_4252_: *mut leanh::LeanObject,
    mut v_t_4253_: *mut leanh::LeanObject,
    mut v_h_4254_: *mut leanh::LeanObject,
    mut v_ipv6_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_4253_, v_ipv6_4255_);
    return v___x_4256_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedHost_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Std_Net_instInhabitedIPv4Addr_default;
    v___x_4258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4258_, 0, v___x_4257_);
    return v___x_4258_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedHost_default() -> *mut leanh::LeanObject {
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4259_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedHost_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedHost_default___closed__0_once),
        _init_l_Std_Http_URI_instInhabitedHost_default___closed__0,
    );
    return v___x_4259_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedHost() -> *mut leanh::LeanObject {
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = l_Std_Http_URI_instInhabitedHost_default;
    return v___x_4260_;
}
pub unsafe fn l_Std_Http_URI_instBEqHost_beq(
    mut v_x_4261_: *mut leanh::LeanObject,
    mut v_x_4262_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_4261_) {
        0 => {
            if leanh::lean_obj_tag(v_x_4262_) == 0 {
                let mut v_name_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_name_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4265_: u8 = 0;
                v_name_4263_ = leanh::lean_ctor_get(v_x_4261_, 0);
                v_name_4264_ = leanh::lean_ctor_get(v_x_4262_, 0);
                v___x_4265_ = lean_string_dec_eq(v_name_4263_, v_name_4264_);
                return v___x_4265_;
            } else {
                let mut v___x_4266_: u8 = 0;
                v___x_4266_ = 0;
                return v___x_4266_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_4262_) == 1 {
                let mut v_ipv4_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ipv4_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4269_: u8 = 0;
                v_ipv4_4267_ = leanh::lean_ctor_get(v_x_4261_, 0);
                v_ipv4_4268_ = leanh::lean_ctor_get(v_x_4262_, 0);
                v___x_4269_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_4267_, v_ipv4_4268_);
                return v___x_4269_;
            } else {
                let mut v___x_4270_: u8 = 0;
                v___x_4270_ = 0;
                return v___x_4270_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_4262_) == 2 {
                let mut v_ipv6_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ipv6_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4273_: u8 = 0;
                v_ipv6_4271_ = leanh::lean_ctor_get(v_x_4261_, 0);
                v_ipv6_4272_ = leanh::lean_ctor_get(v_x_4262_, 0);
                v___x_4273_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_4271_, v_ipv6_4272_);
                return v___x_4273_;
            } else {
                let mut v___x_4274_: u8 = 0;
                v___x_4274_ = 0;
                return v___x_4274_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_instBEqHost_beq___boxed(
    mut v_x_4275_: *mut leanh::LeanObject,
    mut v_x_4276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4277_: u8 = 0;
    let mut v_r_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Std_Http_URI_instBEqHost_beq(v_x_4275_, v_x_4276_);
    leanh::lean_dec_ref(v_x_4276_);
    leanh::lean_dec_ref(v_x_4275_);
    v_r_4278_ = leanh::lean_box((v_res_4277_) as usize);
    return v_r_4278_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprHost___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = leanh::lean_unsigned_to_nat(2);
    v___x_4286_ = lean_nat_to_int(v___x_4285_);
    return v___x_4286_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprHost___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4287_ = leanh::lean_unsigned_to_nat(1);
    v___x_4288_ = lean_nat_to_int(v___x_4287_);
    return v___x_4288_;
}
pub unsafe fn l_Std_Http_URI_instReprHost___lam__0(
    mut v_x_4289_: *mut leanh::LeanObject,
    mut v_prec_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctr_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4316_: u8 = 0;
    let mut v_ipv4_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v_ipv6_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4337_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4338_ = lean_nat_dec_le(v___x_4337_, v_prec_4290_);
                if v___x_4338_ == 0 {
                    v___x_4339_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                        ),
                        _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                    );
                    v___y_4306_ = v___x_4339_;
                    state = 2;
                    continue;
                } else {
                    v___x_4340_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                        ),
                        _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                    );
                    v___y_4306_ = v___x_4340_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4295_ = l_Std_Http_URI_instReprHost___lam__0___closed__0;
                v___x_4296_ = lean_string_append(v___x_4295_, v_ctr_4293_);
                v___x_4297_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4297_, 0, v___x_4296_);
                v___x_4298_ = leanh::lean_box(1);
                v___x_4299_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4299_, 0, v___x_4297_);
                leanh::lean_ctor_set(v___x_4299_, 1, v___x_4298_);
                v___x_4300_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
                leanh::lean_ctor_set(v___x_4300_, 1, v_a_4294_);
                leanh::lean_inc(v___y_4292_);
                v___x_4301_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4301_, 0, v___y_4292_);
                leanh::lean_ctor_set(v___x_4301_, 1, v___x_4300_);
                v___x_4302_ = 0;
                v___x_4303_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4303_, 0, v___x_4301_);
                leanh::lean_ctor_set_uint8(
                    v___x_4303_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4302_,
                );
                v___x_4304_ = l_Repr_addAppParen(v___x_4303_, v_prec_4290_);
                return v___x_4304_;
            }
            2 => match leanh::lean_obj_tag(v_x_4289_) {
                0 => {
                    v_name_4307_ = leanh::lean_ctor_get(v_x_4289_, 0);
                    v_isSharedCheck_4316_ = (!leanh::lean_is_exclusive(v_x_4289_)) as u8;
                    if v_isSharedCheck_4316_ == 0 {
                        v___x_4309_ = v_x_4289_;
                        v_isShared_4310_ = v_isSharedCheck_4316_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_4307_);
                        leanh::lean_dec(v_x_4289_);
                        v___x_4309_ = leanh::lean_box(0);
                        v_isShared_4310_ = v_isSharedCheck_4316_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_ipv4_4317_ = leanh::lean_ctor_get(v_x_4289_, 0);
                    v_isSharedCheck_4326_ = (!leanh::lean_is_exclusive(v_x_4289_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4319_ = v_x_4289_;
                        v_isShared_4320_ = v_isSharedCheck_4326_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_ipv4_4317_);
                        leanh::lean_dec(v_x_4289_);
                        v___x_4319_ = leanh::lean_box(0);
                        v_isShared_4320_ = v_isSharedCheck_4326_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_ipv6_4327_ = leanh::lean_ctor_get(v_x_4289_, 0);
                    v_isSharedCheck_4336_ = (!leanh::lean_is_exclusive(v_x_4289_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4329_ = v_x_4289_;
                        v_isShared_4330_ = v_isSharedCheck_4336_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_ipv6_4327_);
                        leanh::lean_dec(v_x_4289_);
                        v___x_4329_ = leanh::lean_box(0);
                        v_isShared_4330_ = v_isSharedCheck_4336_;
                        state = 7;
                        continue;
                    }
                }
            },
            3 => {
                v___x_4311_ = l_Std_Http_URI_instReprHost___lam__0___closed__1;
                v___x_4312_ = l_String_quote(v_name_4307_);
                if v_isShared_4310_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4309_, 3);
                    leanh::lean_ctor_set(v___x_4309_, 0, v___x_4312_);
                    v___x_4314_ = v___x_4309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4315_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
                    v___x_4314_ = v_reuseFailAlloc_4315_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_4292_ = v___y_4306_;
                v_ctr_4293_ = v___x_4311_;
                v_a_4294_ = v___x_4314_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4321_ = l_Std_Http_URI_instReprHost___lam__0___closed__2;
                v___x_4322_ = lean_uv_ntop_v4(v_ipv4_4317_);
                leanh::lean_dec_ref(v_ipv4_4317_);
                if v_isShared_4320_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4319_, 3);
                    leanh::lean_ctor_set(v___x_4319_, 0, v___x_4322_);
                    v___x_4324_ = v___x_4319_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4322_);
                    v___x_4324_ = v_reuseFailAlloc_4325_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_4292_ = v___y_4306_;
                v_ctr_4293_ = v___x_4321_;
                v_a_4294_ = v___x_4324_;
                state = 1;
                continue;
            }
            7 => {
                v___x_4331_ = l_Std_Http_URI_instReprHost___lam__0___closed__3;
                v___x_4332_ = lean_uv_ntop_v6(v_ipv6_4327_);
                leanh::lean_dec_ref(v_ipv6_4327_);
                if v_isShared_4330_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4329_, 3);
                    leanh::lean_ctor_set(v___x_4329_, 0, v___x_4332_);
                    v___x_4334_ = v___x_4329_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
                    v___x_4334_ = v_reuseFailAlloc_4335_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_4292_ = v___y_4306_;
                v_ctr_4293_ = v___x_4331_;
                v_a_4294_ = v___x_4334_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instReprHost___lam__0___boxed(
    mut v_x_4341_: *mut leanh::LeanObject,
    mut v_prec_4342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Std_Http_URI_instReprHost___lam__0(v_x_4341_, v_prec_4342_);
    leanh::lean_dec(v_prec_4342_);
    return v_res_4343_;
}
pub unsafe fn l_Std_Http_URI_instToStringHost___lam__0(
    mut v_x_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4348_) {
        0 => {
            let mut v_name_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_name_4349_ = leanh::lean_ctor_get(v_x_4348_, 0);
            leanh::lean_inc_ref(v_name_4349_);
            return v_name_4349_;
        }
        1 => {
            let mut v_ipv4_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ipv4_4350_ = leanh::lean_ctor_get(v_x_4348_, 0);
            v___x_4351_ = lean_uv_ntop_v4(v_ipv4_4350_);
            return v___x_4351_;
        }
        _ => {
            let mut v_ipv6_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ipv6_4352_ = leanh::lean_ctor_get(v_x_4348_, 0);
            v___x_4353_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
            v___x_4354_ = lean_uv_ntop_v6(v_ipv6_4352_);
            v___x_4355_ = lean_string_append(v___x_4353_, v___x_4354_);
            leanh::lean_dec_ref(v___x_4354_);
            v___x_4356_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
            v___x_4357_ = lean_string_append(v___x_4355_, v___x_4356_);
            return v___x_4357_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_instToStringHost___lam__0___boxed(
    mut v_x_4358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4359_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_4358_);
    leanh::lean_dec_ref(v_x_4358_);
    return v_res_4359_;
}
pub unsafe fn l_Std_Http_URI_Port_ctorIdx(
    mut v_x_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4362_) {
        0 => {
            let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4363_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4363_;
        }
        1 => {
            let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4364_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4364_;
        }
        _ => {
            let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4365_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4365_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_Port_ctorIdx___boxed(
    mut v_x_4366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4367_ = l_Std_Http_URI_Port_ctorIdx(v_x_4366_);
    leanh::lean_dec(v_x_4366_);
    return v_res_4367_;
}
pub unsafe fn l_Std_Http_URI_Port_ctorElim___redArg(
    mut v_t_4368_: *mut leanh::LeanObject,
    mut v_k_4369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_4368_) == 2 {
        let mut v_port_4370_: u16 = 0;
        let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_port_4370_ = leanh::lean_ctor_get_uint16(v_t_4368_, 0 as u32);
        v___x_4371_ = leanh::lean_box((v_port_4370_) as usize);
        v___x_4372_ = leanh::lean_apply_1(v_k_4369_, v___x_4371_);
        return v___x_4372_;
    } else {
        return v_k_4369_;
    }
}
pub unsafe fn l_Std_Http_URI_Port_ctorElim___redArg___boxed(
    mut v_t_4373_: *mut leanh::LeanObject,
    mut v_k_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4373_, v_k_4374_);
    leanh::lean_dec(v_t_4373_);
    return v_res_4375_;
}
pub unsafe fn l_Std_Http_URI_Port_ctorElim(
    mut v_motive_4376_: *mut leanh::LeanObject,
    mut v_ctorIdx_4377_: *mut leanh::LeanObject,
    mut v_t_4378_: *mut leanh::LeanObject,
    mut v_h_4379_: *mut leanh::LeanObject,
    mut v_k_4380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4378_, v_k_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Std_Http_URI_Port_ctorElim___boxed(
    mut v_motive_4382_: *mut leanh::LeanObject,
    mut v_ctorIdx_4383_: *mut leanh::LeanObject,
    mut v_t_4384_: *mut leanh::LeanObject,
    mut v_h_4385_: *mut leanh::LeanObject,
    mut v_k_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Std_Http_URI_Port_ctorElim(
        v_motive_4382_,
        v_ctorIdx_4383_,
        v_t_4384_,
        v_h_4385_,
        v_k_4386_,
    );
    leanh::lean_dec(v_t_4384_);
    leanh::lean_dec(v_ctorIdx_4383_);
    return v_res_4387_;
}
pub unsafe fn l_Std_Http_URI_Port_omitted_elim___redArg(
    mut v_t_4388_: *mut leanh::LeanObject,
    mut v_omitted_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4388_, v_omitted_4389_);
    return v___x_4390_;
}
pub unsafe fn l_Std_Http_URI_Port_omitted_elim___redArg___boxed(
    mut v_t_4391_: *mut leanh::LeanObject,
    mut v_omitted_4392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4393_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_4391_, v_omitted_4392_);
    leanh::lean_dec(v_t_4391_);
    return v_res_4393_;
}
pub unsafe fn l_Std_Http_URI_Port_omitted_elim(
    mut v_motive_4394_: *mut leanh::LeanObject,
    mut v_t_4395_: *mut leanh::LeanObject,
    mut v_h_4396_: *mut leanh::LeanObject,
    mut v_omitted_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4395_, v_omitted_4397_);
    return v___x_4398_;
}
pub unsafe fn l_Std_Http_URI_Port_omitted_elim___boxed(
    mut v_motive_4399_: *mut leanh::LeanObject,
    mut v_t_4400_: *mut leanh::LeanObject,
    mut v_h_4401_: *mut leanh::LeanObject,
    mut v_omitted_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4403_ =
        l_Std_Http_URI_Port_omitted_elim(v_motive_4399_, v_t_4400_, v_h_4401_, v_omitted_4402_);
    leanh::lean_dec(v_t_4400_);
    return v_res_4403_;
}
pub unsafe fn l_Std_Http_URI_Port_empty_elim___redArg(
    mut v_t_4404_: *mut leanh::LeanObject,
    mut v_empty_4405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4404_, v_empty_4405_);
    return v___x_4406_;
}
pub unsafe fn l_Std_Http_URI_Port_empty_elim___redArg___boxed(
    mut v_t_4407_: *mut leanh::LeanObject,
    mut v_empty_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_4407_, v_empty_4408_);
    leanh::lean_dec(v_t_4407_);
    return v_res_4409_;
}
pub unsafe fn l_Std_Http_URI_Port_empty_elim(
    mut v_motive_4410_: *mut leanh::LeanObject,
    mut v_t_4411_: *mut leanh::LeanObject,
    mut v_h_4412_: *mut leanh::LeanObject,
    mut v_empty_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4411_, v_empty_4413_);
    return v___x_4414_;
}
pub unsafe fn l_Std_Http_URI_Port_empty_elim___boxed(
    mut v_motive_4415_: *mut leanh::LeanObject,
    mut v_t_4416_: *mut leanh::LeanObject,
    mut v_h_4417_: *mut leanh::LeanObject,
    mut v_empty_4418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4419_ =
        l_Std_Http_URI_Port_empty_elim(v_motive_4415_, v_t_4416_, v_h_4417_, v_empty_4418_);
    leanh::lean_dec(v_t_4416_);
    return v_res_4419_;
}
pub unsafe fn l_Std_Http_URI_Port_value_elim___redArg(
    mut v_t_4420_: *mut leanh::LeanObject,
    mut v_value_4421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4422_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4420_, v_value_4421_);
    return v___x_4422_;
}
pub unsafe fn l_Std_Http_URI_Port_value_elim___redArg___boxed(
    mut v_t_4423_: *mut leanh::LeanObject,
    mut v_value_4424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4425_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_4423_, v_value_4424_);
    leanh::lean_dec(v_t_4423_);
    return v_res_4425_;
}
pub unsafe fn l_Std_Http_URI_Port_value_elim(
    mut v_motive_4426_: *mut leanh::LeanObject,
    mut v_t_4427_: *mut leanh::LeanObject,
    mut v_h_4428_: *mut leanh::LeanObject,
    mut v_value_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_4427_, v_value_4429_);
    return v___x_4430_;
}
pub unsafe fn l_Std_Http_URI_Port_value_elim___boxed(
    mut v_motive_4431_: *mut leanh::LeanObject,
    mut v_t_4432_: *mut leanh::LeanObject,
    mut v_h_4433_: *mut leanh::LeanObject,
    mut v_value_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ =
        l_Std_Http_URI_Port_value_elim(v_motive_4431_, v_t_4432_, v_h_4433_, v_value_4434_);
    leanh::lean_dec(v_t_4432_);
    return v_res_4435_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedPort_default() -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = leanh::lean_box(0);
    return v___x_4436_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedPort() -> *mut leanh::LeanObject {
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = leanh::lean_box(0);
    return v___x_4437_;
}
pub unsafe fn l_Std_Http_URI_instReprPort_repr(
    mut v_x_4450_: *mut leanh::LeanObject,
    mut v_prec_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4474_: u16 = 0;
    let mut v___y_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4450_) {
                0 => {
                    v___x_4466_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4467_ = lean_nat_dec_le(v___x_4466_, v_prec_4451_);
                    if v___x_4467_ == 0 {
                        v___x_4468_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_4460_ = v___x_4468_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4469_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_4460_ = v___x_4469_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v___x_4470_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4471_ = lean_nat_dec_le(v___x_4470_, v_prec_4451_);
                    if v___x_4471_ == 0 {
                        v___x_4472_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_4453_ = v___x_4472_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4473_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_4453_ = v___x_4473_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_port_4474_ = leanh::lean_ctor_get_uint16(v_x_4450_, 0 as u32);
                    v___x_4486_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4487_ = lean_nat_dec_le(v___x_4486_, v_prec_4451_);
                    if v___x_4487_ == 0 {
                        v___x_4488_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_4476_ = v___x_4488_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4489_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_4476_ = v___x_4489_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4454_ = l_Std_Http_URI_instReprPort_repr___closed__1;
                leanh::lean_inc(v___y_4453_);
                v___x_4455_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4455_, 0, v___y_4453_);
                leanh::lean_ctor_set(v___x_4455_, 1, v___x_4454_);
                v___x_4456_ = 0;
                v___x_4457_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4457_, 0, v___x_4455_);
                leanh::lean_ctor_set_uint8(
                    v___x_4457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4456_,
                );
                v___x_4458_ = l_Repr_addAppParen(v___x_4457_, v_prec_4451_);
                return v___x_4458_;
            }
            2 => {
                v___x_4461_ = l_Std_Http_URI_instReprPort_repr___closed__3;
                leanh::lean_inc(v___y_4460_);
                v___x_4462_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4462_, 0, v___y_4460_);
                leanh::lean_ctor_set(v___x_4462_, 1, v___x_4461_);
                v___x_4463_ = 0;
                v___x_4464_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4464_, 0, v___x_4462_);
                leanh::lean_ctor_set_uint8(
                    v___x_4464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4463_,
                );
                v___x_4465_ = l_Repr_addAppParen(v___x_4464_, v_prec_4451_);
                return v___x_4465_;
            }
            3 => {
                v___x_4477_ = l_Std_Http_URI_instReprPort_repr___closed__6;
                v___x_4478_ = lean_uint16_to_nat(v_port_4474_);
                v___x_4479_ = l_Nat_reprFast(v___x_4478_);
                v___x_4480_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4480_, 0, v___x_4479_);
                v___x_4481_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4481_, 0, v___x_4477_);
                leanh::lean_ctor_set(v___x_4481_, 1, v___x_4480_);
                leanh::lean_inc(v___y_4476_);
                v___x_4482_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4482_, 0, v___y_4476_);
                leanh::lean_ctor_set(v___x_4482_, 1, v___x_4481_);
                v___x_4483_ = 0;
                v___x_4484_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4484_, 0, v___x_4482_);
                leanh::lean_ctor_set_uint8(
                    v___x_4484_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4483_,
                );
                v___x_4485_ = l_Repr_addAppParen(v___x_4484_, v_prec_4451_);
                return v___x_4485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instReprPort_repr___boxed(
    mut v_x_4490_: *mut leanh::LeanObject,
    mut v_prec_4491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Std_Http_URI_instReprPort_repr(v_x_4490_, v_prec_4491_);
    leanh::lean_dec(v_prec_4491_);
    leanh::lean_dec(v_x_4490_);
    return v_res_4492_;
}
pub unsafe fn l_Std_Http_URI_instDecidableEqPort_decEq(
    mut v_x_4495_: *mut leanh::LeanObject,
    mut v_x_4496_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_4495_) {
        0 => {
            if leanh::lean_obj_tag(v_x_4496_) == 0 {
                let mut v___x_4497_: u8 = 0;
                v___x_4497_ = 1;
                return v___x_4497_;
            } else {
                let mut v___x_4498_: u8 = 0;
                v___x_4498_ = 0;
                return v___x_4498_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_4496_) == 1 {
                let mut v___x_4499_: u8 = 0;
                v___x_4499_ = 1;
                return v___x_4499_;
            } else {
                let mut v___x_4500_: u8 = 0;
                v___x_4500_ = 0;
                return v___x_4500_;
            }
        }
        _ => {
            let mut v_port_4501_: u16 = 0;
            let mut v___x_4502_: u8 = 0;
            v_port_4501_ = leanh::lean_ctor_get_uint16(v_x_4495_, 0 as u32);
            v___x_4502_ = 0;
            if leanh::lean_obj_tag(v_x_4496_) == 2 {
                let mut v_port_4503_: u16 = 0;
                let mut v___x_4504_: u8 = 0;
                v_port_4503_ = leanh::lean_ctor_get_uint16(v_x_4496_, 0 as u32);
                v___x_4504_ = lean_uint16_dec_eq(v_port_4501_, v_port_4503_);
                if v___x_4504_ == 0 {
                    return v___x_4502_;
                } else {
                    return v___x_4504_;
                }
            } else {
                return v___x_4502_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_instDecidableEqPort_decEq___boxed(
    mut v_x_4505_: *mut leanh::LeanObject,
    mut v_x_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4507_: u8 = 0;
    let mut v_r_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4507_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_4505_, v_x_4506_);
    leanh::lean_dec(v_x_4506_);
    leanh::lean_dec(v_x_4505_);
    v_r_4508_ = leanh::lean_box((v_res_4507_) as usize);
    return v_r_4508_;
}
pub unsafe fn l_Std_Http_URI_instDecidableEqPort(
    mut v_x_4509_: *mut leanh::LeanObject,
    mut v_x_4510_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4511_: u8 = 0;
    v___x_4511_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_4509_, v_x_4510_);
    return v___x_4511_;
}
pub unsafe fn l_Std_Http_URI_instDecidableEqPort___boxed(
    mut v_x_4512_: *mut leanh::LeanObject,
    mut v_x_4513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4514_: u8 = 0;
    let mut v_r_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_Std_Http_URI_instDecidableEqPort(v_x_4512_, v_x_4513_);
    leanh::lean_dec(v_x_4513_);
    leanh::lean_dec(v_x_4512_);
    v_r_4515_ = leanh::lean_box((v_res_4514_) as usize);
    return v_r_4515_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = leanh::lean_box(0);
    v___x_4517_ = l_Std_Http_URI_instInhabitedHost_default;
    v___x_4518_ = leanh::lean_box(0);
    v___x_4519_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4519_, 0, v___x_4518_);
    leanh::lean_ctor_set(v___x_4519_, 1, v___x_4517_);
    leanh::lean_ctor_set(v___x_4519_, 2, v___x_4516_);
    return v___x_4519_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedAuthority_default() -> *mut leanh::LeanObject
{
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4520_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedAuthority_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once),
        _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0,
    );
    return v___x_4520_;
}
pub unsafe fn _init_l_Std_Http_URI_instInhabitedAuthority() -> *mut leanh::LeanObject {
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_Std_Http_URI_instInhabitedAuthority_default;
    return v___x_4521_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(
    mut v_x_4522_: *mut leanh::LeanObject,
    mut v_x_4523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4522_) == 0 {
        let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4524_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
        return v___x_4524_;
    } else {
        let mut v_val_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4525_ = leanh::lean_ctor_get(v_x_4522_, 0);
        leanh::lean_inc(v_val_4525_);
        leanh::lean_dec_ref_known(v_x_4522_, 1);
        v___x_4526_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
        v___x_4527_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_4525_);
        v___x_4528_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4528_, 0, v___x_4526_);
        leanh::lean_ctor_set(v___x_4528_, 1, v___x_4527_);
        v___x_4529_ = l_Repr_addAppParen(v___x_4528_, v_x_4523_);
        return v___x_4529_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(
    mut v_x_4530_: *mut leanh::LeanObject,
    mut v_x_4531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4532_ =
        l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_4530_, v_x_4531_);
    leanh::lean_dec(v_x_4531_);
    return v_res_4532_;
}
pub unsafe fn _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = leanh::lean_unsigned_to_nat(8);
    v___x_4546_ = lean_nat_to_int(v___x_4545_);
    return v___x_4546_;
}
pub unsafe fn l_Std_Http_URI_instReprAuthority_repr___redArg(
    mut v_x_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_userInfo_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctr_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4611_: u8 = 0;
    let mut v_ipv4_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4615_: u8 = 0;
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_ipv6_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userInfo_4551_ = leanh::lean_ctor_get(v_x_4550_, 0);
                leanh::lean_inc(v_userInfo_4551_);
                v_host_4552_ = leanh::lean_ctor_get(v_x_4550_, 1);
                leanh::lean_inc_ref(v_host_4552_);
                v_port_4553_ = leanh::lean_ctor_get(v_x_4550_, 2);
                leanh::lean_inc(v_port_4553_);
                leanh::lean_dec_ref(v_x_4550_);
                v___x_4554_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5;
                v___x_4555_ = l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3;
                v___x_4556_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7,
                );
                v___x_4557_ = leanh::lean_unsigned_to_nat(0);
                v___x_4558_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(
                    v_userInfo_4551_,
                    v___x_4557_,
                );
                v___x_4559_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4559_, 0, v___x_4556_);
                leanh::lean_ctor_set(v___x_4559_, 1, v___x_4558_);
                v___x_4560_ = 0;
                v___x_4561_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4561_, 0, v___x_4559_);
                leanh::lean_ctor_set_uint8(
                    v___x_4561_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4560_,
                );
                v___x_4562_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4562_, 0, v___x_4555_);
                leanh::lean_ctor_set(v___x_4562_, 1, v___x_4561_);
                v___x_4563_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9;
                v___x_4564_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4564_, 0, v___x_4562_);
                leanh::lean_ctor_set(v___x_4564_, 1, v___x_4563_);
                v___x_4565_ = leanh::lean_box(1);
                v___x_4566_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4566_, 0, v___x_4564_);
                leanh::lean_ctor_set(v___x_4566_, 1, v___x_4565_);
                v___x_4567_ = l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5;
                v___x_4568_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4568_, 0, v___x_4566_);
                leanh::lean_ctor_set(v___x_4568_, 1, v___x_4567_);
                v___x_4569_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4569_, 0, v___x_4568_);
                leanh::lean_ctor_set(v___x_4569_, 1, v___x_4554_);
                v___x_4570_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once
                    ),
                    _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6,
                );
                v___x_4571_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__4_once),
                    _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                );
                match leanh::lean_obj_tag(v_host_4552_) {
                    0 => {
                        v_name_4602_ = leanh::lean_ctor_get(v_host_4552_, 0);
                        v_isSharedCheck_4611_ =
                            (!leanh::lean_is_exclusive(v_host_4552_)) as u8;
                        if v_isSharedCheck_4611_ == 0 {
                            v___x_4604_ = v_host_4552_;
                            v_isShared_4605_ = v_isSharedCheck_4611_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_name_4602_);
                            leanh::lean_dec(v_host_4552_);
                            v___x_4604_ = leanh::lean_box(0);
                            v_isShared_4605_ = v_isSharedCheck_4611_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        v_ipv4_4612_ = leanh::lean_ctor_get(v_host_4552_, 0);
                        v_isSharedCheck_4621_ =
                            (!leanh::lean_is_exclusive(v_host_4552_)) as u8;
                        if v_isSharedCheck_4621_ == 0 {
                            v___x_4614_ = v_host_4552_;
                            v_isShared_4615_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_ipv4_4612_);
                            leanh::lean_dec(v_host_4552_);
                            v___x_4614_ = leanh::lean_box(0);
                            v_isShared_4615_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        }
                    }
                    _ => {
                        v_ipv6_4622_ = leanh::lean_ctor_get(v_host_4552_, 0);
                        v_isSharedCheck_4631_ =
                            (!leanh::lean_is_exclusive(v_host_4552_)) as u8;
                        if v_isSharedCheck_4631_ == 0 {
                            v___x_4624_ = v_host_4552_;
                            v_isShared_4625_ = v_isSharedCheck_4631_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_ipv6_4622_);
                            leanh::lean_dec(v_host_4552_);
                            v___x_4624_ = leanh::lean_box(0);
                            v_isShared_4625_ = v_isSharedCheck_4631_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4575_ = l_Std_Http_URI_instReprHost___lam__0___closed__0;
                v___x_4576_ = lean_string_append(v___x_4575_, v_ctr_4573_);
                v___x_4577_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4577_, 0, v___x_4576_);
                v___x_4578_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4578_, 0, v___x_4577_);
                leanh::lean_ctor_set(v___x_4578_, 1, v___x_4565_);
                v___x_4579_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4579_, 0, v___x_4578_);
                leanh::lean_ctor_set(v___x_4579_, 1, v_a_4574_);
                v___x_4580_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4580_, 0, v___x_4571_);
                leanh::lean_ctor_set(v___x_4580_, 1, v___x_4579_);
                v___x_4581_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
                leanh::lean_ctor_set_uint8(
                    v___x_4581_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4560_,
                );
                v___x_4582_ = l_Repr_addAppParen(v___x_4581_, v___x_4557_);
                v___x_4583_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4583_, 0, v___x_4570_);
                leanh::lean_ctor_set(v___x_4583_, 1, v___x_4582_);
                v___x_4584_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                leanh::lean_ctor_set_uint8(
                    v___x_4584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4560_,
                );
                v___x_4585_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4585_, 0, v___x_4569_);
                leanh::lean_ctor_set(v___x_4585_, 1, v___x_4584_);
                v___x_4586_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4586_, 0, v___x_4585_);
                leanh::lean_ctor_set(v___x_4586_, 1, v___x_4563_);
                v___x_4587_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4587_, 0, v___x_4586_);
                leanh::lean_ctor_set(v___x_4587_, 1, v___x_4565_);
                v___x_4588_ = l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8;
                v___x_4589_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4589_, 0, v___x_4587_);
                leanh::lean_ctor_set(v___x_4589_, 1, v___x_4588_);
                v___x_4590_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4590_, 0, v___x_4589_);
                leanh::lean_ctor_set(v___x_4590_, 1, v___x_4554_);
                v___x_4591_ = l_Std_Http_URI_instReprPort_repr(v_port_4553_, v___x_4557_);
                leanh::lean_dec(v_port_4553_);
                v___x_4592_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4592_, 0, v___x_4570_);
                leanh::lean_ctor_set(v___x_4592_, 1, v___x_4591_);
                v___x_4593_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4593_, 0, v___x_4592_);
                leanh::lean_ctor_set_uint8(
                    v___x_4593_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4560_,
                );
                v___x_4594_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4594_, 0, v___x_4590_);
                leanh::lean_ctor_set(v___x_4594_, 1, v___x_4593_);
                v___x_4595_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14,
                );
                v___x_4596_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15;
                v___x_4597_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4597_, 0, v___x_4596_);
                leanh::lean_ctor_set(v___x_4597_, 1, v___x_4594_);
                v___x_4598_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16;
                v___x_4599_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4599_, 0, v___x_4597_);
                leanh::lean_ctor_set(v___x_4599_, 1, v___x_4598_);
                v___x_4600_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4600_, 0, v___x_4595_);
                leanh::lean_ctor_set(v___x_4600_, 1, v___x_4599_);
                v___x_4601_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4601_, 0, v___x_4600_);
                leanh::lean_ctor_set_uint8(
                    v___x_4601_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4560_,
                );
                return v___x_4601_;
            }
            2 => {
                v___x_4606_ = l_Std_Http_URI_instReprHost___lam__0___closed__1;
                v___x_4607_ = l_String_quote(v_name_4602_);
                if v_isShared_4605_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4604_, 3);
                    leanh::lean_ctor_set(v___x_4604_, 0, v___x_4607_);
                    v___x_4609_ = v___x_4604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4610_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4607_);
                    v___x_4609_ = v_reuseFailAlloc_4610_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_ctr_4573_ = v___x_4606_;
                v_a_4574_ = v___x_4609_;
                state = 1;
                continue;
            }
            4 => {
                v___x_4616_ = l_Std_Http_URI_instReprHost___lam__0___closed__2;
                v___x_4617_ = lean_uv_ntop_v4(v_ipv4_4612_);
                leanh::lean_dec_ref(v_ipv4_4612_);
                if v_isShared_4615_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4614_, 3);
                    leanh::lean_ctor_set(v___x_4614_, 0, v___x_4617_);
                    v___x_4619_ = v___x_4614_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_ctr_4573_ = v___x_4616_;
                v_a_4574_ = v___x_4619_;
                state = 1;
                continue;
            }
            6 => {
                v___x_4626_ = l_Std_Http_URI_instReprHost___lam__0___closed__3;
                v___x_4627_ = lean_uv_ntop_v6(v_ipv6_4622_);
                leanh::lean_dec_ref(v_ipv6_4622_);
                if v_isShared_4625_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4624_, 3);
                    leanh::lean_ctor_set(v___x_4624_, 0, v___x_4627_);
                    v___x_4629_ = v___x_4624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4630_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
                    v___x_4629_ = v_reuseFailAlloc_4630_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_ctr_4573_ = v___x_4626_;
                v_a_4574_ = v___x_4629_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instReprAuthority_repr(
    mut v_x_4632_: *mut leanh::LeanObject,
    mut v_prec_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4634_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_4632_);
    return v___x_4634_;
}
pub unsafe fn l_Std_Http_URI_instReprAuthority_repr___boxed(
    mut v_x_4635_: *mut leanh::LeanObject,
    mut v_prec_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4637_ = l_Std_Http_URI_instReprAuthority_repr(v_x_4635_, v_prec_4636_);
    leanh::lean_dec(v_prec_4636_);
    return v_res_4637_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(
    mut v_x_4640_: *mut leanh::LeanObject,
    mut v_x_4641_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4640_) == 0 {
        if leanh::lean_obj_tag(v_x_4641_) == 0 {
            let mut v___x_4642_: u8 = 0;
            v___x_4642_ = 1;
            return v___x_4642_;
        } else {
            let mut v___x_4643_: u8 = 0;
            v___x_4643_ = 0;
            return v___x_4643_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4641_) == 0 {
            let mut v___x_4644_: u8 = 0;
            v___x_4644_ = 0;
            return v___x_4644_;
        } else {
            let mut v_val_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4647_: u8 = 0;
            v_val_4645_ = leanh::lean_ctor_get(v_x_4640_, 0);
            v_val_4646_ = leanh::lean_ctor_get(v_x_4641_, 0);
            v___x_4647_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_4645_, v_val_4646_);
            return v___x_4647_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(
    mut v_x_4648_: *mut leanh::LeanObject,
    mut v_x_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4650_: u8 = 0;
    let mut v_r_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4650_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(
        v_x_4648_, v_x_4649_,
    );
    leanh::lean_dec(v_x_4649_);
    leanh::lean_dec(v_x_4648_);
    v_r_4651_ = leanh::lean_box((v_res_4650_) as usize);
    return v_r_4651_;
}
pub unsafe fn l_Std_Http_URI_instBEqAuthority_beq(
    mut v_x_4652_: *mut leanh::LeanObject,
    mut v_x_4653_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_userInfo_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    v_userInfo_4654_ = leanh::lean_ctor_get(v_x_4652_, 0);
    v_host_4655_ = leanh::lean_ctor_get(v_x_4652_, 1);
    v_port_4656_ = leanh::lean_ctor_get(v_x_4652_, 2);
    v_userInfo_4657_ = leanh::lean_ctor_get(v_x_4653_, 0);
    v_host_4658_ = leanh::lean_ctor_get(v_x_4653_, 1);
    v_port_4659_ = leanh::lean_ctor_get(v_x_4653_, 2);
    v___x_4660_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(
        v_userInfo_4654_,
        v_userInfo_4657_,
    );
    if v___x_4660_ == 0 {
        return v___x_4660_;
    } else {
        let mut v___x_4661_: u8 = 0;
        v___x_4661_ = l_Std_Http_URI_instBEqHost_beq(v_host_4655_, v_host_4658_);
        if v___x_4661_ == 0 {
            return v___x_4661_;
        } else {
            let mut v___x_4662_: u8 = 0;
            v___x_4662_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_4656_, v_port_4659_);
            return v___x_4662_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_instBEqAuthority_beq___boxed(
    mut v_x_4663_: *mut leanh::LeanObject,
    mut v_x_4664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4665_: u8 = 0;
    let mut v_r_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4665_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_4663_, v_x_4664_);
    leanh::lean_dec_ref(v_x_4664_);
    leanh::lean_dec_ref(v_x_4663_);
    v_r_4666_ = leanh::lean_box((v_res_4665_) as usize);
    return v_r_4666_;
}
pub unsafe fn l_Std_Http_URI_instToStringAuthority___lam__0(
    mut v_auth_4672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_4687_: u16 = 0;
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userInfo_4679_ = leanh::lean_ctor_get(v_auth_4672_, 0);
                leanh::lean_inc(v_userInfo_4679_);
                v_host_4680_ = leanh::lean_ctor_get(v_auth_4672_, 1);
                leanh::lean_inc_ref(v_host_4680_);
                v_port_4681_ = leanh::lean_ctor_get(v_auth_4672_, 2);
                leanh::lean_inc(v_port_4681_);
                leanh::lean_dec_ref(v_auth_4672_);
                if leanh::lean_obj_tag(v_userInfo_4679_) == 0 {
                    v___x_4703_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_4693_ = v___x_4703_;
                    state = 3;
                    continue;
                } else {
                    v_val_4704_ = leanh::lean_ctor_get(v_userInfo_4679_, 0);
                    leanh::lean_inc(v_val_4704_);
                    leanh::lean_dec_ref_known(v_userInfo_4679_, 1);
                    v_password_4705_ = leanh::lean_ctor_get(v_val_4704_, 1);
                    if leanh::lean_obj_tag(v_password_4705_) == 0 {
                        v_username_4706_ = leanh::lean_ctor_get(v_val_4704_, 0);
                        leanh::lean_inc_ref(v_username_4706_);
                        leanh::lean_dec(v_val_4704_);
                        v___x_4707_ = lean_string_from_utf8_unchecked(v_username_4706_);
                        v___x_4708_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                        v___x_4709_ = lean_string_append(v___x_4707_, v___x_4708_);
                        v___y_4693_ = v___x_4709_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_password_4705_);
                        v_username_4710_ = leanh::lean_ctor_get(v_val_4704_, 0);
                        leanh::lean_inc_ref(v_username_4710_);
                        leanh::lean_dec(v_val_4704_);
                        v_val_4711_ = leanh::lean_ctor_get(v_password_4705_, 0);
                        leanh::lean_inc(v_val_4711_);
                        leanh::lean_dec_ref_known(v_password_4705_, 1);
                        v___x_4712_ = lean_string_from_utf8_unchecked(v_username_4710_);
                        v___x_4713_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                        v___x_4714_ = lean_string_append(v___x_4712_, v___x_4713_);
                        v___x_4715_ = lean_string_from_utf8_unchecked(v_val_4711_);
                        v___x_4716_ = lean_string_append(v___x_4714_, v___x_4715_);
                        leanh::lean_dec_ref(v___x_4715_);
                        v___x_4717_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                        v___x_4718_ = lean_string_append(v___x_4716_, v___x_4717_);
                        v___y_4693_ = v___x_4718_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4677_ = lean_string_append(v___y_4674_, v___y_4675_);
                leanh::lean_dec_ref(v___y_4675_);
                v___x_4678_ = lean_string_append(v___x_4677_, v___y_4676_);
                leanh::lean_dec_ref(v___y_4676_);
                return v___x_4678_;
            }
            2 => match leanh::lean_obj_tag(v_port_4681_) {
                0 => {
                    v___x_4685_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_4674_ = v___y_4683_;
                    v___y_4675_ = v___y_4684_;
                    v___y_4676_ = v___x_4685_;
                    state = 1;
                    continue;
                }
                1 => {
                    v___x_4686_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_4674_ = v___y_4683_;
                    v___y_4675_ = v___y_4684_;
                    v___y_4676_ = v___x_4686_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_port_4687_ = leanh::lean_ctor_get_uint16(v_port_4681_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_4681_, 0);
                    v___x_4688_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_4689_ = lean_uint16_to_nat(v_port_4687_);
                    v___x_4690_ = l_Nat_reprFast(v___x_4689_);
                    v___x_4691_ = lean_string_append(v___x_4688_, v___x_4690_);
                    leanh::lean_dec_ref(v___x_4690_);
                    v___y_4674_ = v___y_4683_;
                    v___y_4675_ = v___y_4684_;
                    v___y_4676_ = v___x_4691_;
                    state = 1;
                    continue;
                }
            },
            3 => match leanh::lean_obj_tag(v_host_4680_) {
                0 => {
                    v_name_4694_ = leanh::lean_ctor_get(v_host_4680_, 0);
                    leanh::lean_inc_ref(v_name_4694_);
                    leanh::lean_dec_ref_known(v_host_4680_, 1);
                    v___y_4683_ = v___y_4693_;
                    v___y_4684_ = v_name_4694_;
                    state = 2;
                    continue;
                }
                1 => {
                    v_ipv4_4695_ = leanh::lean_ctor_get(v_host_4680_, 0);
                    leanh::lean_inc_ref(v_ipv4_4695_);
                    leanh::lean_dec_ref_known(v_host_4680_, 1);
                    v___x_4696_ = lean_uv_ntop_v4(v_ipv4_4695_);
                    leanh::lean_dec_ref(v_ipv4_4695_);
                    v___y_4683_ = v___y_4693_;
                    v___y_4684_ = v___x_4696_;
                    state = 2;
                    continue;
                }
                _ => {
                    v_ipv6_4697_ = leanh::lean_ctor_get(v_host_4680_, 0);
                    leanh::lean_inc_ref(v_ipv6_4697_);
                    leanh::lean_dec_ref_known(v_host_4680_, 1);
                    v___x_4698_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_4699_ = lean_uv_ntop_v6(v_ipv6_4697_);
                    leanh::lean_dec_ref(v_ipv6_4697_);
                    v___x_4700_ = lean_string_append(v___x_4698_, v___x_4699_);
                    leanh::lean_dec_ref(v___x_4699_);
                    v___x_4701_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_4702_ = lean_string_append(v___x_4700_, v___x_4701_);
                    v___y_4683_ = v___y_4693_;
                    v___y_4684_ = v___x_4702_;
                    state = 2;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_4728_: *mut leanh::LeanObject,
    mut v_x_4729_: *mut leanh::LeanObject,
    mut v_x_4730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4730_) == 0 {
                    leanh::lean_dec(v_x_4728_);
                    return v_x_4729_;
                } else {
                    v_head_4731_ = leanh::lean_ctor_get(v_x_4730_, 0);
                    v_tail_4732_ = leanh::lean_ctor_get(v_x_4730_, 1);
                    v_isSharedCheck_4744_ = (!leanh::lean_is_exclusive(v_x_4730_)) as u8;
                    if v_isSharedCheck_4744_ == 0 {
                        v___x_4734_ = v_x_4730_;
                        v_isShared_4735_ = v_isSharedCheck_4744_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4732_);
                        leanh::lean_inc(v_head_4731_);
                        leanh::lean_dec(v_x_4730_);
                        v___x_4734_ = leanh::lean_box(0);
                        v_isShared_4735_ = v_isSharedCheck_4744_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_4728_);
                if v_isShared_4735_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4734_, 5);
                    leanh::lean_ctor_set(v___x_4734_, 1, v_x_4728_);
                    leanh::lean_ctor_set(v___x_4734_, 0, v_x_4729_);
                    v___x_4737_ = v___x_4734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4743_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_x_4729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_x_4728_);
                    v___x_4737_ = v_reuseFailAlloc_4743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4738_ = lean_string_from_utf8_unchecked(v_head_4731_);
                v___x_4739_ = l_String_quote(v___x_4738_);
                v___x_4740_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4740_, 0, v___x_4739_);
                v___x_4741_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4741_, 0, v___x_4737_);
                leanh::lean_ctor_set(v___x_4741_, 1, v___x_4740_);
                v_x_4729_ = v___x_4741_;
                v_x_4730_ = v_tail_4732_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(
    mut v_x_4745_: *mut leanh::LeanObject,
    mut v_x_4746_: *mut leanh::LeanObject,
    mut v_x_4747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4747_) == 0 {
                    leanh::lean_dec(v_x_4745_);
                    return v_x_4746_;
                } else {
                    v_head_4748_ = leanh::lean_ctor_get(v_x_4747_, 0);
                    v_tail_4749_ = leanh::lean_ctor_get(v_x_4747_, 1);
                    v_isSharedCheck_4761_ = (!leanh::lean_is_exclusive(v_x_4747_)) as u8;
                    if v_isSharedCheck_4761_ == 0 {
                        v___x_4751_ = v_x_4747_;
                        v_isShared_4752_ = v_isSharedCheck_4761_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4749_);
                        leanh::lean_inc(v_head_4748_);
                        leanh::lean_dec(v_x_4747_);
                        v___x_4751_ = leanh::lean_box(0);
                        v_isShared_4752_ = v_isSharedCheck_4761_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_4745_);
                if v_isShared_4752_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4751_, 5);
                    leanh::lean_ctor_set(v___x_4751_, 1, v_x_4745_);
                    leanh::lean_ctor_set(v___x_4751_, 0, v_x_4746_);
                    v___x_4754_ = v___x_4751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4760_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_x_4746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_x_4745_);
                    v___x_4754_ = v_reuseFailAlloc_4760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4755_ = lean_string_from_utf8_unchecked(v_head_4748_);
                v___x_4756_ = l_String_quote(v___x_4755_);
                v___x_4757_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4757_, 0, v___x_4756_);
                v___x_4758_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4758_, 0, v___x_4754_);
                leanh::lean_ctor_set(v___x_4758_, 1, v___x_4757_);
                v___x_4759_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_4745_, v___x_4758_, v_tail_4749_);
                return v___x_4759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(
    mut v___y_4762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4763_ = lean_string_from_utf8_unchecked(v___y_4762_);
    v___x_4764_ = l_String_quote(v___x_4763_);
    v___x_4765_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4765_, 0, v___x_4764_);
    return v___x_4765_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(
    mut v_x_4766_: *mut leanh::LeanObject,
    mut v_x_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4766_) == 0 {
        let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4767_);
        v___x_4768_ = leanh::lean_box(0);
        return v___x_4768_;
    } else {
        let mut v_tail_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4769_ = leanh::lean_ctor_get(v_x_4766_, 1);
        if leanh::lean_obj_tag(v_tail_4769_) == 0 {
            let mut v_head_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_4767_);
            v_head_4770_ = leanh::lean_ctor_get(v_x_4766_, 0);
            leanh::lean_inc(v_head_4770_);
            leanh::lean_dec_ref_known(v_x_4766_, 2);
            v___x_4771_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_4770_);
            return v___x_4771_;
        } else {
            let mut v_head_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_4769_);
            v_head_4772_ = leanh::lean_ctor_get(v_x_4766_, 0);
            leanh::lean_inc(v_head_4772_);
            leanh::lean_dec_ref_known(v_x_4766_, 2);
            v___x_4773_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_4772_);
            v___x_4774_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_4767_, v___x_4773_, v_tail_4769_);
            return v___x_4774_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4779_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0;
    v___x_4780_ = lean_string_length(v___x_4779_);
    return v___x_4780_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4781_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once
        ),
        _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2,
    );
    v___x_4782_ = lean_nat_to_int(v___x_4781_);
    return v___x_4782_;
}
pub unsafe fn l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(
    mut v_xs_4790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: u8 = 0;
    v___x_4791_ = lean_array_get_size(v_xs_4790_);
    v___x_4792_ = leanh::lean_unsigned_to_nat(0);
    v___x_4793_ = lean_nat_dec_eq(v___x_4791_, v___x_4792_);
    if v___x_4793_ == 0 {
        let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4794_ = lean_array_to_list(v_xs_4790_);
        v___x_4795_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1;
        v___x_4796_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_4794_, v___x_4795_);
        v___x_4797_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once
            ),
            _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3,
        );
        v___x_4798_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4;
        v___x_4799_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4799_, 0, v___x_4798_);
        leanh::lean_ctor_set(v___x_4799_, 1, v___x_4796_);
        v___x_4800_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5;
        v___x_4801_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4801_, 0, v___x_4799_);
        leanh::lean_ctor_set(v___x_4801_, 1, v___x_4800_);
        v___x_4802_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4802_, 0, v___x_4797_);
        leanh::lean_ctor_set(v___x_4802_, 1, v___x_4801_);
        v___x_4803_ = l_Std_Format_fill(v___x_4802_);
        return v___x_4803_;
    } else {
        let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_4790_);
        v___x_4804_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7;
        return v___x_4804_;
    }
}
pub unsafe fn l_Std_Http_URI_instReprPath_repr___redArg(
    mut v_x_4817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4819_: u8 = 0;
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: u8 = 0;
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_segments_4818_ = leanh::lean_ctor_get(v_x_4817_, 0);
                v_absolute_4819_ = leanh::lean_ctor_get_uint8(
                    v_x_4817_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4851_ = (!leanh::lean_is_exclusive(v_x_4817_)) as u8;
                if v_isSharedCheck_4851_ == 0 {
                    v___x_4821_ = v_x_4817_;
                    v_isShared_4822_ = v_isSharedCheck_4851_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_segments_4818_);
                    leanh::lean_dec(v_x_4817_);
                    v___x_4821_ = leanh::lean_box(0);
                    v_isShared_4822_ = v_isSharedCheck_4851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4823_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5;
                v___x_4824_ = l_Std_Http_URI_instReprPath_repr___redArg___closed__3;
                v___x_4825_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7,
                );
                v___x_4826_ =
                    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_4818_);
                v___x_4827_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4827_, 0, v___x_4825_);
                leanh::lean_ctor_set(v___x_4827_, 1, v___x_4826_);
                v___x_4828_ = 0;
                if v_isShared_4822_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4821_, 6);
                    leanh::lean_ctor_set(v___x_4821_, 0, v___x_4827_);
                    v___x_4830_ = v___x_4821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4850_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4827_);
                    v___x_4830_ = v_reuseFailAlloc_4850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4830_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4828_,
                );
                v___x_4831_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4831_, 0, v___x_4824_);
                leanh::lean_ctor_set(v___x_4831_, 1, v___x_4830_);
                v___x_4832_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9;
                v___x_4833_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4833_, 0, v___x_4831_);
                leanh::lean_ctor_set(v___x_4833_, 1, v___x_4832_);
                v___x_4834_ = leanh::lean_box(1);
                v___x_4835_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4835_, 0, v___x_4833_);
                leanh::lean_ctor_set(v___x_4835_, 1, v___x_4834_);
                v___x_4836_ = l_Std_Http_URI_instReprPath_repr___redArg___closed__5;
                v___x_4837_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4837_, 0, v___x_4835_);
                leanh::lean_ctor_set(v___x_4837_, 1, v___x_4836_);
                v___x_4838_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4838_, 0, v___x_4837_);
                leanh::lean_ctor_set(v___x_4838_, 1, v___x_4823_);
                v___x_4839_ = l_Bool_repr___redArg(v_absolute_4819_);
                v___x_4840_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4840_, 0, v___x_4825_);
                leanh::lean_ctor_set(v___x_4840_, 1, v___x_4839_);
                v___x_4841_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4841_, 0, v___x_4840_);
                leanh::lean_ctor_set_uint8(
                    v___x_4841_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4828_,
                );
                v___x_4842_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4842_, 0, v___x_4838_);
                leanh::lean_ctor_set(v___x_4842_, 1, v___x_4841_);
                v___x_4843_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14,
                );
                v___x_4844_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15;
                v___x_4845_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4845_, 0, v___x_4844_);
                leanh::lean_ctor_set(v___x_4845_, 1, v___x_4842_);
                v___x_4846_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16;
                v___x_4847_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4847_, 0, v___x_4845_);
                leanh::lean_ctor_set(v___x_4847_, 1, v___x_4846_);
                v___x_4848_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4848_, 0, v___x_4843_);
                leanh::lean_ctor_set(v___x_4848_, 1, v___x_4847_);
                v___x_4849_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4849_, 0, v___x_4848_);
                leanh::lean_ctor_set_uint8(
                    v___x_4849_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4828_,
                );
                return v___x_4849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_instReprPath_repr(
    mut v_x_4852_: *mut leanh::LeanObject,
    mut v_prec_4853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4854_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_4852_);
    return v___x_4854_;
}
pub unsafe fn l_Std_Http_URI_instReprPath_repr___boxed(
    mut v_x_4855_: *mut leanh::LeanObject,
    mut v_prec_4856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Std_Http_URI_instReprPath_repr(v_x_4855_, v_prec_4856_);
    leanh::lean_dec(v_prec_4856_);
    return v_res_4857_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(
    mut v_xs_4860_: *mut leanh::LeanObject,
    mut v_ys_4861_: *mut leanh::LeanObject,
    mut v_x_4862_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4864_: u8 = 0;
    let mut v_one_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4863_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4864_ = lean_nat_dec_eq(v_x_4862_, v_zero_4863_);
                if v_isZero_4864_ == 1 {
                    leanh::lean_dec(v_x_4862_);
                    return v_isZero_4864_;
                } else {
                    v_one_4865_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4866_ = lean_nat_sub(v_x_4862_, v_one_4865_);
                    leanh::lean_dec(v_x_4862_);
                    v___x_4867_ = lean_array_fget_borrowed(v_xs_4860_, v_n_4866_);
                    v___x_4868_ = lean_array_fget_borrowed(v_ys_4861_, v_n_4866_);
                    v___x_4869_ = lean_sarray_dec_eq(v___x_4867_, v___x_4868_);
                    if v___x_4869_ == 0 {
                        leanh::lean_dec(v_n_4866_);
                        return v___x_4869_;
                    } else {
                        v_x_4862_ = v_n_4866_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(
    mut v_xs_4871_: *mut leanh::LeanObject,
    mut v_ys_4872_: *mut leanh::LeanObject,
    mut v_x_4873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4874_: u8 = 0;
    let mut v_r_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4874_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(
        v_xs_4871_, v_ys_4872_, v_x_4873_,
    );
    leanh::lean_dec_ref(v_ys_4872_);
    leanh::lean_dec_ref(v_xs_4871_);
    v_r_4875_ = leanh::lean_box((v_res_4874_) as usize);
    return v_r_4875_;
}
pub unsafe fn l_Std_Http_URI_instBEqPath_beq(
    mut v_x_4876_: *mut leanh::LeanObject,
    mut v_x_4877_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_segments_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4879_: u8 = 0;
    let mut v_segments_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4881_: u8 = 0;
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: u8 = 0;
    v_segments_4878_ = leanh::lean_ctor_get(v_x_4876_, 0);
    v_absolute_4879_ = leanh::lean_ctor_get_uint8(
        v_x_4876_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v_segments_4880_ = leanh::lean_ctor_get(v_x_4877_, 0);
    v_absolute_4881_ = leanh::lean_ctor_get_uint8(
        v_x_4877_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v___x_4882_ = lean_array_get_size(v_segments_4878_);
    v___x_4883_ = lean_array_get_size(v_segments_4880_);
    v___x_4884_ = lean_nat_dec_eq(v___x_4882_, v___x_4883_);
    if v___x_4884_ == 0 {
        return v___x_4884_;
    } else {
        let mut v___x_4885_: u8 = 0;
        v___x_4885_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(
            v_segments_4878_,
            v_segments_4880_,
            v___x_4882_,
        );
        if v___x_4885_ == 0 {
            return v___x_4885_;
        } else {
            if v_absolute_4879_ == 0 {
                if v_absolute_4881_ == 0 {
                    return v___x_4885_;
                } else {
                    return v_absolute_4879_;
                }
            } else {
                return v_absolute_4881_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_instBEqPath_beq___boxed(
    mut v_x_4886_: *mut leanh::LeanObject,
    mut v_x_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4888_: u8 = 0;
    let mut v_r_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4888_ = l_Std_Http_URI_instBEqPath_beq(v_x_4886_, v_x_4887_);
    leanh::lean_dec_ref(v_x_4887_);
    leanh::lean_dec_ref(v_x_4886_);
    v_r_4889_ = leanh::lean_box((v_res_4888_) as usize);
    return v_r_4889_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(
    mut v_xs_4890_: *mut leanh::LeanObject,
    mut v_ys_4891_: *mut leanh::LeanObject,
    mut v_hsz_4892_: *mut leanh::LeanObject,
    mut v_x_4893_: *mut leanh::LeanObject,
    mut v_x_4894_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4895_: u8 = 0;
    v___x_4895_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(
        v_xs_4890_, v_ys_4891_, v_x_4893_,
    );
    return v___x_4895_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(
    mut v_xs_4896_: *mut leanh::LeanObject,
    mut v_ys_4897_: *mut leanh::LeanObject,
    mut v_hsz_4898_: *mut leanh::LeanObject,
    mut v_x_4899_: *mut leanh::LeanObject,
    mut v_x_4900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4901_: u8 = 0;
    let mut v_r_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(
        v_xs_4896_,
        v_ys_4897_,
        v_hsz_4898_,
        v_x_4899_,
        v_x_4900_,
    );
    leanh::lean_dec_ref(v_ys_4897_);
    leanh::lean_dec_ref(v_xs_4896_);
    v_r_4902_ = leanh::lean_box((v_res_4901_) as usize);
    return v_r_4902_;
}
pub unsafe fn l_Std_Http_URI_instToStringPath___lam__0(
    mut v_x_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4906_ = lean_string_from_utf8_unchecked(v_x_4905_);
    return v___x_4906_;
}
pub unsafe fn l_Std_Http_URI_instToStringPath___lam__1(
    mut v___f_4927_: *mut leanh::LeanObject,
    mut v_path_4928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4930_: u8 = 0;
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4933_: usize = 0;
    let mut v___x_4934_: usize = 0;
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_segments_4929_ = leanh::lean_ctor_get(v_path_4928_, 0);
    leanh::lean_inc_ref(v_segments_4929_);
    v_absolute_4930_ = leanh::lean_ctor_get_uint8(
        v_path_4928_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    leanh::lean_dec_ref(v_path_4928_);
    v___x_4931_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
    v___x_4932_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
    v_sz_4933_ = lean_array_size(v_segments_4929_);
    v___x_4934_ = 0usize;
    v___x_4935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4932_,
        v___f_4927_,
        v_sz_4933_,
        v___x_4934_,
        v_segments_4929_,
    );
    v___x_4936_ = lean_array_to_list(v___x_4935_);
    v_result_4937_ = l_String_intercalate(v___x_4931_, v___x_4936_);
    if v_absolute_4930_ == 0 {
        return v_result_4937_;
    } else {
        let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4938_ = lean_string_append(v___x_4931_, v_result_4937_);
        leanh::lean_dec_ref(v_result_4937_);
        return v___x_4938_;
    }
}
pub unsafe fn l_Std_Http_URI_Path_isEmpty(mut v_p_4943_: *mut leanh::LeanObject) -> u8 {
    let mut v_segments_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    v_segments_4944_ = leanh::lean_ctor_get(v_p_4943_, 0);
    v___x_4945_ = lean_array_get_size(v_segments_4944_);
    v___x_4946_ = leanh::lean_unsigned_to_nat(0);
    v___x_4947_ = lean_nat_dec_eq(v___x_4945_, v___x_4946_);
    return v___x_4947_;
}
pub unsafe fn l_Std_Http_URI_Path_isEmpty___boxed(
    mut v_p_4948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4949_: u8 = 0;
    let mut v_r_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4949_ = l_Std_Http_URI_Path_isEmpty(v_p_4948_);
    leanh::lean_dec_ref(v_p_4948_);
    v_r_4950_ = leanh::lean_box((v_res_4949_) as usize);
    return v_r_4950_;
}
pub unsafe fn l_Std_Http_URI_Path_parent(
    mut v_p_4951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4953_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_segments_4952_ = leanh::lean_ctor_get(v_p_4951_, 0);
                v_absolute_4953_ = leanh::lean_ctor_get_uint8(
                    v_p_4951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_4954_ = lean_array_get_size(v_segments_4952_);
                v___x_4955_ = leanh::lean_unsigned_to_nat(0);
                v___x_4956_ = lean_nat_dec_eq(v___x_4954_, v___x_4955_);
                if v___x_4956_ == 0 {
                    leanh::lean_inc_ref(v_segments_4952_);
                    v_isSharedCheck_4964_ = (!leanh::lean_is_exclusive(v_p_4951_)) as u8;
                    if v_isSharedCheck_4964_ == 0 {
                        v_unused_4965_ = leanh::lean_ctor_get(v_p_4951_, 0);
                        leanh::lean_dec(v_unused_4965_);
                        v___x_4958_ = v_p_4951_;
                        v_isShared_4959_ = v_isSharedCheck_4964_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_p_4951_);
                        v___x_4958_ = leanh::lean_box(0);
                        v_isShared_4959_ = v_isSharedCheck_4964_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_p_4951_;
                }
            }
            1 => {
                v___x_4960_ = lean_array_pop(v_segments_4952_);
                if v_isShared_4959_ == 0 {
                    leanh::lean_ctor_set(v___x_4958_, 0, v___x_4960_);
                    v___x_4962_ = v___x_4958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4960_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4963_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_absolute_4953_,
                    );
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_join(
    mut v_p1_4966_: *mut leanh::LeanObject,
    mut v_p2_4967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_absolute_4968_: u8 = 0;
    let mut v_segments_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4971_: u8 = 0;
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4974_: u8 = 0;
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_absolute_4968_ = leanh::lean_ctor_get_uint8(
                    v_p2_4967_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_absolute_4968_ == 0 {
                    v_segments_4969_ = leanh::lean_ctor_get(v_p2_4967_, 0);
                    v_segments_4970_ = leanh::lean_ctor_get(v_p1_4966_, 0);
                    v_absolute_4971_ = leanh::lean_ctor_get_uint8(
                        v_p1_4966_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_4979_ = (!leanh::lean_is_exclusive(v_p1_4966_)) as u8;
                    if v_isSharedCheck_4979_ == 0 {
                        v___x_4973_ = v_p1_4966_;
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_segments_4970_);
                        leanh::lean_dec(v_p1_4966_);
                        v___x_4973_ = leanh::lean_box(0);
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p1_4966_);
                    leanh::lean_inc_ref(v_p2_4967_);
                    return v_p2_4967_;
                }
            }
            1 => {
                v___x_4975_ = l_Array_append___redArg(v_segments_4970_, v_segments_4969_);
                if v_isShared_4974_ == 0 {
                    leanh::lean_ctor_set(v___x_4973_, 0, v___x_4975_);
                    v___x_4977_ = v___x_4973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4975_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4978_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_absolute_4971_,
                    );
                    v___x_4977_ = v_reuseFailAlloc_4978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_join___boxed(
    mut v_p1_4980_: *mut leanh::LeanObject,
    mut v_p2_4981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Std_Http_URI_Path_join(v_p1_4980_, v_p2_4981_);
    leanh::lean_dec_ref(v_p2_4981_);
    return v_res_4982_;
}
pub unsafe fn l_Std_Http_URI_Path_append(
    mut v_p_4983_: *mut leanh::LeanObject,
    mut v_segment_4984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_4986_: u8 = 0;
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4989_: u8 = 0;
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_segments_4985_ = leanh::lean_ctor_get(v_p_4983_, 0);
                v_absolute_4986_ = leanh::lean_ctor_get_uint8(
                    v_p_4983_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4995_ = (!leanh::lean_is_exclusive(v_p_4983_)) as u8;
                if v_isSharedCheck_4995_ == 0 {
                    v___x_4988_ = v_p_4983_;
                    v_isShared_4989_ = v_isSharedCheck_4995_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_segments_4985_);
                    leanh::lean_dec(v_p_4983_);
                    v___x_4988_ = leanh::lean_box(0);
                    v_isShared_4989_ = v_isSharedCheck_4995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4990_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_4984_);
                v___x_4991_ = lean_array_push(v_segments_4985_, v___x_4990_);
                if v_isShared_4989_ == 0 {
                    leanh::lean_ctor_set(v___x_4988_, 0, v___x_4991_);
                    v___x_4993_ = v___x_4988_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4994_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4991_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4994_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_absolute_4986_,
                    );
                    v___x_4993_ = v_reuseFailAlloc_4994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_append___boxed(
    mut v_p_4996_: *mut leanh::LeanObject,
    mut v_segment_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4998_ = l_Std_Http_URI_Path_append(v_p_4996_, v_segment_4997_);
    leanh::lean_dec_ref(v_segment_4997_);
    return v_res_4998_;
}
pub unsafe fn l_Std_Http_URI_Path_appendEncoded(
    mut v_p_4999_: *mut leanh::LeanObject,
    mut v_segment_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_5002_: u8 = 0;
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5005_: u8 = 0;
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_segments_5001_ = leanh::lean_ctor_get(v_p_4999_, 0);
                v_absolute_5002_ = leanh::lean_ctor_get_uint8(
                    v_p_4999_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5010_ = (!leanh::lean_is_exclusive(v_p_4999_)) as u8;
                if v_isSharedCheck_5010_ == 0 {
                    v___x_5004_ = v_p_4999_;
                    v_isShared_5005_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_segments_5001_);
                    leanh::lean_dec(v_p_4999_);
                    v___x_5004_ = leanh::lean_box(0);
                    v_isShared_5005_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5006_ = lean_array_push(v_segments_5001_, v_segment_5000_);
                if v_isShared_5005_ == 0 {
                    leanh::lean_ctor_set(v___x_5004_, 0, v___x_5006_);
                    v___x_5008_ = v___x_5004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5006_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5009_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_absolute_5002_,
                    );
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(
    mut v_input_5013_: *mut leanh::LeanObject,
    mut v_output_5014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: u8 = 0;
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_input_5013_) == 0 {
                    v___x_5015_ = l_List_reverse___redArg(v_output_5014_);
                    return v___x_5015_;
                } else {
                    v_head_5016_ = leanh::lean_ctor_get(v_input_5013_, 0);
                    v_tail_5017_ = leanh::lean_ctor_get(v_input_5013_, 1);
                    v_isSharedCheck_5034_ = (!leanh::lean_is_exclusive(v_input_5013_)) as u8;
                    if v_isSharedCheck_5034_ == 0 {
                        v___x_5019_ = v_input_5013_;
                        v_isShared_5020_ = v_isSharedCheck_5034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5017_);
                        leanh::lean_inc(v_head_5016_);
                        leanh::lean_dec(v_input_5013_);
                        v___x_5019_ = leanh::lean_box(0);
                        v_isShared_5020_ = v_isSharedCheck_5034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_head_5016_);
                v___x_5021_ = lean_string_from_utf8_unchecked(v_head_5016_);
                v___x_5022_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0;
                v___x_5023_ = lean_string_dec_eq(v___x_5021_, v___x_5022_);
                if v___x_5023_ == 0 {
                    v___x_5024_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1;
                    v___x_5025_ = lean_string_dec_eq(v___x_5021_, v___x_5024_);
                    leanh::lean_dec_ref(v___x_5021_);
                    if v___x_5025_ == 0 {
                        if v_isShared_5020_ == 0 {
                            leanh::lean_ctor_set(v___x_5019_, 1, v_output_5014_);
                            v___x_5027_ = v___x_5019_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5029_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_head_5016_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5029_, 1, v_output_5014_);
                            v___x_5027_ = v_reuseFailAlloc_5029_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5019_);
                        leanh::lean_dec(v_head_5016_);
                        if leanh::lean_obj_tag(v_output_5014_) == 0 {
                            v_input_5013_ = v_tail_5017_;
                            state = 0;
                            continue;
                        } else {
                            v_tail_5031_ = leanh::lean_ctor_get(v_output_5014_, 1);
                            leanh::lean_inc(v_tail_5031_);
                            leanh::lean_dec_ref_known(v_output_5014_, 2);
                            v_input_5013_ = v_tail_5017_;
                            v_output_5014_ = v_tail_5031_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5021_);
                    leanh::lean_del_object(v___x_5019_);
                    leanh::lean_dec(v_head_5016_);
                    v_input_5013_ = v_tail_5017_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_input_5013_ = v_tail_5017_;
                v_output_5014_ = v___x_5027_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_normalize(
    mut v_p_5035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_5037_: u8 = 0;
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_segments_5036_ = leanh::lean_ctor_get(v_p_5035_, 0);
                v_absolute_5037_ = leanh::lean_ctor_get_uint8(
                    v_p_5035_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5048_ = (!leanh::lean_is_exclusive(v_p_5035_)) as u8;
                if v_isSharedCheck_5048_ == 0 {
                    v___x_5039_ = v_p_5035_;
                    v_isShared_5040_ = v_isSharedCheck_5048_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_segments_5036_);
                    leanh::lean_dec(v_p_5035_);
                    v___x_5039_ = leanh::lean_box(0);
                    v_isShared_5040_ = v_isSharedCheck_5048_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5041_ = lean_array_to_list(v_segments_5036_);
                v___x_5042_ = leanh::lean_box(0);
                v___x_5043_ =
                    l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(
                        v___x_5041_,
                        v___x_5042_,
                    );
                v___x_5044_ = lean_array_mk(v___x_5043_);
                if v_isShared_5040_ == 0 {
                    leanh::lean_ctor_set(v___x_5039_, 0, v___x_5044_);
                    v___x_5046_ = v___x_5039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5047_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5047_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_absolute_5037_,
                    );
                    v___x_5046_ = v_reuseFailAlloc_5047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(
    mut v_sz_5049_: usize,
    mut v_i_5050_: usize,
    mut v_bs_5051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5052_: u8 = 0;
    let mut v_v_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: usize = 0;
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5052_ = lean_usize_dec_lt(v_i_5050_, v_sz_5049_);
                if v___x_5052_ == 0 {
                    return v_bs_5051_;
                } else {
                    v_v_5053_ = lean_array_uget(v_bs_5051_, v_i_5050_);
                    v___x_5054_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5055_ = lean_array_uset(v_bs_5051_, v_i_5050_, v___x_5054_);
                    v___x_5062_ = l_Std_Http_URI_EncodedSegment_decode(v_v_5053_);
                    if leanh::lean_obj_tag(v___x_5062_) == 0 {
                        v___x_5063_ = lean_string_from_utf8_unchecked(v_v_5053_);
                        v___y_5057_ = v___x_5063_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_v_5053_);
                        v_val_5064_ = leanh::lean_ctor_get(v___x_5062_, 0);
                        leanh::lean_inc(v_val_5064_);
                        leanh::lean_dec_ref_known(v___x_5062_, 1);
                        v___y_5057_ = v_val_5064_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5058_ = 1usize;
                v___x_5059_ = lean_usize_add(v_i_5050_, v___x_5058_);
                v___x_5060_ = lean_array_uset(v_bs_x27_5055_, v_i_5050_, v___y_5057_);
                v_i_5050_ = v___x_5059_;
                v_bs_5051_ = v___x_5060_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(
    mut v_sz_5065_: *mut leanh::LeanObject,
    mut v_i_5066_: *mut leanh::LeanObject,
    mut v_bs_5067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5068_: usize = 0;
    let mut v_i_boxed_5069_: usize = 0;
    let mut v_res_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5068_ = leanh::lean_unbox_usize(v_sz_5065_);
    leanh::lean_dec(v_sz_5065_);
    v_i_boxed_5069_ = leanh::lean_unbox_usize(v_i_5066_);
    leanh::lean_dec(v_i_5066_);
    v_res_5070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_5068_, v_i_boxed_5069_, v_bs_5067_);
    return v_res_5070_;
}
pub unsafe fn l_Std_Http_URI_Path_toDecodedSegments(
    mut v_p_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_segments_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5073_: usize = 0;
    let mut v___x_5074_: usize = 0;
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_segments_5072_ = leanh::lean_ctor_get(v_p_5071_, 0);
    leanh::lean_inc_ref(v_segments_5072_);
    leanh::lean_dec_ref(v_p_5071_);
    v_sz_5073_ = lean_array_size(v_segments_5072_);
    v___x_5074_ = 0usize;
    v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_5073_, v___x_5074_, v_segments_5072_);
    return v___x_5075_;
}
pub unsafe fn l_Std_Http_URI_instReprQuery___aux__1___redArg(
    mut v_xs_5084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5085_ = l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3;
    v___x_5086_ = l_Array_repr___redArg(v___x_5085_, v_xs_5084_);
    return v___x_5086_;
}
pub unsafe fn l_Std_Http_URI_instReprQuery___aux__1(
    mut v_xs_5087_: *mut leanh::LeanObject,
    mut v_x_5088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3;
    v___x_5090_ = l_Array_repr___redArg(v___x_5089_, v_xs_5087_);
    return v___x_5090_;
}
pub unsafe fn l_Std_Http_URI_instReprQuery___aux__1___boxed(
    mut v_xs_5091_: *mut leanh::LeanObject,
    mut v_x_5092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5093_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_5091_, v_x_5092_);
    leanh::lean_dec(v_x_5092_);
    return v_res_5093_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(
    mut v_x_5094_: *mut leanh::LeanObject,
    mut v_x_5095_: *mut leanh::LeanObject,
    mut v_x_5096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5096_) == 0 {
                    leanh::lean_dec(v_x_5094_);
                    return v_x_5095_;
                } else {
                    v_head_5097_ = leanh::lean_ctor_get(v_x_5096_, 0);
                    v_tail_5098_ = leanh::lean_ctor_get(v_x_5096_, 1);
                    v_isSharedCheck_5107_ = (!leanh::lean_is_exclusive(v_x_5096_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5100_ = v_x_5096_;
                        v_isShared_5101_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5098_);
                        leanh::lean_inc(v_head_5097_);
                        leanh::lean_dec(v_x_5096_);
                        v___x_5100_ = leanh::lean_box(0);
                        v_isShared_5101_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_5094_);
                if v_isShared_5101_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5100_, 5);
                    leanh::lean_ctor_set(v___x_5100_, 1, v_x_5094_);
                    leanh::lean_ctor_set(v___x_5100_, 0, v_x_5095_);
                    v___x_5103_ = v___x_5100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_x_5095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_x_5094_);
                    v___x_5103_ = v_reuseFailAlloc_5106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5104_, 0, v___x_5103_);
                leanh::lean_ctor_set(v___x_5104_, 1, v_head_5097_);
                v_x_5095_ = v___x_5104_;
                v_x_5096_ = v_tail_5098_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(
    mut v_x_5108_: *mut leanh::LeanObject,
    mut v_x_5109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5108_) == 0 {
        let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5109_);
        v___x_5110_ = leanh::lean_box(0);
        return v___x_5110_;
    } else {
        let mut v_tail_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_5111_ = leanh::lean_ctor_get(v_x_5108_, 1);
        if leanh::lean_obj_tag(v_tail_5111_) == 0 {
            let mut v_head_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_5109_);
            v_head_5112_ = leanh::lean_ctor_get(v_x_5108_, 0);
            leanh::lean_inc(v_head_5112_);
            leanh::lean_dec_ref_known(v_x_5108_, 2);
            return v_head_5112_;
        } else {
            let mut v_head_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_5111_);
            v_head_5113_ = leanh::lean_ctor_get(v_x_5108_, 0);
            leanh::lean_inc(v_head_5113_);
            leanh::lean_dec_ref_known(v_x_5108_, 2);
            v___x_5114_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_5109_, v_head_5113_, v_tail_5111_);
            return v___x_5114_;
        }
    }
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(
    mut v_x_5115_: *mut leanh::LeanObject,
    mut v_x_5116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5115_) == 0 {
                    v___x_5117_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
                    return v___x_5117_;
                } else {
                    v_val_5118_ = leanh::lean_ctor_get(v_x_5115_, 0);
                    v_isSharedCheck_5130_ = (!leanh::lean_is_exclusive(v_x_5115_)) as u8;
                    if v_isSharedCheck_5130_ == 0 {
                        v___x_5120_ = v_x_5115_;
                        v_isShared_5121_ = v_isSharedCheck_5130_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5118_);
                        leanh::lean_dec(v_x_5115_);
                        v___x_5120_ = leanh::lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5130_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5122_ =
                    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
                v___x_5123_ = lean_string_from_utf8_unchecked(v_val_5118_);
                v___x_5124_ = l_String_quote(v___x_5123_);
                if v_isShared_5121_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5120_, 3);
                    leanh::lean_ctor_set(v___x_5120_, 0, v___x_5124_);
                    v___x_5126_ = v___x_5120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5124_);
                    v___x_5126_ = v_reuseFailAlloc_5129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5127_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5127_, 0, v___x_5122_);
                leanh::lean_ctor_set(v___x_5127_, 1, v___x_5126_);
                v___x_5128_ = l_Repr_addAppParen(v___x_5127_, v_x_5116_);
                return v___x_5128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(
    mut v_x_5131_: *mut leanh::LeanObject,
    mut v_x_5132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5133_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_5131_, v_x_5132_);
    leanh::lean_dec(v_x_5132_);
    return v_res_5133_;
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5136_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0;
    v___x_5137_ = lean_string_length(v___x_5136_);
    return v___x_5137_;
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5138_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
    v___x_5139_ = lean_nat_to_int(v___x_5138_);
    return v___x_5139_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(
    mut v_x_5144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5149_: u8 = 0;
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: u8 = 0;
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5145_ = leanh::lean_ctor_get(v_x_5144_, 0);
                v_snd_5146_ = leanh::lean_ctor_get(v_x_5144_, 1);
                v_isSharedCheck_5171_ = (!leanh::lean_is_exclusive(v_x_5144_)) as u8;
                if v_isSharedCheck_5171_ == 0 {
                    v___x_5148_ = v_x_5144_;
                    v_isShared_5149_ = v_isSharedCheck_5171_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5146_);
                    leanh::lean_inc(v_fst_5145_);
                    leanh::lean_dec(v_x_5144_);
                    v___x_5148_ = leanh::lean_box(0);
                    v_isShared_5149_ = v_isSharedCheck_5171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5150_ = lean_string_from_utf8_unchecked(v_fst_5145_);
                v___x_5151_ = l_String_quote(v___x_5150_);
                v___x_5152_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
                v___x_5153_ = leanh::lean_box(0);
                if v_isShared_5149_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5148_, 1);
                    leanh::lean_ctor_set(v___x_5148_, 1, v___x_5153_);
                    leanh::lean_ctor_set(v___x_5148_, 0, v___x_5152_);
                    v___x_5155_ = v___x_5148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v___x_5153_);
                    v___x_5155_ = v_reuseFailAlloc_5170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5156_ = leanh::lean_unsigned_to_nat(0);
                v___x_5157_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_5146_, v___x_5156_);
                v___x_5158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5158_, 0, v___x_5157_);
                leanh::lean_ctor_set(v___x_5158_, 1, v___x_5155_);
                v___x_5159_ = l_List_reverse___redArg(v___x_5158_);
                v___x_5160_ =
                    l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1;
                v___x_5161_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_5159_, v___x_5160_);
                v___x_5162_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
                v___x_5163_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4;
                v___x_5164_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5164_, 0, v___x_5163_);
                leanh::lean_ctor_set(v___x_5164_, 1, v___x_5161_);
                v___x_5165_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5;
                v___x_5166_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5166_, 0, v___x_5164_);
                leanh::lean_ctor_set(v___x_5166_, 1, v___x_5165_);
                v___x_5167_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5167_, 0, v___x_5162_);
                leanh::lean_ctor_set(v___x_5167_, 1, v___x_5166_);
                v___x_5168_ = 0;
                v___x_5169_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5169_, 0, v___x_5167_);
                leanh::lean_ctor_set_uint8(
                    v___x_5169_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5168_,
                );
                return v___x_5169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(
    mut v_x_5172_: *mut leanh::LeanObject,
    mut v_x_5173_: *mut leanh::LeanObject,
    mut v_x_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5174_) == 0 {
                    leanh::lean_dec(v_x_5172_);
                    return v_x_5173_;
                } else {
                    v_head_5175_ = leanh::lean_ctor_get(v_x_5174_, 0);
                    v_tail_5176_ = leanh::lean_ctor_get(v_x_5174_, 1);
                    v_isSharedCheck_5186_ = (!leanh::lean_is_exclusive(v_x_5174_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5178_ = v_x_5174_;
                        v_isShared_5179_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5176_);
                        leanh::lean_inc(v_head_5175_);
                        leanh::lean_dec(v_x_5174_);
                        v___x_5178_ = leanh::lean_box(0);
                        v_isShared_5179_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_5172_);
                if v_isShared_5179_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5178_, 5);
                    leanh::lean_ctor_set(v___x_5178_, 1, v_x_5172_);
                    leanh::lean_ctor_set(v___x_5178_, 0, v_x_5173_);
                    v___x_5181_ = v___x_5178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5185_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_x_5173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 1, v_x_5172_);
                    v___x_5181_ = v_reuseFailAlloc_5185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5182_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_5175_);
                v___x_5183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5183_, 0, v___x_5181_);
                leanh::lean_ctor_set(v___x_5183_, 1, v___x_5182_);
                v_x_5173_ = v___x_5183_;
                v_x_5174_ = v_tail_5176_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(
    mut v_x_5187_: *mut leanh::LeanObject,
    mut v_x_5188_: *mut leanh::LeanObject,
    mut v_x_5189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5194_: u8 = 0;
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5189_) == 0 {
                    leanh::lean_dec(v_x_5187_);
                    return v_x_5188_;
                } else {
                    v_head_5190_ = leanh::lean_ctor_get(v_x_5189_, 0);
                    v_tail_5191_ = leanh::lean_ctor_get(v_x_5189_, 1);
                    v_isSharedCheck_5201_ = (!leanh::lean_is_exclusive(v_x_5189_)) as u8;
                    if v_isSharedCheck_5201_ == 0 {
                        v___x_5193_ = v_x_5189_;
                        v_isShared_5194_ = v_isSharedCheck_5201_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5191_);
                        leanh::lean_inc(v_head_5190_);
                        leanh::lean_dec(v_x_5189_);
                        v___x_5193_ = leanh::lean_box(0);
                        v_isShared_5194_ = v_isSharedCheck_5201_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_5187_);
                if v_isShared_5194_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5193_, 5);
                    leanh::lean_ctor_set(v___x_5193_, 1, v_x_5187_);
                    leanh::lean_ctor_set(v___x_5193_, 0, v_x_5188_);
                    v___x_5196_ = v___x_5193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_x_5188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 1, v_x_5187_);
                    v___x_5196_ = v_reuseFailAlloc_5200_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5197_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_5190_);
                v___x_5198_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5198_, 0, v___x_5196_);
                leanh::lean_ctor_set(v___x_5198_, 1, v___x_5197_);
                v___x_5199_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_5187_, v___x_5198_, v_tail_5191_);
                return v___x_5199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(
    mut v_x_5202_: *mut leanh::LeanObject,
    mut v_x_5203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5202_) == 0 {
        let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5203_);
        v___x_5204_ = leanh::lean_box(0);
        return v___x_5204_;
    } else {
        let mut v_tail_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_5205_ = leanh::lean_ctor_get(v_x_5202_, 1);
        if leanh::lean_obj_tag(v_tail_5205_) == 0 {
            let mut v_head_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_5203_);
            v_head_5206_ = leanh::lean_ctor_get(v_x_5202_, 0);
            leanh::lean_inc(v_head_5206_);
            leanh::lean_dec_ref_known(v_x_5202_, 2);
            v___x_5207_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_5206_);
            return v___x_5207_;
        } else {
            let mut v_head_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_5205_);
            v_head_5208_ = leanh::lean_ctor_get(v_x_5202_, 0);
            leanh::lean_inc(v_head_5208_);
            leanh::lean_dec_ref_known(v_x_5202_, 2);
            v___x_5209_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_5208_);
            v___x_5210_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_5203_, v___x_5209_, v_tail_5205_);
            return v___x_5210_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(
    mut v_xs_5211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: u8 = 0;
    v___x_5212_ = lean_array_get_size(v_xs_5211_);
    v___x_5213_ = leanh::lean_unsigned_to_nat(0);
    v___x_5214_ = lean_nat_dec_eq(v___x_5212_, v___x_5213_);
    if v___x_5214_ == 0 {
        let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5215_ = lean_array_to_list(v_xs_5211_);
        v___x_5216_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1;
        v___x_5217_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_5215_, v___x_5216_);
        v___x_5218_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once
            ),
            _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3,
        );
        v___x_5219_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4;
        v___x_5220_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5220_, 0, v___x_5219_);
        leanh::lean_ctor_set(v___x_5220_, 1, v___x_5217_);
        v___x_5221_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5;
        v___x_5222_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5222_, 0, v___x_5220_);
        leanh::lean_ctor_set(v___x_5222_, 1, v___x_5221_);
        v___x_5223_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5223_, 0, v___x_5218_);
        leanh::lean_ctor_set(v___x_5223_, 1, v___x_5222_);
        v___x_5224_ = l_Std_Format_fill(v___x_5223_);
        return v___x_5224_;
    } else {
        let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_5211_);
        v___x_5225_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7;
        return v___x_5225_;
    }
}
pub unsafe fn l_Std_Http_URI_instReprQuery___lam__0(
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5228_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_5226_);
    return v___x_5228_;
}
pub unsafe fn l_Std_Http_URI_instReprQuery___lam__0___boxed(
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_5229_, v___y_5230_);
    leanh::lean_dec(v___y_5230_);
    return v_res_5231_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(
    mut v_x_5234_: *mut leanh::LeanObject,
    mut v_x_5235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5236_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_5234_);
    return v___x_5236_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(
    mut v_x_5237_: *mut leanh::LeanObject,
    mut v_x_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5239_ =
        l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(
            v_x_5237_, v_x_5238_,
        );
    leanh::lean_dec(v_x_5238_);
    return v_res_5239_;
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___aux__1___lam__0(
    mut v___f_5244_: *mut leanh::LeanObject,
    mut v_x_5245_: *mut leanh::LeanObject,
    mut v_x_5246_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    v_fst_5247_ = leanh::lean_ctor_get(v_x_5245_, 0);
    leanh::lean_inc(v_fst_5247_);
    v_snd_5248_ = leanh::lean_ctor_get(v_x_5245_, 1);
    leanh::lean_inc(v_snd_5248_);
    leanh::lean_dec_ref(v_x_5245_);
    v_fst_5249_ = leanh::lean_ctor_get(v_x_5246_, 0);
    leanh::lean_inc(v_fst_5249_);
    v_snd_5250_ = leanh::lean_ctor_get(v_x_5246_, 1);
    leanh::lean_inc(v_snd_5250_);
    leanh::lean_dec_ref(v_x_5246_);
    v___x_5251_ = lean_sarray_dec_eq(v_fst_5247_, v_fst_5249_);
    leanh::lean_dec(v_fst_5249_);
    leanh::lean_dec(v_fst_5247_);
    if v___x_5251_ == 0 {
        leanh::lean_dec(v_snd_5250_);
        leanh::lean_dec(v_snd_5248_);
        leanh::lean_dec_ref(v___f_5244_);
        return v___x_5251_;
    } else {
        let mut v___x_5252_: u8 = 0;
        v___x_5252_ = l_Option_instBEq_beq___redArg(v___f_5244_, v_snd_5248_, v_snd_5250_);
        return v___x_5252_;
    }
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(
    mut v___f_5253_: *mut leanh::LeanObject,
    mut v_x_5254_: *mut leanh::LeanObject,
    mut v_x_5255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5256_: u8 = 0;
    let mut v_r_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_5253_, v_x_5254_, v_x_5255_);
    v_r_5257_ = leanh::lean_box((v_res_5256_) as usize);
    return v_r_5257_;
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___aux__1(
    mut v_xs_5261_: *mut leanh::LeanObject,
    mut v_ys_5262_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    v___x_5263_ = lean_array_get_size(v_xs_5261_);
    v___x_5264_ = lean_array_get_size(v_ys_5262_);
    v___x_5265_ = lean_nat_dec_eq(v___x_5263_, v___x_5264_);
    if v___x_5265_ == 0 {
        return v___x_5265_;
    } else {
        let mut v___f_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5267_: u8 = 0;
        v___f_5266_ = l_Std_Http_URI_instBEqQuery___aux__1___closed__1;
        v___x_5267_ = l_Array_isEqvAux___redArg(v_xs_5261_, v_ys_5262_, v___f_5266_, v___x_5263_);
        return v___x_5267_;
    }
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___aux__1___boxed(
    mut v_xs_5268_: *mut leanh::LeanObject,
    mut v_ys_5269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5270_: u8 = 0;
    let mut v_r_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_5268_, v_ys_5269_);
    leanh::lean_dec_ref(v_ys_5269_);
    leanh::lean_dec_ref(v_xs_5268_);
    v_r_5271_ = leanh::lean_box((v_res_5270_) as usize);
    return v_r_5271_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(
    mut v_x_5272_: *mut leanh::LeanObject,
    mut v_x_5273_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5272_) == 0 {
        if leanh::lean_obj_tag(v_x_5273_) == 0 {
            let mut v___x_5274_: u8 = 0;
            v___x_5274_ = 1;
            return v___x_5274_;
        } else {
            let mut v___x_5275_: u8 = 0;
            v___x_5275_ = 0;
            return v___x_5275_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_5273_) == 0 {
            let mut v___x_5276_: u8 = 0;
            v___x_5276_ = 0;
            return v___x_5276_;
        } else {
            let mut v_val_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5279_: u8 = 0;
            v_val_5277_ = leanh::lean_ctor_get(v_x_5272_, 0);
            v_val_5278_ = leanh::lean_ctor_get(v_x_5273_, 0);
            v___x_5279_ = lean_sarray_dec_eq(v_val_5277_, v_val_5278_);
            return v___x_5279_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(
    mut v_x_5280_: *mut leanh::LeanObject,
    mut v_x_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5282_: u8 = 0;
    let mut v_r_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5282_ =
        l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_5280_, v_x_5281_);
    leanh::lean_dec(v_x_5281_);
    leanh::lean_dec(v_x_5280_);
    v_r_5283_ = leanh::lean_box((v_res_5282_) as usize);
    return v_r_5283_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(
    mut v_xs_5284_: *mut leanh::LeanObject,
    mut v_ys_5285_: *mut leanh::LeanObject,
    mut v_x_5286_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5288_: u8 = 0;
    let mut v_one_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5292_: u8 = 0;
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: u8 = 0;
    let mut v___x_5301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5287_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5288_ = lean_nat_dec_eq(v_x_5286_, v_zero_5287_);
                if v_isZero_5288_ == 1 {
                    leanh::lean_dec(v_x_5286_);
                    return v_isZero_5288_;
                } else {
                    v_one_5289_ = leanh::lean_unsigned_to_nat(1);
                    v_n_5290_ = lean_nat_sub(v_x_5286_, v_one_5289_);
                    leanh::lean_dec(v_x_5286_);
                    v___x_5294_ = lean_array_fget_borrowed(v_xs_5284_, v_n_5290_);
                    v_fst_5295_ = leanh::lean_ctor_get(v___x_5294_, 0);
                    v_snd_5296_ = leanh::lean_ctor_get(v___x_5294_, 1);
                    v___x_5297_ = lean_array_fget_borrowed(v_ys_5285_, v_n_5290_);
                    v_fst_5298_ = leanh::lean_ctor_get(v___x_5297_, 0);
                    v_snd_5299_ = leanh::lean_ctor_get(v___x_5297_, 1);
                    v___x_5300_ = lean_sarray_dec_eq(v_fst_5295_, v_fst_5298_);
                    if v___x_5300_ == 0 {
                        v___y_5292_ = v___x_5300_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5301_ =
                            l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(
                                v_snd_5296_,
                                v_snd_5299_,
                            );
                        v___y_5292_ = v___x_5301_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5292_ == 0 {
                    leanh::lean_dec(v_n_5290_);
                    return v___y_5292_;
                } else {
                    v_x_5286_ = v_n_5290_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(
    mut v_xs_5302_: *mut leanh::LeanObject,
    mut v_ys_5303_: *mut leanh::LeanObject,
    mut v_x_5304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5305_: u8 = 0;
    let mut v_r_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5305_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(
        v_xs_5302_, v_ys_5303_, v_x_5304_,
    );
    leanh::lean_dec_ref(v_ys_5303_);
    leanh::lean_dec_ref(v_xs_5302_);
    v_r_5306_ = leanh::lean_box((v_res_5305_) as usize);
    return v_r_5306_;
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___lam__0(
    mut v___y_5307_: *mut leanh::LeanObject,
    mut v___y_5308_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: u8 = 0;
    v___x_5309_ = lean_array_get_size(v___y_5307_);
    v___x_5310_ = lean_array_get_size(v___y_5308_);
    v___x_5311_ = lean_nat_dec_eq(v___x_5309_, v___x_5310_);
    if v___x_5311_ == 0 {
        return v___x_5311_;
    } else {
        let mut v___x_5312_: u8 = 0;
        v___x_5312_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(
            v___y_5307_,
            v___y_5308_,
            v___x_5309_,
        );
        return v___x_5312_;
    }
}
pub unsafe fn l_Std_Http_URI_instBEqQuery___lam__0___boxed(
    mut v___y_5313_: *mut leanh::LeanObject,
    mut v___y_5314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5315_: u8 = 0;
    let mut v_r_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_5313_, v___y_5314_);
    leanh::lean_dec_ref(v___y_5314_);
    leanh::lean_dec_ref(v___y_5313_);
    v_r_5316_ = leanh::lean_box((v_res_5315_) as usize);
    return v_r_5316_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(
    mut v_xs_5319_: *mut leanh::LeanObject,
    mut v_ys_5320_: *mut leanh::LeanObject,
    mut v_hsz_5321_: *mut leanh::LeanObject,
    mut v_x_5322_: *mut leanh::LeanObject,
    mut v_x_5323_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5324_: u8 = 0;
    v___x_5324_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(
        v_xs_5319_, v_ys_5320_, v_x_5322_,
    );
    return v___x_5324_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(
    mut v_xs_5325_: *mut leanh::LeanObject,
    mut v_ys_5326_: *mut leanh::LeanObject,
    mut v_hsz_5327_: *mut leanh::LeanObject,
    mut v_x_5328_: *mut leanh::LeanObject,
    mut v_x_5329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5330_: u8 = 0;
    let mut v_r_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5330_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(
        v_xs_5325_,
        v_ys_5326_,
        v_hsz_5327_,
        v_x_5328_,
        v_x_5329_,
    );
    leanh::lean_dec_ref(v_ys_5326_);
    leanh::lean_dec_ref(v_xs_5325_);
    v_r_5331_ = leanh::lean_box((v_res_5330_) as usize);
    return v_r_5331_;
}
pub unsafe fn l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(
    mut v_as_5332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5333_ = l_Std_Http_URI_instBEqQuery___aux__1___closed__0;
    v___x_5334_ = l_List_eraseDupsBy___redArg(v___f_5333_, v_as_5332_);
    return v___x_5334_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(
    mut v_sz_5335_: usize,
    mut v_i_5336_: usize,
    mut v_bs_5337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5338_: u8 = 0;
    let mut v_v_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: usize = 0;
    let mut v___x_5344_: usize = 0;
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5338_ = lean_usize_dec_lt(v_i_5336_, v_sz_5335_);
                if v___x_5338_ == 0 {
                    return v_bs_5337_;
                } else {
                    v_v_5339_ = lean_array_uget_borrowed(v_bs_5337_, v_i_5336_);
                    v_fst_5340_ = leanh::lean_ctor_get(v_v_5339_, 0);
                    leanh::lean_inc(v_fst_5340_);
                    v___x_5341_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5342_ = lean_array_uset(v_bs_5337_, v_i_5336_, v___x_5341_);
                    v___x_5343_ = 1usize;
                    v___x_5344_ = lean_usize_add(v_i_5336_, v___x_5343_);
                    v___x_5345_ = lean_array_uset(v_bs_x27_5342_, v_i_5336_, v_fst_5340_);
                    v_i_5336_ = v___x_5344_;
                    v_bs_5337_ = v___x_5345_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(
    mut v_sz_5347_: *mut leanh::LeanObject,
    mut v_i_5348_: *mut leanh::LeanObject,
    mut v_bs_5349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5350_: usize = 0;
    let mut v_i_boxed_5351_: usize = 0;
    let mut v_res_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5350_ = leanh::lean_unbox_usize(v_sz_5347_);
    leanh::lean_dec(v_sz_5347_);
    v_i_boxed_5351_ = leanh::lean_unbox_usize(v_i_5348_);
    leanh::lean_dec(v_i_5348_);
    v_res_5352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_5350_, v_i_boxed_5351_, v_bs_5349_);
    return v_res_5352_;
}
pub unsafe fn l_Std_Http_URI_Query_names(
    mut v_query_5353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_5354_: usize = 0;
    let mut v___x_5355_: usize = 0;
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_5354_ = lean_array_size(v_query_5353_);
    v___x_5355_ = 0usize;
    v___x_5356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_5354_, v___x_5355_, v_query_5353_);
    v___x_5357_ = lean_array_to_list(v___x_5356_);
    v___x_5358_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_5357_);
    v___x_5359_ = lean_array_mk(v___x_5358_);
    return v___x_5359_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(
    mut v_sz_5360_: usize,
    mut v_i_5361_: usize,
    mut v_bs_5362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5363_: u8 = 0;
    let mut v_v_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: usize = 0;
    let mut v___x_5369_: usize = 0;
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5363_ = lean_usize_dec_lt(v_i_5361_, v_sz_5360_);
                if v___x_5363_ == 0 {
                    return v_bs_5362_;
                } else {
                    v_v_5364_ = lean_array_uget_borrowed(v_bs_5362_, v_i_5361_);
                    v_snd_5365_ = leanh::lean_ctor_get(v_v_5364_, 1);
                    leanh::lean_inc(v_snd_5365_);
                    v___x_5366_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5367_ = lean_array_uset(v_bs_5362_, v_i_5361_, v___x_5366_);
                    v___x_5368_ = 1usize;
                    v___x_5369_ = lean_usize_add(v_i_5361_, v___x_5368_);
                    v___x_5370_ = lean_array_uset(v_bs_x27_5367_, v_i_5361_, v_snd_5365_);
                    v_i_5361_ = v___x_5369_;
                    v_bs_5362_ = v___x_5370_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(
    mut v_sz_5372_: *mut leanh::LeanObject,
    mut v_i_5373_: *mut leanh::LeanObject,
    mut v_bs_5374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5375_: usize = 0;
    let mut v_i_boxed_5376_: usize = 0;
    let mut v_res_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5375_ = leanh::lean_unbox_usize(v_sz_5372_);
    leanh::lean_dec(v_sz_5372_);
    v_i_boxed_5376_ = leanh::lean_unbox_usize(v_i_5373_);
    leanh::lean_dec(v_i_5373_);
    v_res_5377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_5375_, v_i_boxed_5376_, v_bs_5374_);
    return v_res_5377_;
}
pub unsafe fn l_Std_Http_URI_Query_values(
    mut v_query_5378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_5379_: usize = 0;
    let mut v___x_5380_: usize = 0;
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_5379_ = lean_array_size(v_query_5378_);
    v___x_5380_ = 0usize;
    v___x_5381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_5379_, v___x_5380_, v_query_5378_);
    return v___x_5381_;
}
pub unsafe fn l_Std_Http_URI_Query_toArray(
    mut v_query_5382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_query_5382_);
    return v_query_5382_;
}
pub unsafe fn l_Std_Http_URI_Query_toArray___boxed(
    mut v_query_5383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5384_ = l_Std_Http_URI_Query_toArray(v_query_5383_);
    leanh::lean_dec_ref(v_query_5383_);
    return v_res_5384_;
}
pub unsafe fn l_Std_Http_URI_Query_formatQueryParam(
    mut v_key_5386_: *mut leanh::LeanObject,
    mut v_value_5387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_value_5387_) == 0 {
        let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5388_ = lean_string_from_utf8_unchecked(v_key_5386_);
        return v___x_5388_;
    } else {
        let mut v_val_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5389_ = leanh::lean_ctor_get(v_value_5387_, 0);
        leanh::lean_inc(v_val_5389_);
        leanh::lean_dec_ref_known(v_value_5387_, 1);
        v___x_5390_ = lean_string_from_utf8_unchecked(v_key_5386_);
        v___x_5391_ = l_Std_Http_URI_Query_formatQueryParam___closed__0;
        v___x_5392_ = lean_string_append(v___x_5390_, v___x_5391_);
        v___x_5393_ = lean_string_from_utf8_unchecked(v_val_5389_);
        v___x_5394_ = lean_string_append(v___x_5392_, v___x_5393_);
        leanh::lean_dec_ref(v___x_5393_);
        return v___x_5394_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(
    mut v_key_5398_: *mut leanh::LeanObject,
    mut v_as_5399_: *mut leanh::LeanObject,
    mut v_sz_5400_: usize,
    mut v_i_5401_: usize,
    mut v_b_5402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5403_: u8 = 0;
    let mut v_a_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: usize = 0;
    let mut v___x_5410_: usize = 0;
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5403_ = lean_usize_dec_lt(v_i_5401_, v_sz_5400_);
                if v___x_5403_ == 0 {
                    leanh::lean_inc_ref(v_b_5402_);
                    return v_b_5402_;
                } else {
                    v_a_5404_ = lean_array_uget_borrowed(v_as_5399_, v_i_5401_);
                    v_fst_5405_ = leanh::lean_ctor_get(v_a_5404_, 0);
                    v___x_5406_ = leanh::lean_box(0);
                    v___x_5407_ = lean_sarray_dec_eq(v_fst_5405_, v_key_5398_);
                    if v___x_5407_ == 0 {
                        v___x_5408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0;
                        v___x_5409_ = 1usize;
                        v___x_5410_ = lean_usize_add(v_i_5401_, v___x_5409_);
                        v_i_5401_ = v___x_5410_;
                        v_b_5402_ = v___x_5408_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5404_);
                        v___x_5412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5412_, 0, v_a_5404_);
                        v___x_5413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5413_, 0, v___x_5412_);
                        v___x_5414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5414_, 0, v___x_5413_);
                        leanh::lean_ctor_set(v___x_5414_, 1, v___x_5406_);
                        return v___x_5414_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(
    mut v_key_5415_: *mut leanh::LeanObject,
    mut v_as_5416_: *mut leanh::LeanObject,
    mut v_sz_5417_: *mut leanh::LeanObject,
    mut v_i_5418_: *mut leanh::LeanObject,
    mut v_b_5419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5420_: usize = 0;
    let mut v_i_boxed_5421_: usize = 0;
    let mut v_res_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5420_ = leanh::lean_unbox_usize(v_sz_5417_);
    leanh::lean_dec(v_sz_5417_);
    v_i_boxed_5421_ = leanh::lean_unbox_usize(v_i_5418_);
    leanh::lean_dec(v_i_5418_);
    v_res_5422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_5415_, v_as_5416_, v_sz_boxed_5420_, v_i_boxed_5421_, v_b_5419_);
    leanh::lean_dec_ref(v_b_5419_);
    leanh::lean_dec_ref(v_as_5416_);
    leanh::lean_dec_ref(v_key_5415_);
    return v_res_5422_;
}
pub unsafe fn l_Std_Http_URI_Query_findEncoded_x3f(
    mut v_query_5423_: *mut leanh::LeanObject,
    mut v_key_5424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5427_: usize = 0;
    let mut v___x_5428_: usize = 0;
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v_snd_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5425_ = leanh::lean_box(0);
                v___x_5426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0;
                v_sz_5427_ = lean_array_size(v_query_5423_);
                v___x_5428_ = 0usize;
                v___x_5429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_5424_, v_query_5423_, v_sz_5427_, v___x_5428_, v___x_5426_);
                v_fst_5430_ = leanh::lean_ctor_get(v___x_5429_, 0);
                leanh::lean_inc(v_fst_5430_);
                leanh::lean_dec_ref(v___x_5429_);
                if leanh::lean_obj_tag(v_fst_5430_) == 0 {
                    return v___x_5425_;
                } else {
                    v_val_5431_ = leanh::lean_ctor_get(v_fst_5430_, 0);
                    leanh::lean_inc(v_val_5431_);
                    leanh::lean_dec_ref_known(v_fst_5430_, 1);
                    if leanh::lean_obj_tag(v_val_5431_) == 0 {
                        return v___x_5425_;
                    } else {
                        v_val_5432_ = leanh::lean_ctor_get(v_val_5431_, 0);
                        v_isSharedCheck_5440_ =
                            (!leanh::lean_is_exclusive(v_val_5431_)) as u8;
                        if v_isSharedCheck_5440_ == 0 {
                            v___x_5434_ = v_val_5431_;
                            v_isShared_5435_ = v_isSharedCheck_5440_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5432_);
                            leanh::lean_dec(v_val_5431_);
                            v___x_5434_ = leanh::lean_box(0);
                            v_isShared_5435_ = v_isSharedCheck_5440_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_5436_ = leanh::lean_ctor_get(v_val_5432_, 1);
                leanh::lean_inc(v_snd_5436_);
                leanh::lean_dec(v_val_5432_);
                if v_isShared_5435_ == 0 {
                    leanh::lean_ctor_set(v___x_5434_, 0, v_snd_5436_);
                    v___x_5438_ = v___x_5434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_snd_5436_);
                    v___x_5438_ = v_reuseFailAlloc_5439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Query_findEncoded_x3f___boxed(
    mut v_query_5441_: *mut leanh::LeanObject,
    mut v_key_5442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5443_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_5441_, v_key_5442_);
    leanh::lean_dec_ref(v_key_5442_);
    leanh::lean_dec_ref(v_query_5441_);
    return v_res_5443_;
}
pub unsafe fn l_Std_Http_URI_Query_find_x3f(
    mut v_query_5444_: *mut leanh::LeanObject,
    mut v_key_5445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5446_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_5445_);
    v___x_5447_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_5444_, v___x_5446_);
    leanh::lean_dec_ref(v___x_5446_);
    return v___x_5447_;
}
pub unsafe fn l_Std_Http_URI_Query_find_x3f___boxed(
    mut v_query_5448_: *mut leanh::LeanObject,
    mut v_key_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5450_ = l_Std_Http_URI_Query_find_x3f(v_query_5448_, v_key_5449_);
    leanh::lean_dec_ref(v_key_5449_);
    leanh::lean_dec_ref(v_query_5448_);
    return v_res_5450_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(
    mut v_key_5451_: *mut leanh::LeanObject,
    mut v_as_5452_: *mut leanh::LeanObject,
    mut v_i_5453_: usize,
    mut v_stop_5454_: usize,
    mut v_b_5455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: usize = 0;
    let mut v___x_5459_: usize = 0;
    let mut v___x_5461_: u8 = 0;
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: u8 = 0;
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5461_ = lean_usize_dec_eq(v_i_5453_, v_stop_5454_);
                if v___x_5461_ == 0 {
                    v___x_5462_ = lean_array_uget_borrowed(v_as_5452_, v_i_5453_);
                    v_fst_5463_ = leanh::lean_ctor_get(v___x_5462_, 0);
                    v_snd_5464_ = leanh::lean_ctor_get(v___x_5462_, 1);
                    v___x_5465_ = lean_sarray_dec_eq(v_fst_5463_, v_key_5451_);
                    if v___x_5465_ == 0 {
                        v___y_5457_ = v_b_5455_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5464_);
                        v___x_5466_ = lean_array_push(v_b_5455_, v_snd_5464_);
                        v___y_5457_ = v___x_5466_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5455_;
                }
            }
            1 => {
                v___x_5458_ = 1usize;
                v___x_5459_ = lean_usize_add(v_i_5453_, v___x_5458_);
                v_i_5453_ = v___x_5459_;
                v_b_5455_ = v___y_5457_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(
    mut v_key_5467_: *mut leanh::LeanObject,
    mut v_as_5468_: *mut leanh::LeanObject,
    mut v_i_5469_: *mut leanh::LeanObject,
    mut v_stop_5470_: *mut leanh::LeanObject,
    mut v_b_5471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5472_: usize = 0;
    let mut v_stop_boxed_5473_: usize = 0;
    let mut v_res_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5472_ = leanh::lean_unbox_usize(v_i_5469_);
    leanh::lean_dec(v_i_5469_);
    v_stop_boxed_5473_ = leanh::lean_unbox_usize(v_stop_5470_);
    leanh::lean_dec(v_stop_5470_);
    v_res_5474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_5467_, v_as_5468_, v_i_boxed_5472_, v_stop_boxed_5473_, v_b_5471_);
    leanh::lean_dec_ref(v_as_5468_);
    leanh::lean_dec_ref(v_key_5467_);
    return v_res_5474_;
}
pub unsafe fn l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(
    mut v_key_5477_: *mut leanh::LeanObject,
    mut v_as_5478_: *mut leanh::LeanObject,
    mut v_start_5479_: *mut leanh::LeanObject,
    mut v_stop_5480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: u8 = 0;
    v___x_5481_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0;
    v___x_5482_ = lean_nat_dec_lt(v_start_5479_, v_stop_5480_);
    if v___x_5482_ == 0 {
        return v___x_5481_;
    } else {
        let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5484_: u8 = 0;
        v___x_5483_ = lean_array_get_size(v_as_5478_);
        v___x_5484_ = lean_nat_dec_le(v_stop_5480_, v___x_5483_);
        if v___x_5484_ == 0 {
            let mut v___x_5485_: u8 = 0;
            v___x_5485_ = lean_nat_dec_lt(v_start_5479_, v___x_5483_);
            if v___x_5485_ == 0 {
                return v___x_5481_;
            } else {
                let mut v___x_5486_: usize = 0;
                let mut v___x_5487_: usize = 0;
                let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5486_ = lean_usize_of_nat(v_start_5479_);
                v___x_5487_ = lean_usize_of_nat(v___x_5483_);
                v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_5477_, v_as_5478_, v___x_5486_, v___x_5487_, v___x_5481_);
                return v___x_5488_;
            }
        } else {
            let mut v___x_5489_: usize = 0;
            let mut v___x_5490_: usize = 0;
            let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5489_ = lean_usize_of_nat(v_start_5479_);
            v___x_5490_ = lean_usize_of_nat(v_stop_5480_);
            v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_5477_, v_as_5478_, v___x_5489_, v___x_5490_, v___x_5481_);
            return v___x_5491_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(
    mut v_key_5492_: *mut leanh::LeanObject,
    mut v_as_5493_: *mut leanh::LeanObject,
    mut v_start_5494_: *mut leanh::LeanObject,
    mut v_stop_5495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5496_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(
        v_key_5492_,
        v_as_5493_,
        v_start_5494_,
        v_stop_5495_,
    );
    leanh::lean_dec(v_stop_5495_);
    leanh::lean_dec(v_start_5494_);
    leanh::lean_dec_ref(v_as_5493_);
    leanh::lean_dec_ref(v_key_5492_);
    return v_res_5496_;
}
pub unsafe fn l_Std_Http_URI_Query_findAllEncoded(
    mut v_query_5497_: *mut leanh::LeanObject,
    mut v_key_5498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = leanh::lean_unsigned_to_nat(0);
    v___x_5500_ = lean_array_get_size(v_query_5497_);
    v___x_5501_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(
        v_key_5498_,
        v_query_5497_,
        v___x_5499_,
        v___x_5500_,
    );
    return v___x_5501_;
}
pub unsafe fn l_Std_Http_URI_Query_findAllEncoded___boxed(
    mut v_query_5502_: *mut leanh::LeanObject,
    mut v_key_5503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5504_ = l_Std_Http_URI_Query_findAllEncoded(v_query_5502_, v_key_5503_);
    leanh::lean_dec_ref(v_key_5503_);
    leanh::lean_dec_ref(v_query_5502_);
    return v_res_5504_;
}
pub unsafe fn l_Std_Http_URI_Query_findAll(
    mut v_query_5505_: *mut leanh::LeanObject,
    mut v_key_5506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5507_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_5506_);
    v___x_5508_ = l_Std_Http_URI_Query_findAllEncoded(v_query_5505_, v___x_5507_);
    leanh::lean_dec_ref(v___x_5507_);
    return v___x_5508_;
}
pub unsafe fn l_Std_Http_URI_Query_findAll___boxed(
    mut v_query_5509_: *mut leanh::LeanObject,
    mut v_key_5510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5511_ = l_Std_Http_URI_Query_findAll(v_query_5509_, v_key_5510_);
    leanh::lean_dec_ref(v_key_5510_);
    leanh::lean_dec_ref(v_query_5509_);
    return v_res_5511_;
}
pub unsafe fn l_Std_Http_URI_Query_insert(
    mut v_query_5512_: *mut leanh::LeanObject,
    mut v_key_5513_: *mut leanh::LeanObject,
    mut v_value_5514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_encodedKey_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedValue_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_encodedKey_5515_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_5513_);
    v_encodedValue_5516_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_5514_);
    v___x_5517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5517_, 0, v_encodedValue_5516_);
    v___x_5518_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5518_, 0, v_encodedKey_5515_);
    leanh::lean_ctor_set(v___x_5518_, 1, v___x_5517_);
    v___x_5519_ = lean_array_push(v_query_5512_, v___x_5518_);
    return v___x_5519_;
}
pub unsafe fn l_Std_Http_URI_Query_insert___boxed(
    mut v_query_5520_: *mut leanh::LeanObject,
    mut v_key_5521_: *mut leanh::LeanObject,
    mut v_value_5522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5523_ = l_Std_Http_URI_Query_insert(v_query_5520_, v_key_5521_, v_value_5522_);
    leanh::lean_dec_ref(v_value_5522_);
    leanh::lean_dec_ref(v_key_5521_);
    return v_res_5523_;
}
pub unsafe fn l_Std_Http_URI_Query_insertEncoded(
    mut v_query_5524_: *mut leanh::LeanObject,
    mut v_key_5525_: *mut leanh::LeanObject,
    mut v_value_5526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5527_, 0, v_key_5525_);
    leanh::lean_ctor_set(v___x_5527_, 1, v_value_5526_);
    v___x_5528_ = lean_array_push(v_query_5524_, v___x_5527_);
    return v___x_5528_;
}
pub unsafe fn l_Std_Http_URI_Query_ofList(
    mut v_pairs_5532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5533_ = lean_array_mk(v_pairs_5532_);
    return v___x_5533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(
    mut v_key_5534_: *mut leanh::LeanObject,
    mut v_as_5535_: *mut leanh::LeanObject,
    mut v_i_5536_: usize,
    mut v_stop_5537_: usize,
) -> u8 {
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: u8 = 0;
    let mut v___x_5542_: usize = 0;
    let mut v___x_5543_: usize = 0;
    let mut v___x_5545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5538_ = lean_usize_dec_eq(v_i_5536_, v_stop_5537_);
                if v___x_5538_ == 0 {
                    v___x_5539_ = lean_array_uget_borrowed(v_as_5535_, v_i_5536_);
                    v_fst_5540_ = leanh::lean_ctor_get(v___x_5539_, 0);
                    v___x_5541_ = lean_sarray_dec_eq(v_fst_5540_, v_key_5534_);
                    if v___x_5541_ == 0 {
                        v___x_5542_ = 1usize;
                        v___x_5543_ = lean_usize_add(v_i_5536_, v___x_5542_);
                        v_i_5536_ = v___x_5543_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5541_;
                    }
                } else {
                    v___x_5545_ = 0;
                    return v___x_5545_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(
    mut v_key_5546_: *mut leanh::LeanObject,
    mut v_as_5547_: *mut leanh::LeanObject,
    mut v_i_5548_: *mut leanh::LeanObject,
    mut v_stop_5549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5550_: usize = 0;
    let mut v_stop_boxed_5551_: usize = 0;
    let mut v_res_5552_: u8 = 0;
    let mut v_r_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5550_ = leanh::lean_unbox_usize(v_i_5548_);
    leanh::lean_dec(v_i_5548_);
    v_stop_boxed_5551_ = leanh::lean_unbox_usize(v_stop_5549_);
    leanh::lean_dec(v_stop_5549_);
    v_res_5552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_5546_, v_as_5547_, v_i_boxed_5550_, v_stop_boxed_5551_);
    leanh::lean_dec_ref(v_as_5547_);
    leanh::lean_dec_ref(v_key_5546_);
    v_r_5553_ = leanh::lean_box((v_res_5552_) as usize);
    return v_r_5553_;
}
pub unsafe fn l_Std_Http_URI_Query_containsEncoded(
    mut v_query_5554_: *mut leanh::LeanObject,
    mut v_key_5555_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: u8 = 0;
    v___x_5556_ = leanh::lean_unsigned_to_nat(0);
    v___x_5557_ = lean_array_get_size(v_query_5554_);
    v___x_5558_ = lean_nat_dec_lt(v___x_5556_, v___x_5557_);
    if v___x_5558_ == 0 {
        return v___x_5558_;
    } else {
        if v___x_5558_ == 0 {
            return v___x_5558_;
        } else {
            let mut v___x_5559_: usize = 0;
            let mut v___x_5560_: usize = 0;
            let mut v___x_5561_: u8 = 0;
            v___x_5559_ = 0usize;
            v___x_5560_ = lean_usize_of_nat(v___x_5557_);
            v___x_5561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_5555_, v_query_5554_, v___x_5559_, v___x_5560_);
            return v___x_5561_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_Query_containsEncoded___boxed(
    mut v_query_5562_: *mut leanh::LeanObject,
    mut v_key_5563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5564_: u8 = 0;
    let mut v_r_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5564_ = l_Std_Http_URI_Query_containsEncoded(v_query_5562_, v_key_5563_);
    leanh::lean_dec_ref(v_key_5563_);
    leanh::lean_dec_ref(v_query_5562_);
    v_r_5565_ = leanh::lean_box((v_res_5564_) as usize);
    return v_r_5565_;
}
pub unsafe fn l_Std_Http_URI_Query_contains(
    mut v_query_5566_: *mut leanh::LeanObject,
    mut v_key_5567_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: u8 = 0;
    v___x_5568_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_5567_);
    v___x_5569_ = l_Std_Http_URI_Query_containsEncoded(v_query_5566_, v___x_5568_);
    leanh::lean_dec_ref(v___x_5568_);
    return v___x_5569_;
}
pub unsafe fn l_Std_Http_URI_Query_contains___boxed(
    mut v_query_5570_: *mut leanh::LeanObject,
    mut v_key_5571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5572_: u8 = 0;
    let mut v_r_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5572_ = l_Std_Http_URI_Query_contains(v_query_5570_, v_key_5571_);
    leanh::lean_dec_ref(v_key_5571_);
    leanh::lean_dec_ref(v_query_5570_);
    v_r_5573_ = leanh::lean_box((v_res_5572_) as usize);
    return v_r_5573_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(
    mut v_key_5574_: *mut leanh::LeanObject,
    mut v_as_5575_: *mut leanh::LeanObject,
    mut v_i_5576_: usize,
    mut v_stop_5577_: usize,
    mut v_b_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: usize = 0;
    let mut v___x_5582_: usize = 0;
    let mut v___x_5584_: u8 = 0;
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5584_ = lean_usize_dec_eq(v_i_5576_, v_stop_5577_);
                if v___x_5584_ == 0 {
                    v___x_5585_ = lean_array_uget_borrowed(v_as_5575_, v_i_5576_);
                    v_fst_5588_ = leanh::lean_ctor_get(v___x_5585_, 0);
                    v___x_5589_ = lean_sarray_dec_eq(v_fst_5588_, v_key_5574_);
                    if v___x_5589_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        if v___x_5584_ == 0 {
                            v___y_5580_ = v_b_5578_;
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    return v_b_5578_;
                }
            }
            1 => {
                v___x_5581_ = 1usize;
                v___x_5582_ = lean_usize_add(v_i_5576_, v___x_5581_);
                v_i_5576_ = v___x_5582_;
                v_b_5578_ = v___y_5580_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_5585_);
                v___x_5587_ = lean_array_push(v_b_5578_, v___x_5585_);
                v___y_5580_ = v___x_5587_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(
    mut v_key_5590_: *mut leanh::LeanObject,
    mut v_as_5591_: *mut leanh::LeanObject,
    mut v_i_5592_: *mut leanh::LeanObject,
    mut v_stop_5593_: *mut leanh::LeanObject,
    mut v_b_5594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5595_: usize = 0;
    let mut v_stop_boxed_5596_: usize = 0;
    let mut v_res_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5595_ = leanh::lean_unbox_usize(v_i_5592_);
    leanh::lean_dec(v_i_5592_);
    v_stop_boxed_5596_ = leanh::lean_unbox_usize(v_stop_5593_);
    leanh::lean_dec(v_stop_5593_);
    v_res_5597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_5590_, v_as_5591_, v_i_boxed_5595_, v_stop_boxed_5596_, v_b_5594_);
    leanh::lean_dec_ref(v_as_5591_);
    leanh::lean_dec_ref(v_key_5590_);
    return v_res_5597_;
}
pub unsafe fn l_Std_Http_URI_Query_eraseEncoded(
    mut v_query_5598_: *mut leanh::LeanObject,
    mut v_key_5599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    v___x_5600_ = leanh::lean_unsigned_to_nat(0);
    v___x_5601_ = lean_array_get_size(v_query_5598_);
    v___x_5602_ = l_Std_Http_URI_Query_empty___closed__0;
    v___x_5603_ = lean_nat_dec_lt(v___x_5600_, v___x_5601_);
    if v___x_5603_ == 0 {
        return v___x_5602_;
    } else {
        let mut v___x_5604_: u8 = 0;
        v___x_5604_ = lean_nat_dec_le(v___x_5601_, v___x_5601_);
        if v___x_5604_ == 0 {
            if v___x_5603_ == 0 {
                return v___x_5602_;
            } else {
                let mut v___x_5605_: usize = 0;
                let mut v___x_5606_: usize = 0;
                let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5605_ = 0usize;
                v___x_5606_ = lean_usize_of_nat(v___x_5601_);
                v___x_5607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_5599_, v_query_5598_, v___x_5605_, v___x_5606_, v___x_5602_);
                return v___x_5607_;
            }
        } else {
            let mut v___x_5608_: usize = 0;
            let mut v___x_5609_: usize = 0;
            let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5608_ = 0usize;
            v___x_5609_ = lean_usize_of_nat(v___x_5601_);
            v___x_5610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_5599_, v_query_5598_, v___x_5608_, v___x_5609_, v___x_5602_);
            return v___x_5610_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_Query_eraseEncoded___boxed(
    mut v_query_5611_: *mut leanh::LeanObject,
    mut v_key_5612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5613_ = l_Std_Http_URI_Query_eraseEncoded(v_query_5611_, v_key_5612_);
    leanh::lean_dec_ref(v_key_5612_);
    leanh::lean_dec_ref(v_query_5611_);
    return v_res_5613_;
}
pub unsafe fn l_Std_Http_URI_Query_erase(
    mut v_query_5614_: *mut leanh::LeanObject,
    mut v_key_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5616_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_5615_);
    v___x_5617_ = l_Std_Http_URI_Query_eraseEncoded(v_query_5614_, v___x_5616_);
    leanh::lean_dec_ref(v___x_5616_);
    return v___x_5617_;
}
pub unsafe fn l_Std_Http_URI_Query_erase___boxed(
    mut v_query_5618_: *mut leanh::LeanObject,
    mut v_key_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5620_ = l_Std_Http_URI_Query_erase(v_query_5618_, v_key_5619_);
    leanh::lean_dec_ref(v_key_5619_);
    leanh::lean_dec_ref(v_query_5618_);
    return v_res_5620_;
}
pub unsafe fn l_Std_Http_URI_Query_get(
    mut v_query_5623_: *mut leanh::LeanObject,
    mut v_key_5624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5625_ = l_Std_Http_URI_Query_find_x3f(v_query_5623_, v_key_5624_);
    if leanh::lean_obj_tag(v___x_5625_) == 0 {
        let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5626_ = leanh::lean_box(0);
        return v___x_5626_;
    } else {
        let mut v_val_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5627_ = leanh::lean_ctor_get(v___x_5625_, 0);
        leanh::lean_inc(v_val_5627_);
        leanh::lean_dec_ref_known(v___x_5625_, 1);
        if leanh::lean_obj_tag(v_val_5627_) == 0 {
            let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5628_ = l_Std_Http_URI_Query_get___closed__0;
            return v___x_5628_;
        } else {
            let mut v_val_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_5629_ = leanh::lean_ctor_get(v_val_5627_, 0);
            leanh::lean_inc(v_val_5629_);
            leanh::lean_dec_ref_known(v_val_5627_, 1);
            v___x_5630_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_5629_);
            leanh::lean_dec(v_val_5629_);
            return v___x_5630_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_Query_get___boxed(
    mut v_query_5631_: *mut leanh::LeanObject,
    mut v_key_5632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5633_ = l_Std_Http_URI_Query_get(v_query_5631_, v_key_5632_);
    leanh::lean_dec_ref(v_key_5632_);
    leanh::lean_dec_ref(v_query_5631_);
    return v_res_5633_;
}
pub unsafe fn l_Std_Http_URI_Query_getD(
    mut v_query_5634_: *mut leanh::LeanObject,
    mut v_key_5635_: *mut leanh::LeanObject,
    mut v_default_5636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5637_ = l_Std_Http_URI_Query_get(v_query_5634_, v_key_5635_);
    if leanh::lean_obj_tag(v___x_5637_) == 0 {
        leanh::lean_inc_ref(v_default_5636_);
        return v_default_5636_;
    } else {
        let mut v_val_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5638_ = leanh::lean_ctor_get(v___x_5637_, 0);
        leanh::lean_inc(v_val_5638_);
        leanh::lean_dec_ref_known(v___x_5637_, 1);
        return v_val_5638_;
    }
}
pub unsafe fn l_Std_Http_URI_Query_getD___boxed(
    mut v_query_5639_: *mut leanh::LeanObject,
    mut v_key_5640_: *mut leanh::LeanObject,
    mut v_default_5641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5642_ = l_Std_Http_URI_Query_getD(v_query_5639_, v_key_5640_, v_default_5641_);
    leanh::lean_dec_ref(v_default_5641_);
    leanh::lean_dec_ref(v_key_5640_);
    leanh::lean_dec_ref(v_query_5639_);
    return v_res_5642_;
}
pub unsafe fn l_Std_Http_URI_Query_set(
    mut v_query_5643_: *mut leanh::LeanObject,
    mut v_key_5644_: *mut leanh::LeanObject,
    mut v_value_5645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5646_ = l_Std_Http_URI_Query_erase(v_query_5643_, v_key_5644_);
    v___x_5647_ = l_Std_Http_URI_Query_insert(v___x_5646_, v_key_5644_, v_value_5645_);
    return v___x_5647_;
}
pub unsafe fn l_Std_Http_URI_Query_set___boxed(
    mut v_query_5648_: *mut leanh::LeanObject,
    mut v_key_5649_: *mut leanh::LeanObject,
    mut v_value_5650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5651_ = l_Std_Http_URI_Query_set(v_query_5648_, v_key_5649_, v_value_5650_);
    leanh::lean_dec_ref(v_value_5650_);
    leanh::lean_dec_ref(v_key_5649_);
    leanh::lean_dec_ref(v_query_5648_);
    return v_res_5651_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(
    mut v_sz_5652_: usize,
    mut v_i_5653_: usize,
    mut v_bs_5654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5655_: u8 = 0;
    let mut v_v_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: usize = 0;
    let mut v___x_5663_: usize = 0;
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5655_ = lean_usize_dec_lt(v_i_5653_, v_sz_5652_);
                if v___x_5655_ == 0 {
                    return v_bs_5654_;
                } else {
                    v_v_5656_ = lean_array_uget_borrowed(v_bs_5654_, v_i_5653_);
                    v_fst_5657_ = leanh::lean_ctor_get(v_v_5656_, 0);
                    leanh::lean_inc(v_fst_5657_);
                    v_snd_5658_ = leanh::lean_ctor_get(v_v_5656_, 1);
                    leanh::lean_inc(v_snd_5658_);
                    v___x_5659_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5660_ = lean_array_uset(v_bs_5654_, v_i_5653_, v___x_5659_);
                    v___x_5661_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_5657_, v_snd_5658_);
                    v___x_5662_ = 1usize;
                    v___x_5663_ = lean_usize_add(v_i_5653_, v___x_5662_);
                    v___x_5664_ = lean_array_uset(v_bs_x27_5660_, v_i_5653_, v___x_5661_);
                    v_i_5653_ = v___x_5663_;
                    v_bs_5654_ = v___x_5664_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(
    mut v_sz_5666_: *mut leanh::LeanObject,
    mut v_i_5667_: *mut leanh::LeanObject,
    mut v_bs_5668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5669_: usize = 0;
    let mut v_i_boxed_5670_: usize = 0;
    let mut v_res_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5669_ = leanh::lean_unbox_usize(v_sz_5666_);
    leanh::lean_dec(v_sz_5666_);
    v_i_boxed_5670_ = leanh::lean_unbox_usize(v_i_5667_);
    leanh::lean_dec(v_i_5667_);
    v_res_5671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_5669_, v_i_boxed_5670_, v_bs_5668_);
    return v_res_5671_;
}
pub unsafe fn l_Std_Http_URI_Query_toRawString(
    mut v_query_5673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_5674_: usize = 0;
    let mut v___x_5675_: usize = 0;
    let mut v_params_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_5674_ = lean_array_size(v_query_5673_);
    v___x_5675_ = 0usize;
    v_params_5676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_5674_, v___x_5675_, v_query_5673_);
    v___x_5677_ = l_Std_Http_URI_Query_toRawString___closed__0;
    v___x_5678_ = lean_array_to_list(v_params_5676_);
    v___x_5679_ = l_String_intercalate(v___x_5677_, v___x_5678_);
    return v___x_5679_;
}
pub unsafe fn l_Std_Http_URI_Query_instSingletonProdString___lam__0(
    mut v_x_5681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5682_ = leanh::lean_ctor_get(v_x_5681_, 0);
    v_snd_5683_ = leanh::lean_ctor_get(v_x_5681_, 1);
    v___x_5684_ = l_Std_Http_URI_Query_empty;
    v___x_5685_ = l_Std_Http_URI_Query_insert(v___x_5684_, v_fst_5682_, v_snd_5683_);
    return v___x_5685_;
}
pub unsafe fn l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(
    mut v_x_5686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_5686_);
    leanh::lean_dec_ref(v_x_5686_);
    return v_res_5687_;
}
pub unsafe fn l_Std_Http_URI_Query_instInsertProdString___lam__0(
    mut v_x_5690_: *mut leanh::LeanObject,
    mut v_q_5691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5692_ = leanh::lean_ctor_get(v_x_5690_, 0);
    v_snd_5693_ = leanh::lean_ctor_get(v_x_5690_, 1);
    v___x_5694_ = l_Std_Http_URI_Query_insert(v_q_5691_, v_fst_5692_, v_snd_5693_);
    return v___x_5694_;
}
pub unsafe fn l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(
    mut v_x_5695_: *mut leanh::LeanObject,
    mut v_q_5696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5697_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_5695_, v_q_5696_);
    leanh::lean_dec_ref(v_x_5695_);
    return v_res_5697_;
}
pub unsafe fn l_Std_Http_URI_Query_instToString___lam__0(
    mut v_x_5700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5701_ = leanh::lean_ctor_get(v_x_5700_, 0);
    leanh::lean_inc(v_fst_5701_);
    v_snd_5702_ = leanh::lean_ctor_get(v_x_5700_, 1);
    leanh::lean_inc(v_snd_5702_);
    leanh::lean_dec_ref(v_x_5700_);
    v___x_5703_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_5701_, v_snd_5702_);
    return v___x_5703_;
}
pub unsafe fn l_Std_Http_URI_Query_instToString___lam__1(
    mut v___f_5705_: *mut leanh::LeanObject,
    mut v_q_5706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: u8 = 0;
    v___x_5707_ = lean_array_get_size(v_q_5706_);
    v___x_5708_ = leanh::lean_unsigned_to_nat(0);
    v___x_5709_ = lean_nat_dec_eq(v___x_5707_, v___x_5708_);
    if v___x_5709_ == 0 {
        let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_encodedParams_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5710_ = lean_array_to_list(v_q_5706_);
        v___x_5711_ = leanh::lean_box(0);
        v_encodedParams_5712_ = l_List_mapTR_loop___redArg(v___f_5705_, v___x_5710_, v___x_5711_);
        v___x_5713_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
        v___x_5714_ = l_Std_Http_URI_Query_toRawString___closed__0;
        v___x_5715_ = l_String_intercalate(v___x_5714_, v_encodedParams_5712_);
        v___x_5716_ = lean_string_append(v___x_5713_, v___x_5715_);
        leanh::lean_dec_ref(v___x_5715_);
        return v___x_5716_;
    } else {
        let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_q_5706_);
        leanh::lean_dec_ref(v___f_5705_);
        v___x_5717_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
        return v___x_5717_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(
    mut v_x_5722_: *mut leanh::LeanObject,
    mut v_x_5723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5722_) == 0 {
        let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5724_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
        return v___x_5724_;
    } else {
        let mut v_val_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5725_ = leanh::lean_ctor_get(v_x_5722_, 0);
        leanh::lean_inc(v_val_5725_);
        leanh::lean_dec_ref_known(v_x_5722_, 1);
        v___x_5726_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
        v___x_5727_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_5725_);
        v___x_5728_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5728_, 0, v___x_5726_);
        leanh::lean_ctor_set(v___x_5728_, 1, v___x_5727_);
        v___x_5729_ = l_Repr_addAppParen(v___x_5728_, v_x_5723_);
        return v___x_5729_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(
    mut v_x_5730_: *mut leanh::LeanObject,
    mut v_x_5731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5732_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_5730_, v_x_5731_);
    leanh::lean_dec(v_x_5731_);
    return v_res_5732_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(
    mut v_x_5733_: *mut leanh::LeanObject,
    mut v_x_5734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5733_) == 0 {
                    v___x_5735_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
                    return v___x_5735_;
                } else {
                    v_val_5736_ = leanh::lean_ctor_get(v_x_5733_, 0);
                    v_isSharedCheck_5747_ = (!leanh::lean_is_exclusive(v_x_5733_)) as u8;
                    if v_isSharedCheck_5747_ == 0 {
                        v___x_5738_ = v_x_5733_;
                        v_isShared_5739_ = v_isSharedCheck_5747_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5736_);
                        leanh::lean_dec(v_x_5733_);
                        v___x_5738_ = leanh::lean_box(0);
                        v_isShared_5739_ = v_isSharedCheck_5747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5740_ =
                    l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
                v___x_5741_ = l_String_quote(v_val_5736_);
                if v_isShared_5739_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5738_, 3);
                    leanh::lean_ctor_set(v___x_5738_, 0, v___x_5741_);
                    v___x_5743_ = v___x_5738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5746_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5741_);
                    v___x_5743_ = v_reuseFailAlloc_5746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5744_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5744_, 0, v___x_5740_);
                leanh::lean_ctor_set(v___x_5744_, 1, v___x_5743_);
                v___x_5745_ = l_Repr_addAppParen(v___x_5744_, v_x_5734_);
                return v___x_5745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(
    mut v_x_5748_: *mut leanh::LeanObject,
    mut v_x_5749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5750_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_5748_, v_x_5749_);
    leanh::lean_dec(v_x_5749_);
    return v_res_5750_;
}
pub unsafe fn _init_l_Std_Http_instReprURI_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5760_ = leanh::lean_unsigned_to_nat(10);
    v___x_5761_ = lean_nat_to_int(v___x_5760_);
    return v___x_5761_;
}
pub unsafe fn _init_l_Std_Http_instReprURI_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = leanh::lean_unsigned_to_nat(13);
    v___x_5766_ = lean_nat_to_int(v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn _init_l_Std_Http_instReprURI_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5773_ = leanh::lean_unsigned_to_nat(9);
    v___x_5774_ = lean_nat_to_int(v___x_5773_);
    return v___x_5774_;
}
pub unsafe fn l_Std_Http_instReprURI_repr___redArg(
    mut v_x_5778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_scheme_5779_ = leanh::lean_ctor_get(v_x_5778_, 0);
    leanh::lean_inc_ref(v_scheme_5779_);
    v_authority_5780_ = leanh::lean_ctor_get(v_x_5778_, 1);
    leanh::lean_inc(v_authority_5780_);
    v_path_5781_ = leanh::lean_ctor_get(v_x_5778_, 2);
    leanh::lean_inc_ref(v_path_5781_);
    v_query_5782_ = leanh::lean_ctor_get(v_x_5778_, 3);
    leanh::lean_inc_ref(v_query_5782_);
    v_fragment_5783_ = leanh::lean_ctor_get(v_x_5778_, 4);
    leanh::lean_inc(v_fragment_5783_);
    leanh::lean_dec_ref(v_x_5778_);
    v___x_5784_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5;
    v___x_5785_ = l_Std_Http_instReprURI_repr___redArg___closed__3;
    v___x_5786_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__4_once),
        _init_l_Std_Http_instReprURI_repr___redArg___closed__4,
    );
    v___x_5787_ = l_String_quote(v_scheme_5779_);
    v___x_5788_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5788_, 0, v___x_5787_);
    v___x_5789_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5789_, 0, v___x_5786_);
    leanh::lean_ctor_set(v___x_5789_, 1, v___x_5788_);
    v___x_5790_ = 0;
    v___x_5791_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5791_, 0, v___x_5789_);
    leanh::lean_ctor_set_uint8(
        v___x_5791_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    v___x_5792_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5792_, 0, v___x_5785_);
    leanh::lean_ctor_set(v___x_5792_, 1, v___x_5791_);
    v___x_5793_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9;
    v___x_5794_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5794_, 0, v___x_5792_);
    leanh::lean_ctor_set(v___x_5794_, 1, v___x_5793_);
    v___x_5795_ = leanh::lean_box(1);
    v___x_5796_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5796_, 0, v___x_5794_);
    leanh::lean_ctor_set(v___x_5796_, 1, v___x_5795_);
    v___x_5797_ = l_Std_Http_instReprURI_repr___redArg___closed__6;
    v___x_5798_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5798_, 0, v___x_5796_);
    leanh::lean_ctor_set(v___x_5798_, 1, v___x_5797_);
    v___x_5799_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5799_, 0, v___x_5798_);
    leanh::lean_ctor_set(v___x_5799_, 1, v___x_5784_);
    v___x_5800_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__7_once),
        _init_l_Std_Http_instReprURI_repr___redArg___closed__7,
    );
    v___x_5801_ = leanh::lean_unsigned_to_nat(0);
    v___x_5802_ =
        l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_5780_, v___x_5801_);
    v___x_5803_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5803_, 0, v___x_5800_);
    leanh::lean_ctor_set(v___x_5803_, 1, v___x_5802_);
    v___x_5804_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5804_, 0, v___x_5803_);
    leanh::lean_ctor_set_uint8(
        v___x_5804_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    v___x_5805_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5805_, 0, v___x_5799_);
    leanh::lean_ctor_set(v___x_5805_, 1, v___x_5804_);
    v___x_5806_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5806_, 0, v___x_5805_);
    leanh::lean_ctor_set(v___x_5806_, 1, v___x_5793_);
    v___x_5807_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5807_, 0, v___x_5806_);
    leanh::lean_ctor_set(v___x_5807_, 1, v___x_5795_);
    v___x_5808_ = l_Std_Http_instReprURI_repr___redArg___closed__9;
    v___x_5809_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5809_, 0, v___x_5807_);
    leanh::lean_ctor_set(v___x_5809_, 1, v___x_5808_);
    v___x_5810_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5810_, 0, v___x_5809_);
    leanh::lean_ctor_set(v___x_5810_, 1, v___x_5784_);
    v___x_5811_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once),
        _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6,
    );
    v___x_5812_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_5781_);
    v___x_5813_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5813_, 0, v___x_5811_);
    leanh::lean_ctor_set(v___x_5813_, 1, v___x_5812_);
    v___x_5814_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5814_, 0, v___x_5813_);
    leanh::lean_ctor_set_uint8(
        v___x_5814_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    v___x_5815_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5815_, 0, v___x_5810_);
    leanh::lean_ctor_set(v___x_5815_, 1, v___x_5814_);
    v___x_5816_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5816_, 0, v___x_5815_);
    leanh::lean_ctor_set(v___x_5816_, 1, v___x_5793_);
    v___x_5817_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5817_, 0, v___x_5816_);
    leanh::lean_ctor_set(v___x_5817_, 1, v___x_5795_);
    v___x_5818_ = l_Std_Http_instReprURI_repr___redArg___closed__11;
    v___x_5819_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5819_, 0, v___x_5817_);
    leanh::lean_ctor_set(v___x_5819_, 1, v___x_5818_);
    v___x_5820_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5820_, 0, v___x_5819_);
    leanh::lean_ctor_set(v___x_5820_, 1, v___x_5784_);
    v___x_5821_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Std_Http_instReprURI_repr___redArg___closed__12_once),
        _init_l_Std_Http_instReprURI_repr___redArg___closed__12,
    );
    v___x_5822_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_query_5782_);
    v___x_5823_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5823_, 0, v___x_5821_);
    leanh::lean_ctor_set(v___x_5823_, 1, v___x_5822_);
    v___x_5824_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5824_, 0, v___x_5823_);
    leanh::lean_ctor_set_uint8(
        v___x_5824_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    v___x_5825_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5825_, 0, v___x_5820_);
    leanh::lean_ctor_set(v___x_5825_, 1, v___x_5824_);
    v___x_5826_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5826_, 0, v___x_5825_);
    leanh::lean_ctor_set(v___x_5826_, 1, v___x_5793_);
    v___x_5827_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5827_, 0, v___x_5826_);
    leanh::lean_ctor_set(v___x_5827_, 1, v___x_5795_);
    v___x_5828_ = l_Std_Http_instReprURI_repr___redArg___closed__14;
    v___x_5829_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5829_, 0, v___x_5827_);
    leanh::lean_ctor_set(v___x_5829_, 1, v___x_5828_);
    v___x_5830_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5830_, 0, v___x_5829_);
    leanh::lean_ctor_set(v___x_5830_, 1, v___x_5784_);
    v___x_5831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once),
        _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7,
    );
    v___x_5832_ =
        l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_fragment_5783_, v___x_5801_);
    v___x_5833_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5833_, 0, v___x_5831_);
    leanh::lean_ctor_set(v___x_5833_, 1, v___x_5832_);
    v___x_5834_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5834_, 0, v___x_5833_);
    leanh::lean_ctor_set_uint8(
        v___x_5834_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    v___x_5835_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5835_, 0, v___x_5830_);
    leanh::lean_ctor_set(v___x_5835_, 1, v___x_5834_);
    v___x_5836_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once),
        _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14,
    );
    v___x_5837_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15;
    v___x_5838_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5838_, 0, v___x_5837_);
    leanh::lean_ctor_set(v___x_5838_, 1, v___x_5835_);
    v___x_5839_ = l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16;
    v___x_5840_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5840_, 0, v___x_5838_);
    leanh::lean_ctor_set(v___x_5840_, 1, v___x_5839_);
    v___x_5841_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5841_, 0, v___x_5836_);
    leanh::lean_ctor_set(v___x_5841_, 1, v___x_5840_);
    v___x_5842_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_5842_, 0, v___x_5841_);
    leanh::lean_ctor_set_uint8(
        v___x_5842_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_5790_,
    );
    return v___x_5842_;
}
pub unsafe fn l_Std_Http_instReprURI_repr(
    mut v_x_5843_: *mut leanh::LeanObject,
    mut v_prec_5844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5845_ = l_Std_Http_instReprURI_repr___redArg(v_x_5843_);
    return v___x_5845_;
}
pub unsafe fn l_Std_Http_instReprURI_repr___boxed(
    mut v_x_5846_: *mut leanh::LeanObject,
    mut v_prec_5847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5848_ = l_Std_Http_instReprURI_repr(v_x_5846_, v_prec_5847_);
    leanh::lean_dec(v_prec_5847_);
    return v_res_5848_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(
    mut v_x_5858_: *mut leanh::LeanObject,
    mut v_x_5859_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5858_) == 0 {
        if leanh::lean_obj_tag(v_x_5859_) == 0 {
            let mut v___x_5860_: u8 = 0;
            v___x_5860_ = 1;
            return v___x_5860_;
        } else {
            let mut v___x_5861_: u8 = 0;
            v___x_5861_ = 0;
            return v___x_5861_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_5859_) == 0 {
            let mut v___x_5862_: u8 = 0;
            v___x_5862_ = 0;
            return v___x_5862_;
        } else {
            let mut v_val_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5865_: u8 = 0;
            v_val_5863_ = leanh::lean_ctor_get(v_x_5858_, 0);
            v_val_5864_ = leanh::lean_ctor_get(v_x_5859_, 0);
            v___x_5865_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_5863_, v_val_5864_);
            return v___x_5865_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(
    mut v_x_5866_: *mut leanh::LeanObject,
    mut v_x_5867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5868_: u8 = 0;
    let mut v_r_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5868_ =
        l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_5866_, v_x_5867_);
    leanh::lean_dec(v_x_5867_);
    leanh::lean_dec(v_x_5866_);
    v_r_5869_ = leanh::lean_box((v_res_5868_) as usize);
    return v_r_5869_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(
    mut v_x_5870_: *mut leanh::LeanObject,
    mut v_x_5871_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5870_) == 0 {
        if leanh::lean_obj_tag(v_x_5871_) == 0 {
            let mut v___x_5872_: u8 = 0;
            v___x_5872_ = 1;
            return v___x_5872_;
        } else {
            let mut v___x_5873_: u8 = 0;
            v___x_5873_ = 0;
            return v___x_5873_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_5871_) == 0 {
            let mut v___x_5874_: u8 = 0;
            v___x_5874_ = 0;
            return v___x_5874_;
        } else {
            let mut v_val_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5877_: u8 = 0;
            v_val_5875_ = leanh::lean_ctor_get(v_x_5870_, 0);
            v_val_5876_ = leanh::lean_ctor_get(v_x_5871_, 0);
            v___x_5877_ = lean_string_dec_eq(v_val_5875_, v_val_5876_);
            return v___x_5877_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(
    mut v_x_5878_: *mut leanh::LeanObject,
    mut v_x_5879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5880_: u8 = 0;
    let mut v_r_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5880_ =
        l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_5878_, v_x_5879_);
    leanh::lean_dec(v_x_5879_);
    leanh::lean_dec(v_x_5878_);
    v_r_5881_ = leanh::lean_box((v_res_5880_) as usize);
    return v_r_5881_;
}
pub unsafe fn l_Std_Http_instBEqURI_beq(
    mut v_x_5882_: *mut leanh::LeanObject,
    mut v_x_5883_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_scheme_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: u8 = 0;
    v_scheme_5884_ = leanh::lean_ctor_get(v_x_5882_, 0);
    v_authority_5885_ = leanh::lean_ctor_get(v_x_5882_, 1);
    v_path_5886_ = leanh::lean_ctor_get(v_x_5882_, 2);
    v_query_5887_ = leanh::lean_ctor_get(v_x_5882_, 3);
    v_fragment_5888_ = leanh::lean_ctor_get(v_x_5882_, 4);
    v_scheme_5889_ = leanh::lean_ctor_get(v_x_5883_, 0);
    v_authority_5890_ = leanh::lean_ctor_get(v_x_5883_, 1);
    v_path_5891_ = leanh::lean_ctor_get(v_x_5883_, 2);
    v_query_5892_ = leanh::lean_ctor_get(v_x_5883_, 3);
    v_fragment_5893_ = leanh::lean_ctor_get(v_x_5883_, 4);
    v___x_5894_ = lean_string_dec_eq(v_scheme_5884_, v_scheme_5889_);
    if v___x_5894_ == 0 {
        return v___x_5894_;
    } else {
        let mut v___x_5895_: u8 = 0;
        v___x_5895_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(
            v_authority_5885_,
            v_authority_5890_,
        );
        if v___x_5895_ == 0 {
            return v___x_5895_;
        } else {
            let mut v___x_5896_: u8 = 0;
            v___x_5896_ = l_Std_Http_URI_instBEqPath_beq(v_path_5886_, v_path_5891_);
            if v___x_5896_ == 0 {
                return v___x_5896_;
            } else {
                let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5899_: u8 = 0;
                v___x_5897_ = lean_array_get_size(v_query_5887_);
                v___x_5898_ = lean_array_get_size(v_query_5892_);
                v___x_5899_ = lean_nat_dec_eq(v___x_5897_, v___x_5898_);
                if v___x_5899_ == 0 {
                    return v___x_5899_;
                } else {
                    let mut v___x_5900_: u8 = 0;
                    v___x_5900_ =
                        l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(
                            v_query_5887_,
                            v_query_5892_,
                            v___x_5897_,
                        );
                    if v___x_5900_ == 0 {
                        return v___x_5900_;
                    } else {
                        let mut v___x_5901_: u8 = 0;
                        v___x_5901_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(
                            v_fragment_5888_,
                            v_fragment_5893_,
                        );
                        return v___x_5901_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Http_instBEqURI_beq___boxed(
    mut v_x_5902_: *mut leanh::LeanObject,
    mut v_x_5903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5904_: u8 = 0;
    let mut v_r_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5904_ = l_Std_Http_instBEqURI_beq(v_x_5902_, v_x_5903_);
    leanh::lean_dec_ref(v_x_5903_);
    leanh::lean_dec_ref(v_x_5902_);
    v_r_5905_ = leanh::lean_box((v_res_5904_) as usize);
    return v_r_5905_;
}
pub unsafe fn l_Std_Http_instToStringURI___lam__2(
    mut v___f_5910_: *mut leanh::LeanObject,
    mut v___f_5911_: *mut leanh::LeanObject,
    mut v_uri_5912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: u8 = 0;
    let mut v___x_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_5956_: u8 = 0;
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5959_: usize = 0;
    let mut v___x_5960_: usize = 0;
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_5983_: u16 = 0;
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_5913_ = leanh::lean_ctor_get(v_uri_5912_, 0);
                leanh::lean_inc_ref(v_scheme_5913_);
                v_authority_5914_ = leanh::lean_ctor_get(v_uri_5912_, 1);
                leanh::lean_inc(v_authority_5914_);
                v_path_5915_ = leanh::lean_ctor_get(v_uri_5912_, 2);
                leanh::lean_inc_ref(v_path_5915_);
                v_query_5916_ = leanh::lean_ctor_get(v_uri_5912_, 3);
                leanh::lean_inc_ref(v_query_5916_);
                v_fragment_5917_ = leanh::lean_ctor_get(v_uri_5912_, 4);
                leanh::lean_inc(v_fragment_5917_);
                leanh::lean_dec_ref(v_uri_5912_);
                if leanh::lean_obj_tag(v_authority_5914_) == 0 {
                    v___x_5965_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_5954_ = v___x_5965_;
                    state = 4;
                    continue;
                } else {
                    v_val_5966_ = leanh::lean_ctor_get(v_authority_5914_, 0);
                    leanh::lean_inc(v_val_5966_);
                    leanh::lean_dec_ref_known(v_authority_5914_, 1);
                    v_userInfo_5967_ = leanh::lean_ctor_get(v_val_5966_, 0);
                    leanh::lean_inc(v_userInfo_5967_);
                    v_host_5968_ = leanh::lean_ctor_get(v_val_5966_, 1);
                    leanh::lean_inc_ref(v_host_5968_);
                    v_port_5969_ = leanh::lean_ctor_get(v_val_5966_, 2);
                    leanh::lean_inc(v_port_5969_);
                    leanh::lean_dec(v_val_5966_);
                    v___x_5970_ = l_Std_Http_instToStringURI___lam__2___closed__1;
                    if leanh::lean_obj_tag(v_userInfo_5967_) == 0 {
                        v___x_5999_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                        v___y_5989_ = v___x_5999_;
                        state = 7;
                        continue;
                    } else {
                        v_val_6000_ = leanh::lean_ctor_get(v_userInfo_5967_, 0);
                        leanh::lean_inc(v_val_6000_);
                        leanh::lean_dec_ref_known(v_userInfo_5967_, 1);
                        v_password_6001_ = leanh::lean_ctor_get(v_val_6000_, 1);
                        if leanh::lean_obj_tag(v_password_6001_) == 0 {
                            v_username_6002_ = leanh::lean_ctor_get(v_val_6000_, 0);
                            leanh::lean_inc_ref(v_username_6002_);
                            leanh::lean_dec(v_val_6000_);
                            v___x_6003_ = lean_string_from_utf8_unchecked(v_username_6002_);
                            v___x_6004_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_6005_ = lean_string_append(v___x_6003_, v___x_6004_);
                            v___y_5989_ = v___x_6005_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_password_6001_);
                            v_username_6006_ = leanh::lean_ctor_get(v_val_6000_, 0);
                            leanh::lean_inc_ref(v_username_6006_);
                            leanh::lean_dec(v_val_6000_);
                            v_val_6007_ = leanh::lean_ctor_get(v_password_6001_, 0);
                            leanh::lean_inc(v_val_6007_);
                            leanh::lean_dec_ref_known(v_password_6001_, 1);
                            v___x_6008_ = lean_string_from_utf8_unchecked(v_username_6006_);
                            v___x_6009_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                            v___x_6010_ = lean_string_append(v___x_6008_, v___x_6009_);
                            v___x_6011_ = lean_string_from_utf8_unchecked(v_val_6007_);
                            v___x_6012_ = lean_string_append(v___x_6010_, v___x_6011_);
                            leanh::lean_dec_ref(v___x_6011_);
                            v___x_6013_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_6014_ = lean_string_append(v___x_6012_, v___x_6013_);
                            v___y_5989_ = v___x_6014_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5923_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                v___x_5924_ = lean_string_append(v_scheme_5913_, v___x_5923_);
                v___x_5925_ = lean_string_append(v___x_5924_, v___y_5920_);
                leanh::lean_dec_ref(v___y_5920_);
                v___x_5926_ = lean_string_append(v___x_5925_, v___y_5921_);
                leanh::lean_dec_ref(v___y_5921_);
                v___x_5927_ = lean_string_append(v___x_5926_, v___y_5919_);
                leanh::lean_dec_ref(v___y_5919_);
                v___x_5928_ = lean_string_append(v___x_5927_, v___y_5922_);
                leanh::lean_dec_ref(v___y_5922_);
                return v___x_5928_;
            }
            2 => {
                if leanh::lean_obj_tag(v_fragment_5917_) == 0 {
                    v___x_5933_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_5919_ = v___y_5932_;
                    v___y_5920_ = v___y_5930_;
                    v___y_5921_ = v___y_5931_;
                    v___y_5922_ = v___x_5933_;
                    state = 1;
                    continue;
                } else {
                    v_val_5934_ = leanh::lean_ctor_get(v_fragment_5917_, 0);
                    leanh::lean_inc(v_val_5934_);
                    leanh::lean_dec_ref_known(v_fragment_5917_, 1);
                    v___x_5935_ = l_Std_Http_instToStringURI___lam__2___closed__0;
                    v___x_5936_ = l_Std_Http_URI_EncodedFragment_encode(v_val_5934_);
                    leanh::lean_dec(v_val_5934_);
                    v___x_5937_ = lean_string_from_utf8_unchecked(v___x_5936_);
                    v___x_5938_ = lean_string_append(v___x_5935_, v___x_5937_);
                    leanh::lean_dec_ref(v___x_5937_);
                    v___y_5919_ = v___y_5932_;
                    v___y_5920_ = v___y_5930_;
                    v___y_5921_ = v___y_5931_;
                    v___y_5922_ = v___x_5938_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5942_ = lean_array_get_size(v_query_5916_);
                v___x_5943_ = leanh::lean_unsigned_to_nat(0);
                v___x_5944_ = lean_nat_dec_eq(v___x_5942_, v___x_5943_);
                if v___x_5944_ == 0 {
                    v___x_5945_ = lean_array_to_list(v_query_5916_);
                    v___x_5946_ = leanh::lean_box(0);
                    v_encodedParams_5947_ =
                        l_List_mapTR_loop___redArg(v___f_5910_, v___x_5945_, v___x_5946_);
                    v___x_5948_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
                    v___x_5949_ = l_Std_Http_URI_Query_toRawString___closed__0;
                    v___x_5950_ = l_String_intercalate(v___x_5949_, v_encodedParams_5947_);
                    v___x_5951_ = lean_string_append(v___x_5948_, v___x_5950_);
                    leanh::lean_dec_ref(v___x_5950_);
                    v___y_5930_ = v___y_5940_;
                    v___y_5931_ = v___y_5941_;
                    v___y_5932_ = v___x_5951_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_query_5916_);
                    leanh::lean_dec_ref(v___f_5910_);
                    v___x_5952_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_5930_ = v___y_5940_;
                    v___y_5931_ = v___y_5941_;
                    v___y_5932_ = v___x_5952_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_segments_5955_ = leanh::lean_ctor_get(v_path_5915_, 0);
                leanh::lean_inc_ref(v_segments_5955_);
                v_absolute_5956_ = leanh::lean_ctor_get_uint8(
                    v_path_5915_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_path_5915_);
                v___x_5957_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
                v___x_5958_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
                v_sz_5959_ = lean_array_size(v_segments_5955_);
                v___x_5960_ = 0usize;
                v___x_5961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5958_,
                    v___f_5911_,
                    v_sz_5959_,
                    v___x_5960_,
                    v_segments_5955_,
                );
                v___x_5962_ = lean_array_to_list(v___x_5961_);
                v_result_5963_ = l_String_intercalate(v___x_5957_, v___x_5962_);
                if v_absolute_5956_ == 0 {
                    v___y_5940_ = v___y_5954_;
                    v___y_5941_ = v_result_5963_;
                    state = 3;
                    continue;
                } else {
                    v___x_5964_ = lean_string_append(v___x_5957_, v_result_5963_);
                    leanh::lean_dec_ref(v_result_5963_);
                    v___y_5940_ = v___y_5954_;
                    v___y_5941_ = v___x_5964_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_5975_ = lean_string_append(v___y_5973_, v___y_5972_);
                leanh::lean_dec_ref(v___y_5972_);
                v___x_5976_ = lean_string_append(v___x_5975_, v___y_5974_);
                leanh::lean_dec_ref(v___y_5974_);
                v___x_5977_ = lean_string_append(v___x_5970_, v___x_5976_);
                leanh::lean_dec_ref(v___x_5976_);
                v___y_5954_ = v___x_5977_;
                state = 4;
                continue;
            }
            6 => match leanh::lean_obj_tag(v_port_5969_) {
                0 => {
                    v___x_5981_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_5972_ = v___y_5980_;
                    v___y_5973_ = v___y_5979_;
                    v___y_5974_ = v___x_5981_;
                    state = 5;
                    continue;
                }
                1 => {
                    v___x_5982_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_5972_ = v___y_5980_;
                    v___y_5973_ = v___y_5979_;
                    v___y_5974_ = v___x_5982_;
                    state = 5;
                    continue;
                }
                _ => {
                    v_port_5983_ = leanh::lean_ctor_get_uint16(v_port_5969_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_5969_, 0);
                    v___x_5984_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_5985_ = lean_uint16_to_nat(v_port_5983_);
                    v___x_5986_ = l_Nat_reprFast(v___x_5985_);
                    v___x_5987_ = lean_string_append(v___x_5984_, v___x_5986_);
                    leanh::lean_dec_ref(v___x_5986_);
                    v___y_5972_ = v___y_5980_;
                    v___y_5973_ = v___y_5979_;
                    v___y_5974_ = v___x_5987_;
                    state = 5;
                    continue;
                }
            },
            7 => match leanh::lean_obj_tag(v_host_5968_) {
                0 => {
                    v_name_5990_ = leanh::lean_ctor_get(v_host_5968_, 0);
                    leanh::lean_inc_ref(v_name_5990_);
                    leanh::lean_dec_ref_known(v_host_5968_, 1);
                    v___y_5979_ = v___y_5989_;
                    v___y_5980_ = v_name_5990_;
                    state = 6;
                    continue;
                }
                1 => {
                    v_ipv4_5991_ = leanh::lean_ctor_get(v_host_5968_, 0);
                    leanh::lean_inc_ref(v_ipv4_5991_);
                    leanh::lean_dec_ref_known(v_host_5968_, 1);
                    v___x_5992_ = lean_uv_ntop_v4(v_ipv4_5991_);
                    leanh::lean_dec_ref(v_ipv4_5991_);
                    v___y_5979_ = v___y_5989_;
                    v___y_5980_ = v___x_5992_;
                    state = 6;
                    continue;
                }
                _ => {
                    v_ipv6_5993_ = leanh::lean_ctor_get(v_host_5968_, 0);
                    leanh::lean_inc_ref(v_ipv6_5993_);
                    leanh::lean_dec_ref_known(v_host_5968_, 1);
                    v___x_5994_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_5995_ = lean_uv_ntop_v6(v_ipv6_5993_);
                    leanh::lean_dec_ref(v_ipv6_5993_);
                    v___x_5996_ = lean_string_append(v___x_5994_, v___x_5995_);
                    leanh::lean_dec_ref(v___x_5995_);
                    v___x_5997_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_5998_ = lean_string_append(v___x_5996_, v___x_5997_);
                    v___y_5979_ = v___y_5989_;
                    v___y_5980_ = v___x_5998_;
                    state = 6;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setScheme_x3f(
    mut v_b_6028_: *mut leanh::LeanObject,
    mut v_scheme_6029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6045_: u8 = 0;
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut v_unused_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_unused_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6030_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_6029_);
                if leanh::lean_obj_tag(v___x_6030_) == 0 {
                    leanh::lean_dec_ref(v_b_6028_);
                    v___x_6031_ = leanh::lean_box(0);
                    return v___x_6031_;
                } else {
                    v_userInfo_6032_ = leanh::lean_ctor_get(v_b_6028_, 1);
                    v_host_6033_ = leanh::lean_ctor_get(v_b_6028_, 2);
                    v_port_6034_ = leanh::lean_ctor_get(v_b_6028_, 3);
                    v_pathSegments_6035_ = leanh::lean_ctor_get(v_b_6028_, 4);
                    v_query_6036_ = leanh::lean_ctor_get(v_b_6028_, 5);
                    v_fragment_6037_ = leanh::lean_ctor_get(v_b_6028_, 6);
                    v_isSharedCheck_6052_ = (!leanh::lean_is_exclusive(v_b_6028_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v_unused_6053_ = leanh::lean_ctor_get(v_b_6028_, 0);
                        leanh::lean_dec(v_unused_6053_);
                        v___x_6039_ = v_b_6028_;
                        v_isShared_6040_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fragment_6037_);
                        leanh::lean_inc(v_query_6036_);
                        leanh::lean_inc(v_pathSegments_6035_);
                        leanh::lean_inc(v_port_6034_);
                        leanh::lean_inc(v_host_6033_);
                        leanh::lean_inc(v_userInfo_6032_);
                        leanh::lean_dec(v_b_6028_);
                        v___x_6039_ = leanh::lean_box(0);
                        v_isShared_6040_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___x_6030_);
                if v_isShared_6040_ == 0 {
                    leanh::lean_ctor_set(v___x_6039_, 0, v___x_6030_);
                    v___x_6042_ = v___x_6039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_6030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_userInfo_6032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 2, v_host_6033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 3, v_port_6034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 4, v_pathSegments_6035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 5, v_query_6036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 6, v_fragment_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_isSharedCheck_6049_ = (!leanh::lean_is_exclusive(v___x_6030_)) as u8;
                if v_isSharedCheck_6049_ == 0 {
                    v_unused_6050_ = leanh::lean_ctor_get(v___x_6030_, 0);
                    leanh::lean_dec(v_unused_6050_);
                    v___x_6044_ = v___x_6030_;
                    v_isShared_6045_ = v_isSharedCheck_6049_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6030_);
                    v___x_6044_ = leanh::lean_box(0);
                    v_isShared_6045_ = v_isSharedCheck_6049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6045_ == 0 {
                    leanh::lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                    v___x_6047_ = v___x_6044_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6042_);
                    v___x_6047_ = v_reuseFailAlloc_6048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(
    mut v_msg_6054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ = l_Std_Http_URI_instInhabitedBuilder_default;
    v___x_6056_ = lean_panic_fn_borrowed(v___x_6055_, v_msg_6054_);
    return v___x_6056_;
}
pub unsafe fn l_Std_Http_URI_Builder_setScheme_x21(
    mut v_b_6058_: *mut leanh::LeanObject,
    mut v_scheme_6059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_scheme_6059_);
    v___x_6060_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_6058_, v_scheme_6059_);
    if leanh::lean_obj_tag(v___x_6060_) == 0 {
        let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6061_ = l_Std_Http_URI_Scheme_ofString_x21___closed__0;
        v___x_6062_ = l_Std_Http_URI_Builder_setScheme_x21___closed__0;
        v___x_6063_ = leanh::lean_unsigned_to_nat(679);
        v___x_6064_ = leanh::lean_unsigned_to_nat(14);
        v___x_6065_ = l_Std_Http_URI_Scheme_ofString_x21___closed__2;
        v___x_6066_ = l_String_quote(v_scheme_6059_);
        v___x_6067_ = lean_string_append(v___x_6065_, v___x_6066_);
        leanh::lean_dec_ref(v___x_6066_);
        v___x_6068_ = l_mkPanicMessageWithDecl(
            v___x_6061_,
            v___x_6062_,
            v___x_6063_,
            v___x_6064_,
            v___x_6067_,
        );
        leanh::lean_dec_ref(v___x_6067_);
        v___x_6069_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_6068_);
        return v___x_6069_;
    } else {
        let mut v_val_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_scheme_6059_);
        v_val_6070_ = leanh::lean_ctor_get(v___x_6060_, 0);
        leanh::lean_inc(v_val_6070_);
        leanh::lean_dec_ref_known(v___x_6060_, 1);
        return v_val_6070_;
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setUserInfo(
    mut v_b_6071_: *mut leanh::LeanObject,
    mut v_username_6072_: *mut leanh::LeanObject,
    mut v_password_6073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___y_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6101_: u8 = 0;
    let mut v_isSharedCheck_6102_: u8 = 0;
    let mut v_unused_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6074_ = leanh::lean_ctor_get(v_b_6071_, 0);
                v_host_6075_ = leanh::lean_ctor_get(v_b_6071_, 2);
                v_port_6076_ = leanh::lean_ctor_get(v_b_6071_, 3);
                v_pathSegments_6077_ = leanh::lean_ctor_get(v_b_6071_, 4);
                v_query_6078_ = leanh::lean_ctor_get(v_b_6071_, 5);
                v_fragment_6079_ = leanh::lean_ctor_get(v_b_6071_, 6);
                v_isSharedCheck_6102_ = (!leanh::lean_is_exclusive(v_b_6071_)) as u8;
                if v_isSharedCheck_6102_ == 0 {
                    v_unused_6103_ = leanh::lean_ctor_get(v_b_6071_, 1);
                    leanh::lean_dec(v_unused_6103_);
                    v___x_6081_ = v_b_6071_;
                    v_isShared_6082_ = v_isSharedCheck_6102_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6079_);
                    leanh::lean_inc(v_query_6078_);
                    leanh::lean_inc(v_pathSegments_6077_);
                    leanh::lean_inc(v_port_6076_);
                    leanh::lean_inc(v_host_6075_);
                    leanh::lean_inc(v_scheme_6074_);
                    leanh::lean_dec(v_b_6071_);
                    v___x_6081_ = leanh::lean_box(0);
                    v_isShared_6082_ = v_isSharedCheck_6102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6089_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_6072_);
                if leanh::lean_obj_tag(v_password_6073_) == 0 {
                    v___x_6090_ = leanh::lean_box(0);
                    v___x_6091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6091_, 0, v___x_6089_);
                    leanh::lean_ctor_set(v___x_6091_, 1, v___x_6090_);
                    v___y_6084_ = v___x_6091_;
                    state = 2;
                    continue;
                } else {
                    v_val_6092_ = leanh::lean_ctor_get(v_password_6073_, 0);
                    v_isSharedCheck_6101_ =
                        (!leanh::lean_is_exclusive(v_password_6073_)) as u8;
                    if v_isSharedCheck_6101_ == 0 {
                        v___x_6094_ = v_password_6073_;
                        v_isShared_6095_ = v_isSharedCheck_6101_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6092_);
                        leanh::lean_dec(v_password_6073_);
                        v___x_6094_ = leanh::lean_box(0);
                        v_isShared_6095_ = v_isSharedCheck_6101_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6085_, 0, v___y_6084_);
                if v_isShared_6082_ == 0 {
                    leanh::lean_ctor_set(v___x_6081_, 1, v___x_6085_);
                    v___x_6087_ = v___x_6081_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6088_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_scheme_6074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 1, v___x_6085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 2, v_host_6075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 3, v_port_6076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 4, v_pathSegments_6077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 5, v_query_6078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 6, v_fragment_6079_);
                    v___x_6087_ = v_reuseFailAlloc_6088_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6087_;
            }
            4 => {
                v___x_6096_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_6092_);
                leanh::lean_dec(v_val_6092_);
                if v_isShared_6095_ == 0 {
                    leanh::lean_ctor_set(v___x_6094_, 0, v___x_6096_);
                    v___x_6098_ = v___x_6094_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6096_);
                    v___x_6098_ = v_reuseFailAlloc_6100_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6099_, 0, v___x_6089_);
                leanh::lean_ctor_set(v___x_6099_, 1, v___x_6098_);
                v___y_6084_ = v___x_6099_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setUserInfo___boxed(
    mut v_b_6104_: *mut leanh::LeanObject,
    mut v_username_6105_: *mut leanh::LeanObject,
    mut v_password_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6107_ = l_Std_Http_URI_Builder_setUserInfo(v_b_6104_, v_username_6105_, v_password_6106_);
    leanh::lean_dec_ref(v_username_6105_);
    return v_res_6107_;
}
pub unsafe fn l_Std_Http_URI_Builder_setHost_x3f(
    mut v_b_6108_: *mut leanh::LeanObject,
    mut v_name_6109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6115_: u8 = 0;
    let mut v_scheme_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6133_: u8 = 0;
    let mut v_unused_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6110_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_6109_);
                if leanh::lean_obj_tag(v___x_6110_) == 0 {
                    leanh::lean_dec_ref(v_b_6108_);
                    v___x_6111_ = leanh::lean_box(0);
                    return v___x_6111_;
                } else {
                    v_val_6112_ = leanh::lean_ctor_get(v___x_6110_, 0);
                    v_isSharedCheck_6135_ = (!leanh::lean_is_exclusive(v___x_6110_)) as u8;
                    if v_isSharedCheck_6135_ == 0 {
                        v___x_6114_ = v___x_6110_;
                        v_isShared_6115_ = v_isSharedCheck_6135_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6112_);
                        leanh::lean_dec(v___x_6110_);
                        v___x_6114_ = leanh::lean_box(0);
                        v_isShared_6115_ = v_isSharedCheck_6135_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_scheme_6116_ = leanh::lean_ctor_get(v_b_6108_, 0);
                v_userInfo_6117_ = leanh::lean_ctor_get(v_b_6108_, 1);
                v_port_6118_ = leanh::lean_ctor_get(v_b_6108_, 3);
                v_pathSegments_6119_ = leanh::lean_ctor_get(v_b_6108_, 4);
                v_query_6120_ = leanh::lean_ctor_get(v_b_6108_, 5);
                v_fragment_6121_ = leanh::lean_ctor_get(v_b_6108_, 6);
                v_isSharedCheck_6133_ = (!leanh::lean_is_exclusive(v_b_6108_)) as u8;
                if v_isSharedCheck_6133_ == 0 {
                    v_unused_6134_ = leanh::lean_ctor_get(v_b_6108_, 2);
                    leanh::lean_dec(v_unused_6134_);
                    v___x_6123_ = v_b_6108_;
                    v_isShared_6124_ = v_isSharedCheck_6133_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6121_);
                    leanh::lean_inc(v_query_6120_);
                    leanh::lean_inc(v_pathSegments_6119_);
                    leanh::lean_inc(v_port_6118_);
                    leanh::lean_inc(v_userInfo_6117_);
                    leanh::lean_inc(v_scheme_6116_);
                    leanh::lean_dec(v_b_6108_);
                    v___x_6123_ = leanh::lean_box(0);
                    v_isShared_6124_ = v_isSharedCheck_6133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6125_, 0, v_val_6112_);
                if v_isShared_6115_ == 0 {
                    leanh::lean_ctor_set(v___x_6114_, 0, v___x_6125_);
                    v___x_6127_ = v___x_6114_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 0, v___x_6125_);
                    v___x_6127_ = v_reuseFailAlloc_6132_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6124_ == 0 {
                    leanh::lean_ctor_set(v___x_6123_, 2, v___x_6127_);
                    v___x_6129_ = v___x_6123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6131_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_scheme_6116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 1, v_userInfo_6117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 2, v___x_6127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 3, v_port_6118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 4, v_pathSegments_6119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 5, v_query_6120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6131_, 6, v_fragment_6121_);
                    v___x_6129_ = v_reuseFailAlloc_6131_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6130_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6130_, 0, v___x_6129_);
                return v___x_6130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setHost_x21(
    mut v_b_6138_: *mut leanh::LeanObject,
    mut v_name_6139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_name_6139_);
    v___x_6140_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_6138_, v_name_6139_);
    if leanh::lean_obj_tag(v___x_6140_) == 0 {
        let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6141_ = l_Std_Http_URI_Scheme_ofString_x21___closed__0;
        v___x_6142_ = l_Std_Http_URI_Builder_setHost_x21___closed__0;
        v___x_6143_ = leanh::lean_unsigned_to_nat(708);
        v___x_6144_ = leanh::lean_unsigned_to_nat(14);
        v___x_6145_ = l_Std_Http_URI_Builder_setHost_x21___closed__1;
        v___x_6146_ = l_String_quote(v_name_6139_);
        v___x_6147_ = lean_string_append(v___x_6145_, v___x_6146_);
        leanh::lean_dec_ref(v___x_6146_);
        v___x_6148_ = l_mkPanicMessageWithDecl(
            v___x_6141_,
            v___x_6142_,
            v___x_6143_,
            v___x_6144_,
            v___x_6147_,
        );
        leanh::lean_dec_ref(v___x_6147_);
        v___x_6149_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_6148_);
        return v___x_6149_;
    } else {
        let mut v_val_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_name_6139_);
        v_val_6150_ = leanh::lean_ctor_get(v___x_6140_, 0);
        leanh::lean_inc(v_val_6150_);
        leanh::lean_dec_ref_known(v___x_6140_, 1);
        return v_val_6150_;
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setHostIPv4(
    mut v_b_6151_: *mut leanh::LeanObject,
    mut v_addr_6152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v_unused_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6153_ = leanh::lean_ctor_get(v_b_6151_, 0);
                v_userInfo_6154_ = leanh::lean_ctor_get(v_b_6151_, 1);
                v_port_6155_ = leanh::lean_ctor_get(v_b_6151_, 3);
                v_pathSegments_6156_ = leanh::lean_ctor_get(v_b_6151_, 4);
                v_query_6157_ = leanh::lean_ctor_get(v_b_6151_, 5);
                v_fragment_6158_ = leanh::lean_ctor_get(v_b_6151_, 6);
                v_isSharedCheck_6167_ = (!leanh::lean_is_exclusive(v_b_6151_)) as u8;
                if v_isSharedCheck_6167_ == 0 {
                    v_unused_6168_ = leanh::lean_ctor_get(v_b_6151_, 2);
                    leanh::lean_dec(v_unused_6168_);
                    v___x_6160_ = v_b_6151_;
                    v_isShared_6161_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6158_);
                    leanh::lean_inc(v_query_6157_);
                    leanh::lean_inc(v_pathSegments_6156_);
                    leanh::lean_inc(v_port_6155_);
                    leanh::lean_inc(v_userInfo_6154_);
                    leanh::lean_inc(v_scheme_6153_);
                    leanh::lean_dec(v_b_6151_);
                    v___x_6160_ = leanh::lean_box(0);
                    v_isShared_6161_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6162_, 0, v_addr_6152_);
                v___x_6163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6163_, 0, v___x_6162_);
                if v_isShared_6161_ == 0 {
                    leanh::lean_ctor_set(v___x_6160_, 2, v___x_6163_);
                    v___x_6165_ = v___x_6160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_scheme_6153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 1, v_userInfo_6154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 2, v___x_6163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 3, v_port_6155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 4, v_pathSegments_6156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 5, v_query_6157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 6, v_fragment_6158_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setHostIPv6(
    mut v_b_6169_: *mut leanh::LeanObject,
    mut v_addr_6170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6179_: u8 = 0;
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_unused_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6171_ = leanh::lean_ctor_get(v_b_6169_, 0);
                v_userInfo_6172_ = leanh::lean_ctor_get(v_b_6169_, 1);
                v_port_6173_ = leanh::lean_ctor_get(v_b_6169_, 3);
                v_pathSegments_6174_ = leanh::lean_ctor_get(v_b_6169_, 4);
                v_query_6175_ = leanh::lean_ctor_get(v_b_6169_, 5);
                v_fragment_6176_ = leanh::lean_ctor_get(v_b_6169_, 6);
                v_isSharedCheck_6185_ = (!leanh::lean_is_exclusive(v_b_6169_)) as u8;
                if v_isSharedCheck_6185_ == 0 {
                    v_unused_6186_ = leanh::lean_ctor_get(v_b_6169_, 2);
                    leanh::lean_dec(v_unused_6186_);
                    v___x_6178_ = v_b_6169_;
                    v_isShared_6179_ = v_isSharedCheck_6185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6176_);
                    leanh::lean_inc(v_query_6175_);
                    leanh::lean_inc(v_pathSegments_6174_);
                    leanh::lean_inc(v_port_6173_);
                    leanh::lean_inc(v_userInfo_6172_);
                    leanh::lean_inc(v_scheme_6171_);
                    leanh::lean_dec(v_b_6169_);
                    v___x_6178_ = leanh::lean_box(0);
                    v_isShared_6179_ = v_isSharedCheck_6185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6180_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6180_, 0, v_addr_6170_);
                v___x_6181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6181_, 0, v___x_6180_);
                if v_isShared_6179_ == 0 {
                    leanh::lean_ctor_set(v___x_6178_, 2, v___x_6181_);
                    v___x_6183_ = v___x_6178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_scheme_6171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 1, v_userInfo_6172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 2, v___x_6181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 3, v_port_6173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 4, v_pathSegments_6174_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 5, v_query_6175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 6, v_fragment_6176_);
                    v___x_6183_ = v_reuseFailAlloc_6184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setPort(
    mut v_b_6187_: *mut leanh::LeanObject,
    mut v_port_6188_: u16,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_unused_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6189_ = leanh::lean_ctor_get(v_b_6187_, 0);
                v_userInfo_6190_ = leanh::lean_ctor_get(v_b_6187_, 1);
                v_host_6191_ = leanh::lean_ctor_get(v_b_6187_, 2);
                v_pathSegments_6192_ = leanh::lean_ctor_get(v_b_6187_, 4);
                v_query_6193_ = leanh::lean_ctor_get(v_b_6187_, 5);
                v_fragment_6194_ = leanh::lean_ctor_get(v_b_6187_, 6);
                v_isSharedCheck_6202_ = (!leanh::lean_is_exclusive(v_b_6187_)) as u8;
                if v_isSharedCheck_6202_ == 0 {
                    v_unused_6203_ = leanh::lean_ctor_get(v_b_6187_, 3);
                    leanh::lean_dec(v_unused_6203_);
                    v___x_6196_ = v_b_6187_;
                    v_isShared_6197_ = v_isSharedCheck_6202_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6194_);
                    leanh::lean_inc(v_query_6193_);
                    leanh::lean_inc(v_pathSegments_6192_);
                    leanh::lean_inc(v_host_6191_);
                    leanh::lean_inc(v_userInfo_6190_);
                    leanh::lean_inc(v_scheme_6189_);
                    leanh::lean_dec(v_b_6187_);
                    v___x_6196_ = leanh::lean_box(0);
                    v_isShared_6197_ = v_isSharedCheck_6202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6198_ = leanh::lean_alloc_ctor(2, 0, (2) as u32);
                leanh::lean_ctor_set_uint16(v___x_6198_, 0 as u32, v_port_6188_);
                if v_isShared_6197_ == 0 {
                    leanh::lean_ctor_set(v___x_6196_, 3, v___x_6198_);
                    v___x_6200_ = v___x_6196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6201_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_scheme_6189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 1, v_userInfo_6190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 2, v_host_6191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 3, v___x_6198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 4, v_pathSegments_6192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 5, v_query_6193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 6, v_fragment_6194_);
                    v___x_6200_ = v_reuseFailAlloc_6201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setPort___boxed(
    mut v_b_6204_: *mut leanh::LeanObject,
    mut v_port_6205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_port_boxed_6206_: u16 = 0;
    let mut v_res_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_port_boxed_6206_ = (leanh::lean_unbox(v_port_6205_) as u16);
    v_res_6207_ = l_Std_Http_URI_Builder_setPort(v_b_6204_, v_port_boxed_6206_);
    return v_res_6207_;
}
pub unsafe fn l_Std_Http_URI_Builder_setPath(
    mut v_b_6208_: *mut leanh::LeanObject,
    mut v_segments_6209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6218_: u8 = 0;
    let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6222_: u8 = 0;
    let mut v_unused_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6210_ = leanh::lean_ctor_get(v_b_6208_, 0);
                v_userInfo_6211_ = leanh::lean_ctor_get(v_b_6208_, 1);
                v_host_6212_ = leanh::lean_ctor_get(v_b_6208_, 2);
                v_port_6213_ = leanh::lean_ctor_get(v_b_6208_, 3);
                v_query_6214_ = leanh::lean_ctor_get(v_b_6208_, 5);
                v_fragment_6215_ = leanh::lean_ctor_get(v_b_6208_, 6);
                v_isSharedCheck_6222_ = (!leanh::lean_is_exclusive(v_b_6208_)) as u8;
                if v_isSharedCheck_6222_ == 0 {
                    v_unused_6223_ = leanh::lean_ctor_get(v_b_6208_, 4);
                    leanh::lean_dec(v_unused_6223_);
                    v___x_6217_ = v_b_6208_;
                    v_isShared_6218_ = v_isSharedCheck_6222_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6215_);
                    leanh::lean_inc(v_query_6214_);
                    leanh::lean_inc(v_port_6213_);
                    leanh::lean_inc(v_host_6212_);
                    leanh::lean_inc(v_userInfo_6211_);
                    leanh::lean_inc(v_scheme_6210_);
                    leanh::lean_dec(v_b_6208_);
                    v___x_6217_ = leanh::lean_box(0);
                    v_isShared_6218_ = v_isSharedCheck_6222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6218_ == 0 {
                    leanh::lean_ctor_set(v___x_6217_, 4, v_segments_6209_);
                    v___x_6220_ = v___x_6217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6221_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_scheme_6210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 1, v_userInfo_6211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 2, v_host_6212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 3, v_port_6213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 4, v_segments_6209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 5, v_query_6214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 6, v_fragment_6215_);
                    v___x_6220_ = v_reuseFailAlloc_6221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_appendPathSegment(
    mut v_b_6224_: *mut leanh::LeanObject,
    mut v_segment_6225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6226_ = leanh::lean_ctor_get(v_b_6224_, 0);
                v_userInfo_6227_ = leanh::lean_ctor_get(v_b_6224_, 1);
                v_host_6228_ = leanh::lean_ctor_get(v_b_6224_, 2);
                v_port_6229_ = leanh::lean_ctor_get(v_b_6224_, 3);
                v_pathSegments_6230_ = leanh::lean_ctor_get(v_b_6224_, 4);
                v_query_6231_ = leanh::lean_ctor_get(v_b_6224_, 5);
                v_fragment_6232_ = leanh::lean_ctor_get(v_b_6224_, 6);
                v_isSharedCheck_6240_ = (!leanh::lean_is_exclusive(v_b_6224_)) as u8;
                if v_isSharedCheck_6240_ == 0 {
                    v___x_6234_ = v_b_6224_;
                    v_isShared_6235_ = v_isSharedCheck_6240_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6232_);
                    leanh::lean_inc(v_query_6231_);
                    leanh::lean_inc(v_pathSegments_6230_);
                    leanh::lean_inc(v_port_6229_);
                    leanh::lean_inc(v_host_6228_);
                    leanh::lean_inc(v_userInfo_6227_);
                    leanh::lean_inc(v_scheme_6226_);
                    leanh::lean_dec(v_b_6224_);
                    v___x_6234_ = leanh::lean_box(0);
                    v_isShared_6235_ = v_isSharedCheck_6240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6236_ = lean_array_push(v_pathSegments_6230_, v_segment_6225_);
                if v_isShared_6235_ == 0 {
                    leanh::lean_ctor_set(v___x_6234_, 4, v___x_6236_);
                    v___x_6238_ = v___x_6234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6239_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 0, v_scheme_6226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 1, v_userInfo_6227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 2, v_host_6228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 3, v_port_6229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 4, v___x_6236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 5, v_query_6231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 6, v_fragment_6232_);
                    v___x_6238_ = v_reuseFailAlloc_6239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_addQueryParam(
    mut v_b_6241_: *mut leanh::LeanObject,
    mut v_key_6242_: *mut leanh::LeanObject,
    mut v_value_6243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6253_: u8 = 0;
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6244_ = leanh::lean_ctor_get(v_b_6241_, 0);
                v_userInfo_6245_ = leanh::lean_ctor_get(v_b_6241_, 1);
                v_host_6246_ = leanh::lean_ctor_get(v_b_6241_, 2);
                v_port_6247_ = leanh::lean_ctor_get(v_b_6241_, 3);
                v_pathSegments_6248_ = leanh::lean_ctor_get(v_b_6241_, 4);
                v_query_6249_ = leanh::lean_ctor_get(v_b_6241_, 5);
                v_fragment_6250_ = leanh::lean_ctor_get(v_b_6241_, 6);
                v_isSharedCheck_6260_ = (!leanh::lean_is_exclusive(v_b_6241_)) as u8;
                if v_isSharedCheck_6260_ == 0 {
                    v___x_6252_ = v_b_6241_;
                    v_isShared_6253_ = v_isSharedCheck_6260_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6250_);
                    leanh::lean_inc(v_query_6249_);
                    leanh::lean_inc(v_pathSegments_6248_);
                    leanh::lean_inc(v_port_6247_);
                    leanh::lean_inc(v_host_6246_);
                    leanh::lean_inc(v_userInfo_6245_);
                    leanh::lean_inc(v_scheme_6244_);
                    leanh::lean_dec(v_b_6241_);
                    v___x_6252_ = leanh::lean_box(0);
                    v_isShared_6253_ = v_isSharedCheck_6260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6254_, 0, v_value_6243_);
                v___x_6255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6255_, 0, v_key_6242_);
                leanh::lean_ctor_set(v___x_6255_, 1, v___x_6254_);
                v___x_6256_ = lean_array_push(v_query_6249_, v___x_6255_);
                if v_isShared_6253_ == 0 {
                    leanh::lean_ctor_set(v___x_6252_, 5, v___x_6256_);
                    v___x_6258_ = v___x_6252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6259_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_scheme_6244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 1, v_userInfo_6245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 2, v_host_6246_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 3, v_port_6247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 4, v_pathSegments_6248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 5, v___x_6256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 6, v_fragment_6250_);
                    v___x_6258_ = v_reuseFailAlloc_6259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_addQueryFlag(
    mut v_b_6261_: *mut leanh::LeanObject,
    mut v_key_6262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6272_: u8 = 0;
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6263_ = leanh::lean_ctor_get(v_b_6261_, 0);
                v_userInfo_6264_ = leanh::lean_ctor_get(v_b_6261_, 1);
                v_host_6265_ = leanh::lean_ctor_get(v_b_6261_, 2);
                v_port_6266_ = leanh::lean_ctor_get(v_b_6261_, 3);
                v_pathSegments_6267_ = leanh::lean_ctor_get(v_b_6261_, 4);
                v_query_6268_ = leanh::lean_ctor_get(v_b_6261_, 5);
                v_fragment_6269_ = leanh::lean_ctor_get(v_b_6261_, 6);
                v_isSharedCheck_6279_ = (!leanh::lean_is_exclusive(v_b_6261_)) as u8;
                if v_isSharedCheck_6279_ == 0 {
                    v___x_6271_ = v_b_6261_;
                    v_isShared_6272_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6269_);
                    leanh::lean_inc(v_query_6268_);
                    leanh::lean_inc(v_pathSegments_6267_);
                    leanh::lean_inc(v_port_6266_);
                    leanh::lean_inc(v_host_6265_);
                    leanh::lean_inc(v_userInfo_6264_);
                    leanh::lean_inc(v_scheme_6263_);
                    leanh::lean_dec(v_b_6261_);
                    v___x_6271_ = leanh::lean_box(0);
                    v_isShared_6272_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6273_ = leanh::lean_box(0);
                v___x_6274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6274_, 0, v_key_6262_);
                leanh::lean_ctor_set(v___x_6274_, 1, v___x_6273_);
                v___x_6275_ = lean_array_push(v_query_6268_, v___x_6274_);
                if v_isShared_6272_ == 0 {
                    leanh::lean_ctor_set(v___x_6271_, 5, v___x_6275_);
                    v___x_6277_ = v___x_6271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6278_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 0, v_scheme_6263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 1, v_userInfo_6264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 2, v_host_6265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 3, v_port_6266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 4, v_pathSegments_6267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 5, v___x_6275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6278_, 6, v_fragment_6269_);
                    v___x_6277_ = v_reuseFailAlloc_6278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setQuery(
    mut v_b_6280_: *mut leanh::LeanObject,
    mut v_query_6281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6290_: u8 = 0;
    let mut v___x_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6294_: u8 = 0;
    let mut v_unused_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6282_ = leanh::lean_ctor_get(v_b_6280_, 0);
                v_userInfo_6283_ = leanh::lean_ctor_get(v_b_6280_, 1);
                v_host_6284_ = leanh::lean_ctor_get(v_b_6280_, 2);
                v_port_6285_ = leanh::lean_ctor_get(v_b_6280_, 3);
                v_pathSegments_6286_ = leanh::lean_ctor_get(v_b_6280_, 4);
                v_fragment_6287_ = leanh::lean_ctor_get(v_b_6280_, 6);
                v_isSharedCheck_6294_ = (!leanh::lean_is_exclusive(v_b_6280_)) as u8;
                if v_isSharedCheck_6294_ == 0 {
                    v_unused_6295_ = leanh::lean_ctor_get(v_b_6280_, 5);
                    leanh::lean_dec(v_unused_6295_);
                    v___x_6289_ = v_b_6280_;
                    v_isShared_6290_ = v_isSharedCheck_6294_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6287_);
                    leanh::lean_inc(v_pathSegments_6286_);
                    leanh::lean_inc(v_port_6285_);
                    leanh::lean_inc(v_host_6284_);
                    leanh::lean_inc(v_userInfo_6283_);
                    leanh::lean_inc(v_scheme_6282_);
                    leanh::lean_dec(v_b_6280_);
                    v___x_6289_ = leanh::lean_box(0);
                    v_isShared_6290_ = v_isSharedCheck_6294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6290_ == 0 {
                    leanh::lean_ctor_set(v___x_6289_, 5, v_query_6281_);
                    v___x_6292_ = v___x_6289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6293_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_scheme_6282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 1, v_userInfo_6283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 2, v_host_6284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 3, v_port_6285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 4, v_pathSegments_6286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 5, v_query_6281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 6, v_fragment_6287_);
                    v___x_6292_ = v_reuseFailAlloc_6293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Builder_setFragment(
    mut v_b_6296_: *mut leanh::LeanObject,
    mut v_fragment_6297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_unused_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6298_ = leanh::lean_ctor_get(v_b_6296_, 0);
                v_userInfo_6299_ = leanh::lean_ctor_get(v_b_6296_, 1);
                v_host_6300_ = leanh::lean_ctor_get(v_b_6296_, 2);
                v_port_6301_ = leanh::lean_ctor_get(v_b_6296_, 3);
                v_pathSegments_6302_ = leanh::lean_ctor_get(v_b_6296_, 4);
                v_query_6303_ = leanh::lean_ctor_get(v_b_6296_, 5);
                v_isSharedCheck_6311_ = (!leanh::lean_is_exclusive(v_b_6296_)) as u8;
                if v_isSharedCheck_6311_ == 0 {
                    v_unused_6312_ = leanh::lean_ctor_get(v_b_6296_, 6);
                    leanh::lean_dec(v_unused_6312_);
                    v___x_6305_ = v_b_6296_;
                    v_isShared_6306_ = v_isSharedCheck_6311_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_query_6303_);
                    leanh::lean_inc(v_pathSegments_6302_);
                    leanh::lean_inc(v_port_6301_);
                    leanh::lean_inc(v_host_6300_);
                    leanh::lean_inc(v_userInfo_6299_);
                    leanh::lean_inc(v_scheme_6298_);
                    leanh::lean_dec(v_b_6296_);
                    v___x_6305_ = leanh::lean_box(0);
                    v_isShared_6306_ = v_isSharedCheck_6311_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6307_, 0, v_fragment_6297_);
                if v_isShared_6306_ == 0 {
                    leanh::lean_ctor_set(v___x_6305_, 6, v___x_6307_);
                    v___x_6309_ = v___x_6305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6310_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_scheme_6298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 1, v_userInfo_6299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 2, v_host_6300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 3, v_port_6301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 4, v_pathSegments_6302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 5, v_query_6303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 6, v___x_6307_);
                    v___x_6309_ = v_reuseFailAlloc_6310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(
    mut v_sz_6313_: usize,
    mut v_i_6314_: usize,
    mut v_bs_6315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6316_: u8 = 0;
    let mut v_v_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: usize = 0;
    let mut v___x_6322_: usize = 0;
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6316_ = lean_usize_dec_lt(v_i_6314_, v_sz_6313_);
                if v___x_6316_ == 0 {
                    return v_bs_6315_;
                } else {
                    v_v_6317_ = lean_array_uget(v_bs_6315_, v_i_6314_);
                    v___x_6318_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6319_ = lean_array_uset(v_bs_6315_, v_i_6314_, v___x_6318_);
                    v___x_6320_ = l_Std_Http_URI_EncodedSegment_encode(v_v_6317_);
                    leanh::lean_dec(v_v_6317_);
                    v___x_6321_ = 1usize;
                    v___x_6322_ = lean_usize_add(v_i_6314_, v___x_6321_);
                    v___x_6323_ = lean_array_uset(v_bs_x27_6319_, v_i_6314_, v___x_6320_);
                    v_i_6314_ = v___x_6322_;
                    v_bs_6315_ = v___x_6323_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(
    mut v_sz_6325_: *mut leanh::LeanObject,
    mut v_i_6326_: *mut leanh::LeanObject,
    mut v_bs_6327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6328_: usize = 0;
    let mut v_i_boxed_6329_: usize = 0;
    let mut v_res_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6328_ = leanh::lean_unbox_usize(v_sz_6325_);
    leanh::lean_dec(v_sz_6325_);
    v_i_boxed_6329_ = leanh::lean_unbox_usize(v_i_6326_);
    leanh::lean_dec(v_i_6326_);
    v_res_6330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_6328_, v_i_boxed_6329_, v_bs_6327_);
    return v_res_6330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(
    mut v_sz_6331_: usize,
    mut v_i_6332_: usize,
    mut v_bs_6333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6334_: u8 = 0;
    let mut v_v_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6340_: u8 = 0;
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: usize = 0;
    let mut v___x_6346_: usize = 0;
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6357_: u8 = 0;
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6365_: u8 = 0;
    let mut v_isSharedCheck_6366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6334_ = lean_usize_dec_lt(v_i_6332_, v_sz_6331_);
                if v___x_6334_ == 0 {
                    return v_bs_6333_;
                } else {
                    v_v_6335_ = lean_array_uget(v_bs_6333_, v_i_6332_);
                    v_fst_6336_ = leanh::lean_ctor_get(v_v_6335_, 0);
                    v_snd_6337_ = leanh::lean_ctor_get(v_v_6335_, 1);
                    v_isSharedCheck_6366_ = (!leanh::lean_is_exclusive(v_v_6335_)) as u8;
                    if v_isSharedCheck_6366_ == 0 {
                        v___x_6339_ = v_v_6335_;
                        v_isShared_6340_ = v_isSharedCheck_6366_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6337_);
                        leanh::lean_inc(v_fst_6336_);
                        leanh::lean_dec(v_v_6335_);
                        v___x_6339_ = leanh::lean_box(0);
                        v_isShared_6340_ = v_isSharedCheck_6366_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6341_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_6342_ = lean_array_uset(v_bs_6333_, v_i_6332_, v___x_6341_);
                v___x_6349_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_6336_);
                leanh::lean_dec(v_fst_6336_);
                if leanh::lean_obj_tag(v_snd_6337_) == 0 {
                    v___x_6350_ = leanh::lean_box(0);
                    if v_isShared_6340_ == 0 {
                        leanh::lean_ctor_set(v___x_6339_, 1, v___x_6350_);
                        leanh::lean_ctor_set(v___x_6339_, 0, v___x_6349_);
                        v___x_6352_ = v___x_6339_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6353_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6349_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6353_, 1, v___x_6350_);
                        v___x_6352_ = v_reuseFailAlloc_6353_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_6354_ = leanh::lean_ctor_get(v_snd_6337_, 0);
                    v_isSharedCheck_6365_ = (!leanh::lean_is_exclusive(v_snd_6337_)) as u8;
                    if v_isSharedCheck_6365_ == 0 {
                        v___x_6356_ = v_snd_6337_;
                        v_isShared_6357_ = v_isSharedCheck_6365_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6354_);
                        leanh::lean_dec(v_snd_6337_);
                        v___x_6356_ = leanh::lean_box(0);
                        v_isShared_6357_ = v_isSharedCheck_6365_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6345_ = 1usize;
                v___x_6346_ = lean_usize_add(v_i_6332_, v___x_6345_);
                v___x_6347_ = lean_array_uset(v_bs_x27_6342_, v_i_6332_, v___y_6344_);
                v_i_6332_ = v___x_6346_;
                v_bs_6333_ = v___x_6347_;
                state = 0;
                continue;
            }
            3 => {
                v___y_6344_ = v___x_6352_;
                state = 2;
                continue;
            }
            4 => {
                v___x_6358_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_6354_);
                leanh::lean_dec(v_val_6354_);
                if v_isShared_6357_ == 0 {
                    leanh::lean_ctor_set(v___x_6356_, 0, v___x_6358_);
                    v___x_6360_ = v___x_6356_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6364_, 0, v___x_6358_);
                    v___x_6360_ = v_reuseFailAlloc_6364_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6340_ == 0 {
                    leanh::lean_ctor_set(v___x_6339_, 1, v___x_6360_);
                    leanh::lean_ctor_set(v___x_6339_, 0, v___x_6349_);
                    v___x_6362_ = v___x_6339_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6363_, 0, v___x_6349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6363_, 1, v___x_6360_);
                    v___x_6362_ = v_reuseFailAlloc_6363_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_6344_ = v___x_6362_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(
    mut v_sz_6367_: *mut leanh::LeanObject,
    mut v_i_6368_: *mut leanh::LeanObject,
    mut v_bs_6369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6370_: usize = 0;
    let mut v_i_boxed_6371_: usize = 0;
    let mut v_res_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6370_ = leanh::lean_unbox_usize(v_sz_6367_);
    leanh::lean_dec(v_sz_6367_);
    v_i_boxed_6371_ = leanh::lean_unbox_usize(v_i_6368_);
    leanh::lean_dec(v_i_6368_);
    v_res_6372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_6370_, v_i_boxed_6371_, v_bs_6369_);
    return v_res_6372_;
}
pub unsafe fn l_Std_Http_URI_Builder_build(
    mut v_b_6373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6376_: u8 = 0;
    let mut v___y_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6381_: usize = 0;
    let mut v___x_6382_: usize = 0;
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6385_: usize = 0;
    let mut v_query_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pathSegments_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: u8 = 0;
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6404_: u8 = 0;
    let mut v___x_6405_: u8 = 0;
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6410_: u8 = 0;
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6390_ = leanh::lean_ctor_get(v_b_6373_, 0);
                leanh::lean_inc(v_scheme_6390_);
                v_userInfo_6391_ = leanh::lean_ctor_get(v_b_6373_, 1);
                leanh::lean_inc(v_userInfo_6391_);
                v_host_6392_ = leanh::lean_ctor_get(v_b_6373_, 2);
                leanh::lean_inc(v_host_6392_);
                v_port_6393_ = leanh::lean_ctor_get(v_b_6373_, 3);
                leanh::lean_inc(v_port_6393_);
                v_pathSegments_6394_ = leanh::lean_ctor_get(v_b_6373_, 4);
                leanh::lean_inc_ref(v_pathSegments_6394_);
                v_query_6395_ = leanh::lean_ctor_get(v_b_6373_, 5);
                leanh::lean_inc_ref(v_query_6395_);
                v_fragment_6396_ = leanh::lean_ctor_get(v_b_6373_, 6);
                leanh::lean_inc(v_fragment_6396_);
                leanh::lean_dec_ref(v_b_6373_);
                if leanh::lean_obj_tag(v_scheme_6390_) == 0 {
                    v___x_6411_ = l_Std_Http_URI_Scheme_defaultPort___closed__0;
                    v___y_6398_ = v___x_6411_;
                    state = 2;
                    continue;
                } else {
                    v_val_6412_ = leanh::lean_ctor_get(v_scheme_6390_, 0);
                    leanh::lean_inc(v_val_6412_);
                    leanh::lean_dec_ref_known(v_scheme_6390_, 1);
                    v___y_6398_ = v_val_6412_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_sz_6381_ = lean_array_size(v___y_6377_);
                v___x_6382_ = 0usize;
                v___x_6383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_6381_, v___x_6382_, v___y_6377_);
                v_path_6384_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v_path_6384_, 0, v___x_6383_);
                leanh::lean_ctor_set_uint8(
                    v_path_6384_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_6376_,
                );
                v_sz_6385_ = lean_array_size(v___y_6378_);
                v_query_6386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_6385_, v___x_6382_, v___y_6378_);
                v___x_6387_ = lean_array_to_list(v_query_6386_);
                v_query_6388_ = lean_array_mk(v___x_6387_);
                v___x_6389_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6389_, 0, v___y_6379_);
                leanh::lean_ctor_set(v___x_6389_, 1, v___y_6380_);
                leanh::lean_ctor_set(v___x_6389_, 2, v_path_6384_);
                leanh::lean_ctor_set(v___x_6389_, 3, v_query_6388_);
                leanh::lean_ctor_set(v___x_6389_, 4, v___y_6375_);
                return v___x_6389_;
            }
            2 => {
                if leanh::lean_obj_tag(v_host_6392_) == 0 {
                    leanh::lean_dec(v_port_6393_);
                    leanh::lean_dec(v_userInfo_6391_);
                    v___x_6399_ = 1;
                    v___x_6400_ = leanh::lean_box(0);
                    v___y_6375_ = v_fragment_6396_;
                    v___y_6376_ = v___x_6399_;
                    v___y_6377_ = v_pathSegments_6394_;
                    v___y_6378_ = v_query_6395_;
                    v___y_6379_ = v___y_6398_;
                    v___y_6380_ = v___x_6400_;
                    state = 1;
                    continue;
                } else {
                    v_val_6401_ = leanh::lean_ctor_get(v_host_6392_, 0);
                    v_isSharedCheck_6410_ = (!leanh::lean_is_exclusive(v_host_6392_)) as u8;
                    if v_isSharedCheck_6410_ == 0 {
                        v___x_6403_ = v_host_6392_;
                        v_isShared_6404_ = v_isSharedCheck_6410_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6401_);
                        leanh::lean_dec(v_host_6392_);
                        v___x_6403_ = leanh::lean_box(0);
                        v_isShared_6404_ = v_isSharedCheck_6410_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6405_ = 1;
                v___x_6406_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6406_, 0, v_userInfo_6391_);
                leanh::lean_ctor_set(v___x_6406_, 1, v_val_6401_);
                leanh::lean_ctor_set(v___x_6406_, 2, v_port_6393_);
                if v_isShared_6404_ == 0 {
                    leanh::lean_ctor_set(v___x_6403_, 0, v___x_6406_);
                    v___x_6408_ = v___x_6403_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6409_, 0, v___x_6406_);
                    v___x_6408_ = v_reuseFailAlloc_6409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_6375_ = v_fragment_6396_;
                v___y_6376_ = v___x_6405_;
                v___y_6377_ = v_pathSegments_6394_;
                v___y_6378_ = v_query_6395_;
                v___y_6379_ = v___y_6398_;
                v___y_6380_ = v___x_6408_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_withScheme_x21(
    mut v_uri_6413_: *mut leanh::LeanObject,
    mut v_scheme_6414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_authority_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6421_: u8 = 0;
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6426_: u8 = 0;
    let mut v_unused_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_authority_6415_ = leanh::lean_ctor_get(v_uri_6413_, 1);
                v_path_6416_ = leanh::lean_ctor_get(v_uri_6413_, 2);
                v_query_6417_ = leanh::lean_ctor_get(v_uri_6413_, 3);
                v_fragment_6418_ = leanh::lean_ctor_get(v_uri_6413_, 4);
                v_isSharedCheck_6426_ = (!leanh::lean_is_exclusive(v_uri_6413_)) as u8;
                if v_isSharedCheck_6426_ == 0 {
                    v_unused_6427_ = leanh::lean_ctor_get(v_uri_6413_, 0);
                    leanh::lean_dec(v_unused_6427_);
                    v___x_6420_ = v_uri_6413_;
                    v_isShared_6421_ = v_isSharedCheck_6426_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6418_);
                    leanh::lean_inc(v_query_6417_);
                    leanh::lean_inc(v_path_6416_);
                    leanh::lean_inc(v_authority_6415_);
                    leanh::lean_dec(v_uri_6413_);
                    v___x_6420_ = leanh::lean_box(0);
                    v_isShared_6421_ = v_isSharedCheck_6426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6422_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_6414_);
                if v_isShared_6421_ == 0 {
                    leanh::lean_ctor_set(v___x_6420_, 0, v___x_6422_);
                    v___x_6424_ = v___x_6420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6425_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6425_, 0, v___x_6422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6425_, 1, v_authority_6415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6425_, 2, v_path_6416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6425_, 3, v_query_6417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6425_, 4, v_fragment_6418_);
                    v___x_6424_ = v_reuseFailAlloc_6425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_withAuthority(
    mut v_uri_6428_: *mut leanh::LeanObject,
    mut v_authority_6429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6436_: u8 = 0;
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6440_: u8 = 0;
    let mut v_unused_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6430_ = leanh::lean_ctor_get(v_uri_6428_, 0);
                v_path_6431_ = leanh::lean_ctor_get(v_uri_6428_, 2);
                v_query_6432_ = leanh::lean_ctor_get(v_uri_6428_, 3);
                v_fragment_6433_ = leanh::lean_ctor_get(v_uri_6428_, 4);
                v_isSharedCheck_6440_ = (!leanh::lean_is_exclusive(v_uri_6428_)) as u8;
                if v_isSharedCheck_6440_ == 0 {
                    v_unused_6441_ = leanh::lean_ctor_get(v_uri_6428_, 1);
                    leanh::lean_dec(v_unused_6441_);
                    v___x_6435_ = v_uri_6428_;
                    v_isShared_6436_ = v_isSharedCheck_6440_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6433_);
                    leanh::lean_inc(v_query_6432_);
                    leanh::lean_inc(v_path_6431_);
                    leanh::lean_inc(v_scheme_6430_);
                    leanh::lean_dec(v_uri_6428_);
                    v___x_6435_ = leanh::lean_box(0);
                    v_isShared_6436_ = v_isSharedCheck_6440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6436_ == 0 {
                    leanh::lean_ctor_set(v___x_6435_, 1, v_authority_6429_);
                    v___x_6438_ = v___x_6435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6439_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6439_, 0, v_scheme_6430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6439_, 1, v_authority_6429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6439_, 2, v_path_6431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6439_, 3, v_query_6432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6439_, 4, v_fragment_6433_);
                    v___x_6438_ = v_reuseFailAlloc_6439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_withPath(
    mut v_uri_6442_: *mut leanh::LeanObject,
    mut v_path_6443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6454_: u8 = 0;
    let mut v_unused_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6444_ = leanh::lean_ctor_get(v_uri_6442_, 0);
                v_authority_6445_ = leanh::lean_ctor_get(v_uri_6442_, 1);
                v_query_6446_ = leanh::lean_ctor_get(v_uri_6442_, 3);
                v_fragment_6447_ = leanh::lean_ctor_get(v_uri_6442_, 4);
                v_isSharedCheck_6454_ = (!leanh::lean_is_exclusive(v_uri_6442_)) as u8;
                if v_isSharedCheck_6454_ == 0 {
                    v_unused_6455_ = leanh::lean_ctor_get(v_uri_6442_, 2);
                    leanh::lean_dec(v_unused_6455_);
                    v___x_6449_ = v_uri_6442_;
                    v_isShared_6450_ = v_isSharedCheck_6454_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6447_);
                    leanh::lean_inc(v_query_6446_);
                    leanh::lean_inc(v_authority_6445_);
                    leanh::lean_inc(v_scheme_6444_);
                    leanh::lean_dec(v_uri_6442_);
                    v___x_6449_ = leanh::lean_box(0);
                    v_isShared_6450_ = v_isSharedCheck_6454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6450_ == 0 {
                    leanh::lean_ctor_set(v___x_6449_, 2, v_path_6443_);
                    v___x_6452_ = v___x_6449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6453_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 0, v_scheme_6444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 1, v_authority_6445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 2, v_path_6443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 3, v_query_6446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 4, v_fragment_6447_);
                    v___x_6452_ = v_reuseFailAlloc_6453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_withQuery(
    mut v_uri_6456_: *mut leanh::LeanObject,
    mut v_query_6457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6464_: u8 = 0;
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6468_: u8 = 0;
    let mut v_unused_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6458_ = leanh::lean_ctor_get(v_uri_6456_, 0);
                v_authority_6459_ = leanh::lean_ctor_get(v_uri_6456_, 1);
                v_path_6460_ = leanh::lean_ctor_get(v_uri_6456_, 2);
                v_fragment_6461_ = leanh::lean_ctor_get(v_uri_6456_, 4);
                v_isSharedCheck_6468_ = (!leanh::lean_is_exclusive(v_uri_6456_)) as u8;
                if v_isSharedCheck_6468_ == 0 {
                    v_unused_6469_ = leanh::lean_ctor_get(v_uri_6456_, 3);
                    leanh::lean_dec(v_unused_6469_);
                    v___x_6463_ = v_uri_6456_;
                    v_isShared_6464_ = v_isSharedCheck_6468_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6461_);
                    leanh::lean_inc(v_path_6460_);
                    leanh::lean_inc(v_authority_6459_);
                    leanh::lean_inc(v_scheme_6458_);
                    leanh::lean_dec(v_uri_6456_);
                    v___x_6463_ = leanh::lean_box(0);
                    v_isShared_6464_ = v_isSharedCheck_6468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6464_ == 0 {
                    leanh::lean_ctor_set(v___x_6463_, 3, v_query_6457_);
                    v___x_6466_ = v___x_6463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6467_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 0, v_scheme_6458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 1, v_authority_6459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 2, v_path_6460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 3, v_query_6457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 4, v_fragment_6461_);
                    v___x_6466_ = v_reuseFailAlloc_6467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_withFragment(
    mut v_uri_6470_: *mut leanh::LeanObject,
    mut v_fragment_6471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6478_: u8 = 0;
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6482_: u8 = 0;
    let mut v_unused_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6472_ = leanh::lean_ctor_get(v_uri_6470_, 0);
                v_authority_6473_ = leanh::lean_ctor_get(v_uri_6470_, 1);
                v_path_6474_ = leanh::lean_ctor_get(v_uri_6470_, 2);
                v_query_6475_ = leanh::lean_ctor_get(v_uri_6470_, 3);
                v_isSharedCheck_6482_ = (!leanh::lean_is_exclusive(v_uri_6470_)) as u8;
                if v_isSharedCheck_6482_ == 0 {
                    v_unused_6483_ = leanh::lean_ctor_get(v_uri_6470_, 4);
                    leanh::lean_dec(v_unused_6483_);
                    v___x_6477_ = v_uri_6470_;
                    v_isShared_6478_ = v_isSharedCheck_6482_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_query_6475_);
                    leanh::lean_inc(v_path_6474_);
                    leanh::lean_inc(v_authority_6473_);
                    leanh::lean_inc(v_scheme_6472_);
                    leanh::lean_dec(v_uri_6470_);
                    v___x_6477_ = leanh::lean_box(0);
                    v_isShared_6478_ = v_isSharedCheck_6482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6478_ == 0 {
                    leanh::lean_ctor_set(v___x_6477_, 4, v_fragment_6471_);
                    v___x_6480_ = v___x_6477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6481_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_scheme_6472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 1, v_authority_6473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 2, v_path_6474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 3, v_query_6475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 4, v_fragment_6471_);
                    v___x_6480_ = v_reuseFailAlloc_6481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_normalize(
    mut v_uri_6484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scheme_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6492_: u8 = 0;
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scheme_6485_ = leanh::lean_ctor_get(v_uri_6484_, 0);
                v_authority_6486_ = leanh::lean_ctor_get(v_uri_6484_, 1);
                v_path_6487_ = leanh::lean_ctor_get(v_uri_6484_, 2);
                v_query_6488_ = leanh::lean_ctor_get(v_uri_6484_, 3);
                v_fragment_6489_ = leanh::lean_ctor_get(v_uri_6484_, 4);
                v_isSharedCheck_6497_ = (!leanh::lean_is_exclusive(v_uri_6484_)) as u8;
                if v_isSharedCheck_6497_ == 0 {
                    v___x_6491_ = v_uri_6484_;
                    v_isShared_6492_ = v_isSharedCheck_6497_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fragment_6489_);
                    leanh::lean_inc(v_query_6488_);
                    leanh::lean_inc(v_path_6487_);
                    leanh::lean_inc(v_authority_6486_);
                    leanh::lean_inc(v_scheme_6485_);
                    leanh::lean_dec(v_uri_6484_);
                    v___x_6491_ = leanh::lean_box(0);
                    v_isShared_6492_ = v_isSharedCheck_6497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6493_ = l_Std_Http_URI_Path_normalize(v_path_6487_);
                if v_isShared_6492_ == 0 {
                    leanh::lean_ctor_set(v___x_6491_, 2, v___x_6493_);
                    v___x_6495_ = v___x_6491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_scheme_6485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 1, v_authority_6486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 2, v___x_6493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 3, v_query_6488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 4, v_fragment_6489_);
                    v___x_6495_ = v_reuseFailAlloc_6496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_ctorIdx(
    mut v_x_6498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_6498_) {
        0 => {
            let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6499_ = leanh::lean_unsigned_to_nat(0);
            return v___x_6499_;
        }
        1 => {
            let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6500_ = leanh::lean_unsigned_to_nat(1);
            return v___x_6500_;
        }
        2 => {
            let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6501_ = leanh::lean_unsigned_to_nat(2);
            return v___x_6501_;
        }
        _ => {
            let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6502_ = leanh::lean_unsigned_to_nat(3);
            return v___x_6502_;
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_ctorIdx___boxed(
    mut v_x_6503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6504_ = l_Std_Http_RequestTarget_ctorIdx(v_x_6503_);
    leanh::lean_dec(v_x_6503_);
    return v_res_6504_;
}
pub unsafe fn l_Std_Http_RequestTarget_ctorElim___redArg(
    mut v_t_6505_: *mut leanh::LeanObject,
    mut v_k_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_6505_) {
        0 => {
            let mut v_path_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_query_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_path_6507_ = leanh::lean_ctor_get(v_t_6505_, 0);
            leanh::lean_inc_ref(v_path_6507_);
            v_query_6508_ = leanh::lean_ctor_get(v_t_6505_, 1);
            leanh::lean_inc(v_query_6508_);
            leanh::lean_dec_ref_known(v_t_6505_, 2);
            v___x_6509_ = leanh::lean_apply_2(v_k_6506_, v_path_6507_, v_query_6508_);
            return v___x_6509_;
        }
        3 => {
            return v_k_6506_;
        }
        _ => {
            let mut v_uri_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_uri_6510_ = leanh::lean_ctor_get(v_t_6505_, 0);
            leanh::lean_inc_ref(v_uri_6510_);
            leanh::lean_dec(v_t_6505_);
            v___x_6511_ = leanh::lean_apply_1(v_k_6506_, v_uri_6510_);
            return v___x_6511_;
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_ctorElim(
    mut v_motive_6512_: *mut leanh::LeanObject,
    mut v_ctorIdx_6513_: *mut leanh::LeanObject,
    mut v_t_6514_: *mut leanh::LeanObject,
    mut v_h_6515_: *mut leanh::LeanObject,
    mut v_k_6516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6517_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6514_, v_k_6516_);
    return v___x_6517_;
}
pub unsafe fn l_Std_Http_RequestTarget_ctorElim___boxed(
    mut v_motive_6518_: *mut leanh::LeanObject,
    mut v_ctorIdx_6519_: *mut leanh::LeanObject,
    mut v_t_6520_: *mut leanh::LeanObject,
    mut v_h_6521_: *mut leanh::LeanObject,
    mut v_k_6522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6523_ = l_Std_Http_RequestTarget_ctorElim(
        v_motive_6518_,
        v_ctorIdx_6519_,
        v_t_6520_,
        v_h_6521_,
        v_k_6522_,
    );
    leanh::lean_dec(v_ctorIdx_6519_);
    return v_res_6523_;
}
pub unsafe fn l_Std_Http_RequestTarget_originForm_elim___redArg(
    mut v_t_6524_: *mut leanh::LeanObject,
    mut v_originForm_6525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6526_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6524_, v_originForm_6525_);
    return v___x_6526_;
}
pub unsafe fn l_Std_Http_RequestTarget_originForm_elim(
    mut v_motive_6527_: *mut leanh::LeanObject,
    mut v_t_6528_: *mut leanh::LeanObject,
    mut v_h_6529_: *mut leanh::LeanObject,
    mut v_originForm_6530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6531_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6528_, v_originForm_6530_);
    return v___x_6531_;
}
pub unsafe fn l_Std_Http_RequestTarget_absoluteForm_elim___redArg(
    mut v_t_6532_: *mut leanh::LeanObject,
    mut v_absoluteForm_6533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6532_, v_absoluteForm_6533_);
    return v___x_6534_;
}
pub unsafe fn l_Std_Http_RequestTarget_absoluteForm_elim(
    mut v_motive_6535_: *mut leanh::LeanObject,
    mut v_t_6536_: *mut leanh::LeanObject,
    mut v_h_6537_: *mut leanh::LeanObject,
    mut v_absoluteForm_6538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6539_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6536_, v_absoluteForm_6538_);
    return v___x_6539_;
}
pub unsafe fn l_Std_Http_RequestTarget_authorityForm_elim___redArg(
    mut v_t_6540_: *mut leanh::LeanObject,
    mut v_authorityForm_6541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6542_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6540_, v_authorityForm_6541_);
    return v___x_6542_;
}
pub unsafe fn l_Std_Http_RequestTarget_authorityForm_elim(
    mut v_motive_6543_: *mut leanh::LeanObject,
    mut v_t_6544_: *mut leanh::LeanObject,
    mut v_h_6545_: *mut leanh::LeanObject,
    mut v_authorityForm_6546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6547_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6544_, v_authorityForm_6546_);
    return v___x_6547_;
}
pub unsafe fn l_Std_Http_RequestTarget_asteriskForm_elim___redArg(
    mut v_t_6548_: *mut leanh::LeanObject,
    mut v_asteriskForm_6549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6550_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6548_, v_asteriskForm_6549_);
    return v___x_6550_;
}
pub unsafe fn l_Std_Http_RequestTarget_asteriskForm_elim(
    mut v_motive_6551_: *mut leanh::LeanObject,
    mut v_t_6552_: *mut leanh::LeanObject,
    mut v_h_6553_: *mut leanh::LeanObject,
    mut v_asteriskForm_6554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6555_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_6552_, v_asteriskForm_6554_);
    return v___x_6555_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(
    mut v_x_6561_: *mut leanh::LeanObject,
    mut v_x_6562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6561_) == 0 {
        let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6563_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1;
        return v___x_6563_;
    } else {
        let mut v_val_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6564_ = leanh::lean_ctor_get(v_x_6561_, 0);
        leanh::lean_inc(v_val_6564_);
        leanh::lean_dec_ref_known(v_x_6561_, 1);
        v___x_6565_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3;
        v___x_6566_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_6564_);
        v___x_6567_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6567_, 0, v___x_6565_);
        leanh::lean_ctor_set(v___x_6567_, 1, v___x_6566_);
        v___x_6568_ = l_Repr_addAppParen(v___x_6567_, v_x_6562_);
        return v___x_6568_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(
    mut v_x_6569_: *mut leanh::LeanObject,
    mut v_x_6570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6571_ =
        l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_x_6569_, v_x_6570_);
    leanh::lean_dec(v_x_6570_);
    return v_res_6571_;
}
pub unsafe fn l_Std_Http_instReprRequestTarget_repr(
    mut v_x_6593_: *mut leanh::LeanObject,
    mut v_prec_6594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: u8 = 0;
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6606_: u8 = 0;
    let mut v___y_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: u8 = 0;
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: u8 = 0;
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut v_uri_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: u8 = 0;
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: u8 = 0;
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: u8 = 0;
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: u8 = 0;
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: u8 = 0;
    let mut v___x_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_6593_) {
                0 => {
                    v_path_6602_ = leanh::lean_ctor_get(v_x_6593_, 0);
                    v_query_6603_ = leanh::lean_ctor_get(v_x_6593_, 1);
                    v_isSharedCheck_6627_ = (!leanh::lean_is_exclusive(v_x_6593_)) as u8;
                    if v_isSharedCheck_6627_ == 0 {
                        v___x_6605_ = v_x_6593_;
                        v_isShared_6606_ = v_isSharedCheck_6627_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_query_6603_);
                        leanh::lean_inc(v_path_6602_);
                        leanh::lean_dec(v_x_6593_);
                        v___x_6605_ = leanh::lean_box(0);
                        v_isShared_6606_ = v_isSharedCheck_6627_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_uri_6628_ = leanh::lean_ctor_get(v_x_6593_, 0);
                    leanh::lean_inc_ref(v_uri_6628_);
                    leanh::lean_dec_ref_known(v_x_6593_, 1);
                    v___x_6638_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_6639_ = lean_nat_dec_le(v___x_6638_, v_prec_6594_);
                    if v___x_6639_ == 0 {
                        v___x_6640_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_6630_ = v___x_6640_;
                        state = 5;
                        continue;
                    } else {
                        v___x_6641_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_6630_ = v___x_6641_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_authority_6642_ = leanh::lean_ctor_get(v_x_6593_, 0);
                    leanh::lean_inc_ref(v_authority_6642_);
                    leanh::lean_dec_ref_known(v_x_6593_, 1);
                    v___x_6652_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_6653_ = lean_nat_dec_le(v___x_6652_, v_prec_6594_);
                    if v___x_6653_ == 0 {
                        v___x_6654_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_6644_ = v___x_6654_;
                        state = 6;
                        continue;
                    } else {
                        v___x_6655_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_6644_ = v___x_6655_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v___x_6656_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_6657_ = lean_nat_dec_le(v___x_6656_, v_prec_6594_);
                    if v___x_6657_ == 0 {
                        v___x_6658_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                        );
                        v___y_6596_ = v___x_6658_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6659_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                            ),
                            _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                        );
                        v___y_6596_ = v___x_6659_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_6597_ = l_Std_Http_instReprRequestTarget_repr___closed__1;
                leanh::lean_inc(v___y_6596_);
                v___x_6598_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6598_, 0, v___y_6596_);
                leanh::lean_ctor_set(v___x_6598_, 1, v___x_6597_);
                v___x_6599_ = 0;
                v___x_6600_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_6600_, 0, v___x_6598_);
                leanh::lean_ctor_set_uint8(
                    v___x_6600_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6599_,
                );
                v___x_6601_ = l_Repr_addAppParen(v___x_6600_, v_prec_6594_);
                return v___x_6601_;
            }
            2 => {
                v___x_6623_ = leanh::lean_unsigned_to_nat(1024);
                v___x_6624_ = lean_nat_dec_le(v___x_6623_, v_prec_6594_);
                if v___x_6624_ == 0 {
                    v___x_6625_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instReprHost___lam__0___closed__4_once
                        ),
                        _init_l_Std_Http_URI_instReprHost___lam__0___closed__4,
                    );
                    v___y_6608_ = v___x_6625_;
                    state = 3;
                    continue;
                } else {
                    v___x_6626_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_instReprHost___lam__0___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_instReprHost___lam__0___closed__5_once
                        ),
                        _init_l_Std_Http_URI_instReprHost___lam__0___closed__5,
                    );
                    v___y_6608_ = v___x_6626_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6609_ = leanh::lean_box(1);
                v___x_6610_ = l_Std_Http_instReprRequestTarget_repr___closed__4;
                v___x_6611_ = leanh::lean_unsigned_to_nat(1024);
                v___x_6612_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_6602_);
                if v_isShared_6606_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6605_, 5);
                    leanh::lean_ctor_set(v___x_6605_, 1, v___x_6612_);
                    leanh::lean_ctor_set(v___x_6605_, 0, v___x_6610_);
                    v___x_6614_ = v___x_6605_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6622_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___x_6610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6622_, 1, v___x_6612_);
                    v___x_6614_ = v_reuseFailAlloc_6622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6615_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6615_, 0, v___x_6614_);
                leanh::lean_ctor_set(v___x_6615_, 1, v___x_6609_);
                v___x_6616_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(
                    v_query_6603_,
                    v___x_6611_,
                );
                v___x_6617_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6617_, 0, v___x_6615_);
                leanh::lean_ctor_set(v___x_6617_, 1, v___x_6616_);
                leanh::lean_inc(v___y_6608_);
                v___x_6618_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6618_, 0, v___y_6608_);
                leanh::lean_ctor_set(v___x_6618_, 1, v___x_6617_);
                v___x_6619_ = 0;
                v___x_6620_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_6620_, 0, v___x_6618_);
                leanh::lean_ctor_set_uint8(
                    v___x_6620_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6619_,
                );
                v___x_6621_ = l_Repr_addAppParen(v___x_6620_, v_prec_6594_);
                return v___x_6621_;
            }
            5 => {
                v___x_6631_ = l_Std_Http_instReprRequestTarget_repr___closed__7;
                v___x_6632_ = l_Std_Http_instReprURI_repr___redArg(v_uri_6628_);
                v___x_6633_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6633_, 0, v___x_6631_);
                leanh::lean_ctor_set(v___x_6633_, 1, v___x_6632_);
                leanh::lean_inc(v___y_6630_);
                v___x_6634_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6634_, 0, v___y_6630_);
                leanh::lean_ctor_set(v___x_6634_, 1, v___x_6633_);
                v___x_6635_ = 0;
                v___x_6636_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_6636_, 0, v___x_6634_);
                leanh::lean_ctor_set_uint8(
                    v___x_6636_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6635_,
                );
                v___x_6637_ = l_Repr_addAppParen(v___x_6636_, v_prec_6594_);
                return v___x_6637_;
            }
            6 => {
                v___x_6645_ = l_Std_Http_instReprRequestTarget_repr___closed__10;
                v___x_6646_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_6642_);
                v___x_6647_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6647_, 0, v___x_6645_);
                leanh::lean_ctor_set(v___x_6647_, 1, v___x_6646_);
                leanh::lean_inc(v___y_6644_);
                v___x_6648_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6648_, 0, v___y_6644_);
                leanh::lean_ctor_set(v___x_6648_, 1, v___x_6647_);
                v___x_6649_ = 0;
                v___x_6650_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_6650_, 0, v___x_6648_);
                leanh::lean_ctor_set_uint8(
                    v___x_6650_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6649_,
                );
                v___x_6651_ = l_Repr_addAppParen(v___x_6650_, v_prec_6594_);
                return v___x_6651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instReprRequestTarget_repr___boxed(
    mut v_x_6660_: *mut leanh::LeanObject,
    mut v_prec_6661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6662_ = l_Std_Http_instReprRequestTarget_repr(v_x_6660_, v_prec_6661_);
    leanh::lean_dec(v_prec_6661_);
    return v_res_6662_;
}
pub unsafe fn l_Std_Http_RequestTarget_path(
    mut v_x_6670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_6670_) {
        0 => {
            let mut v_path_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_path_6671_ = leanh::lean_ctor_get(v_x_6670_, 0);
            leanh::lean_inc_ref(v_path_6671_);
            return v_path_6671_;
        }
        1 => {
            let mut v_uri_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_path_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_uri_6672_ = leanh::lean_ctor_get(v_x_6670_, 0);
            v_path_6673_ = leanh::lean_ctor_get(v_uri_6672_, 2);
            leanh::lean_inc_ref(v_path_6673_);
            return v_path_6673_;
        }
        _ => {
            let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6674_ = l_Std_Http_RequestTarget_path___closed__1;
            return v___x_6674_;
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_path___boxed(
    mut v_x_6675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6676_ = l_Std_Http_RequestTarget_path(v_x_6675_);
    leanh::lean_dec(v_x_6675_);
    return v_res_6676_;
}
pub unsafe fn l_Std_Http_RequestTarget_query(
    mut v_x_6677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_6677_) {
        0 => {
            let mut v_query_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_query_6678_ = leanh::lean_ctor_get(v_x_6677_, 1);
            if leanh::lean_obj_tag(v_query_6678_) == 0 {
                let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6679_ = l_Std_Http_URI_Query_empty;
                return v___x_6679_;
            } else {
                let mut v_val_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_val_6680_ = leanh::lean_ctor_get(v_query_6678_, 0);
                leanh::lean_inc(v_val_6680_);
                return v_val_6680_;
            }
        }
        1 => {
            let mut v_uri_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_query_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_uri_6681_ = leanh::lean_ctor_get(v_x_6677_, 0);
            v_query_6682_ = leanh::lean_ctor_get(v_uri_6681_, 3);
            leanh::lean_inc_ref(v_query_6682_);
            return v_query_6682_;
        }
        _ => {
            let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6683_ = l_Std_Http_URI_Query_empty;
            return v___x_6683_;
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_query___boxed(
    mut v_x_6684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6685_ = l_Std_Http_RequestTarget_query(v_x_6684_);
    leanh::lean_dec(v_x_6684_);
    return v_res_6685_;
}
pub unsafe fn l_Std_Http_RequestTarget_authority_x3f(
    mut v_x_6686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_authority_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6690_: u8 = 0;
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6694_: u8 = 0;
    let mut v_uri_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_6686_) {
                2 => {
                    v_authority_6687_ = leanh::lean_ctor_get(v_x_6686_, 0);
                    v_isSharedCheck_6694_ = (!leanh::lean_is_exclusive(v_x_6686_)) as u8;
                    if v_isSharedCheck_6694_ == 0 {
                        v___x_6689_ = v_x_6686_;
                        v_isShared_6690_ = v_isSharedCheck_6694_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_authority_6687_);
                        leanh::lean_dec(v_x_6686_);
                        v___x_6689_ = leanh::lean_box(0);
                        v_isShared_6690_ = v_isSharedCheck_6694_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_uri_6695_ = leanh::lean_ctor_get(v_x_6686_, 0);
                    leanh::lean_inc_ref(v_uri_6695_);
                    leanh::lean_dec_ref_known(v_x_6686_, 1);
                    v_authority_6696_ = leanh::lean_ctor_get(v_uri_6695_, 1);
                    leanh::lean_inc(v_authority_6696_);
                    leanh::lean_dec_ref(v_uri_6695_);
                    return v_authority_6696_;
                }
                _ => {
                    leanh::lean_dec(v_x_6686_);
                    v___x_6697_ = leanh::lean_box(0);
                    return v___x_6697_;
                }
            },
            1 => {
                if v_isShared_6690_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6689_, 1);
                    v___x_6692_ = v___x_6689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6693_, 0, v_authority_6687_);
                    v___x_6692_ = v_reuseFailAlloc_6693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_instToString___lam__4(
    mut v___f_6699_: *mut leanh::LeanObject,
    mut v___f_6700_: *mut leanh::LeanObject,
    mut v___f_6701_: *mut leanh::LeanObject,
    mut v___f_6702_: *mut leanh::LeanObject,
    mut v_x_6703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: u8 = 0;
    let mut v___x_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_6727_: u8 = 0;
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6730_: usize = 0;
    let mut v___x_6731_: usize = 0;
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: u8 = 0;
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_6780_: u8 = 0;
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6783_: usize = 0;
    let mut v___x_6784_: usize = 0;
    let mut v___x_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6807_: u16 = 0;
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6848_: u16 = 0;
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_6703_) {
                0 => {
                    leanh::lean_dec_ref(v___f_6702_);
                    leanh::lean_dec_ref(v___f_6701_);
                    v_path_6710_ = leanh::lean_ctor_get(v_x_6703_, 0);
                    leanh::lean_inc_ref(v_path_6710_);
                    v_query_6711_ = leanh::lean_ctor_get(v_x_6703_, 1);
                    leanh::lean_inc(v_query_6711_);
                    leanh::lean_dec_ref_known(v_x_6703_, 2);
                    v_segments_6726_ = leanh::lean_ctor_get(v_path_6710_, 0);
                    leanh::lean_inc_ref(v_segments_6726_);
                    v_absolute_6727_ = leanh::lean_ctor_get_uint8(
                        v_path_6710_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref(v_path_6710_);
                    v___x_6728_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
                    v___x_6729_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
                    v_sz_6730_ = lean_array_size(v_segments_6726_);
                    v___x_6731_ = 0usize;
                    v___x_6732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6729_,
                        v___f_6700_,
                        v_sz_6730_,
                        v___x_6731_,
                        v_segments_6726_,
                    );
                    v___x_6733_ = lean_array_to_list(v___x_6732_);
                    v_result_6734_ = l_String_intercalate(v___x_6728_, v___x_6733_);
                    if v_absolute_6727_ == 0 {
                        v___y_6713_ = v_result_6734_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6735_ = lean_string_append(v___x_6728_, v_result_6734_);
                        leanh::lean_dec_ref(v_result_6734_);
                        v___y_6713_ = v___x_6735_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec_ref(v___f_6700_);
                    leanh::lean_dec_ref(v___f_6699_);
                    v_uri_6736_ = leanh::lean_ctor_get(v_x_6703_, 0);
                    leanh::lean_inc_ref(v_uri_6736_);
                    leanh::lean_dec_ref_known(v_x_6703_, 1);
                    v_scheme_6737_ = leanh::lean_ctor_get(v_uri_6736_, 0);
                    leanh::lean_inc_ref(v_scheme_6737_);
                    v_authority_6738_ = leanh::lean_ctor_get(v_uri_6736_, 1);
                    leanh::lean_inc(v_authority_6738_);
                    v_path_6739_ = leanh::lean_ctor_get(v_uri_6736_, 2);
                    leanh::lean_inc_ref(v_path_6739_);
                    v_query_6740_ = leanh::lean_ctor_get(v_uri_6736_, 3);
                    leanh::lean_inc_ref(v_query_6740_);
                    v_fragment_6741_ = leanh::lean_ctor_get(v_uri_6736_, 4);
                    leanh::lean_inc(v_fragment_6741_);
                    leanh::lean_dec_ref(v_uri_6736_);
                    if leanh::lean_obj_tag(v_authority_6738_) == 0 {
                        v___x_6789_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                        v___y_6778_ = v___x_6789_;
                        state = 6;
                        continue;
                    } else {
                        v_val_6790_ = leanh::lean_ctor_get(v_authority_6738_, 0);
                        leanh::lean_inc(v_val_6790_);
                        leanh::lean_dec_ref_known(v_authority_6738_, 1);
                        v_userInfo_6791_ = leanh::lean_ctor_get(v_val_6790_, 0);
                        leanh::lean_inc(v_userInfo_6791_);
                        v_host_6792_ = leanh::lean_ctor_get(v_val_6790_, 1);
                        leanh::lean_inc_ref(v_host_6792_);
                        v_port_6793_ = leanh::lean_ctor_get(v_val_6790_, 2);
                        leanh::lean_inc(v_port_6793_);
                        leanh::lean_dec(v_val_6790_);
                        v___x_6794_ = l_Std_Http_instToStringURI___lam__2___closed__1;
                        if leanh::lean_obj_tag(v_userInfo_6791_) == 0 {
                            v___x_6823_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                            v___y_6813_ = v___x_6823_;
                            state = 9;
                            continue;
                        } else {
                            v_val_6824_ = leanh::lean_ctor_get(v_userInfo_6791_, 0);
                            leanh::lean_inc(v_val_6824_);
                            leanh::lean_dec_ref_known(v_userInfo_6791_, 1);
                            v_password_6825_ = leanh::lean_ctor_get(v_val_6824_, 1);
                            if leanh::lean_obj_tag(v_password_6825_) == 0 {
                                v_username_6826_ = leanh::lean_ctor_get(v_val_6824_, 0);
                                leanh::lean_inc_ref(v_username_6826_);
                                leanh::lean_dec(v_val_6824_);
                                v___x_6827_ = lean_string_from_utf8_unchecked(v_username_6826_);
                                v___x_6828_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                                v___x_6829_ = lean_string_append(v___x_6827_, v___x_6828_);
                                v___y_6813_ = v___x_6829_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_password_6825_);
                                v_username_6830_ = leanh::lean_ctor_get(v_val_6824_, 0);
                                leanh::lean_inc_ref(v_username_6830_);
                                leanh::lean_dec(v_val_6824_);
                                v_val_6831_ = leanh::lean_ctor_get(v_password_6825_, 0);
                                leanh::lean_inc(v_val_6831_);
                                leanh::lean_dec_ref_known(v_password_6825_, 1);
                                v___x_6832_ = lean_string_from_utf8_unchecked(v_username_6830_);
                                v___x_6833_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                                v___x_6834_ = lean_string_append(v___x_6832_, v___x_6833_);
                                v___x_6835_ = lean_string_from_utf8_unchecked(v_val_6831_);
                                v___x_6836_ = lean_string_append(v___x_6834_, v___x_6835_);
                                leanh::lean_dec_ref(v___x_6835_);
                                v___x_6837_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                                v___x_6838_ = lean_string_append(v___x_6836_, v___x_6837_);
                                v___y_6813_ = v___x_6838_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
                2 => {
                    leanh::lean_dec_ref(v___f_6702_);
                    leanh::lean_dec_ref(v___f_6701_);
                    leanh::lean_dec_ref(v___f_6700_);
                    leanh::lean_dec_ref(v___f_6699_);
                    v_authority_6839_ = leanh::lean_ctor_get(v_x_6703_, 0);
                    leanh::lean_inc_ref(v_authority_6839_);
                    leanh::lean_dec_ref_known(v_x_6703_, 1);
                    v_userInfo_6840_ = leanh::lean_ctor_get(v_authority_6839_, 0);
                    leanh::lean_inc(v_userInfo_6840_);
                    v_host_6841_ = leanh::lean_ctor_get(v_authority_6839_, 1);
                    leanh::lean_inc_ref(v_host_6841_);
                    v_port_6842_ = leanh::lean_ctor_get(v_authority_6839_, 2);
                    leanh::lean_inc(v_port_6842_);
                    leanh::lean_dec_ref(v_authority_6839_);
                    if leanh::lean_obj_tag(v_userInfo_6840_) == 0 {
                        v___x_6864_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                        v___y_6854_ = v___x_6864_;
                        state = 11;
                        continue;
                    } else {
                        v_val_6865_ = leanh::lean_ctor_get(v_userInfo_6840_, 0);
                        leanh::lean_inc(v_val_6865_);
                        leanh::lean_dec_ref_known(v_userInfo_6840_, 1);
                        v_password_6866_ = leanh::lean_ctor_get(v_val_6865_, 1);
                        if leanh::lean_obj_tag(v_password_6866_) == 0 {
                            v_username_6867_ = leanh::lean_ctor_get(v_val_6865_, 0);
                            leanh::lean_inc_ref(v_username_6867_);
                            leanh::lean_dec(v_val_6865_);
                            v___x_6868_ = lean_string_from_utf8_unchecked(v_username_6867_);
                            v___x_6869_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_6870_ = lean_string_append(v___x_6868_, v___x_6869_);
                            v___y_6854_ = v___x_6870_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_password_6866_);
                            v_username_6871_ = leanh::lean_ctor_get(v_val_6865_, 0);
                            leanh::lean_inc_ref(v_username_6871_);
                            leanh::lean_dec(v_val_6865_);
                            v_val_6872_ = leanh::lean_ctor_get(v_password_6866_, 0);
                            leanh::lean_inc(v_val_6872_);
                            leanh::lean_dec_ref_known(v_password_6866_, 1);
                            v___x_6873_ = lean_string_from_utf8_unchecked(v_username_6871_);
                            v___x_6874_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                            v___x_6875_ = lean_string_append(v___x_6873_, v___x_6874_);
                            v___x_6876_ = lean_string_from_utf8_unchecked(v_val_6872_);
                            v___x_6877_ = lean_string_append(v___x_6875_, v___x_6876_);
                            leanh::lean_dec_ref(v___x_6876_);
                            v___x_6878_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_6879_ = lean_string_append(v___x_6877_, v___x_6878_);
                            v___y_6854_ = v___x_6879_;
                            state = 11;
                            continue;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v___f_6702_);
                    leanh::lean_dec_ref(v___f_6701_);
                    leanh::lean_dec_ref(v___f_6700_);
                    leanh::lean_dec_ref(v___f_6699_);
                    v___x_6880_ = l_Std_Http_RequestTarget_instToString___lam__4___closed__0;
                    return v___x_6880_;
                }
            },
            1 => {
                v___x_6708_ = lean_string_append(v___y_6706_, v___y_6705_);
                leanh::lean_dec_ref(v___y_6705_);
                v___x_6709_ = lean_string_append(v___x_6708_, v___y_6707_);
                leanh::lean_dec_ref(v___y_6707_);
                return v___x_6709_;
            }
            2 => {
                if leanh::lean_obj_tag(v_query_6711_) == 0 {
                    leanh::lean_dec_ref(v___f_6699_);
                    return v___y_6713_;
                } else {
                    v_val_6714_ = leanh::lean_ctor_get(v_query_6711_, 0);
                    leanh::lean_inc(v_val_6714_);
                    leanh::lean_dec_ref_known(v_query_6711_, 1);
                    v___x_6715_ = lean_array_get_size(v_val_6714_);
                    v___x_6716_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6717_ = lean_nat_dec_eq(v___x_6715_, v___x_6716_);
                    if v___x_6717_ == 0 {
                        v___x_6718_ = lean_array_to_list(v_val_6714_);
                        v___x_6719_ = leanh::lean_box(0);
                        v_encodedParams_6720_ =
                            l_List_mapTR_loop___redArg(v___f_6699_, v___x_6718_, v___x_6719_);
                        v___x_6721_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
                        v___x_6722_ = l_Std_Http_URI_Query_toRawString___closed__0;
                        v___x_6723_ = l_String_intercalate(v___x_6722_, v_encodedParams_6720_);
                        v___x_6724_ = lean_string_append(v___x_6721_, v___x_6723_);
                        leanh::lean_dec_ref(v___x_6723_);
                        v___x_6725_ = lean_string_append(v___y_6713_, v___x_6724_);
                        leanh::lean_dec_ref(v___x_6724_);
                        return v___x_6725_;
                    } else {
                        leanh::lean_dec(v_val_6714_);
                        leanh::lean_dec_ref(v___f_6699_);
                        return v___y_6713_;
                    }
                }
            }
            3 => {
                v___x_6747_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                v___x_6748_ = lean_string_append(v_scheme_6737_, v___x_6747_);
                v___x_6749_ = lean_string_append(v___x_6748_, v___y_6745_);
                leanh::lean_dec_ref(v___y_6745_);
                v___x_6750_ = lean_string_append(v___x_6749_, v___y_6743_);
                leanh::lean_dec_ref(v___y_6743_);
                v___x_6751_ = lean_string_append(v___x_6750_, v___y_6744_);
                leanh::lean_dec_ref(v___y_6744_);
                v___x_6752_ = lean_string_append(v___x_6751_, v___y_6746_);
                leanh::lean_dec_ref(v___y_6746_);
                return v___x_6752_;
            }
            4 => {
                if leanh::lean_obj_tag(v_fragment_6741_) == 0 {
                    v___x_6757_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6743_ = v___y_6754_;
                    v___y_6744_ = v___y_6756_;
                    v___y_6745_ = v___y_6755_;
                    v___y_6746_ = v___x_6757_;
                    state = 3;
                    continue;
                } else {
                    v_val_6758_ = leanh::lean_ctor_get(v_fragment_6741_, 0);
                    leanh::lean_inc(v_val_6758_);
                    leanh::lean_dec_ref_known(v_fragment_6741_, 1);
                    v___x_6759_ = l_Std_Http_instToStringURI___lam__2___closed__0;
                    v___x_6760_ = l_Std_Http_URI_EncodedFragment_encode(v_val_6758_);
                    leanh::lean_dec(v_val_6758_);
                    v___x_6761_ = lean_string_from_utf8_unchecked(v___x_6760_);
                    v___x_6762_ = lean_string_append(v___x_6759_, v___x_6761_);
                    leanh::lean_dec_ref(v___x_6761_);
                    v___y_6743_ = v___y_6754_;
                    v___y_6744_ = v___y_6756_;
                    v___y_6745_ = v___y_6755_;
                    v___y_6746_ = v___x_6762_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_6766_ = lean_array_get_size(v_query_6740_);
                v___x_6767_ = leanh::lean_unsigned_to_nat(0);
                v___x_6768_ = lean_nat_dec_eq(v___x_6766_, v___x_6767_);
                if v___x_6768_ == 0 {
                    v___x_6769_ = lean_array_to_list(v_query_6740_);
                    v___x_6770_ = leanh::lean_box(0);
                    v_encodedParams_6771_ =
                        l_List_mapTR_loop___redArg(v___f_6701_, v___x_6769_, v___x_6770_);
                    v___x_6772_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
                    v___x_6773_ = l_Std_Http_URI_Query_toRawString___closed__0;
                    v___x_6774_ = l_String_intercalate(v___x_6773_, v_encodedParams_6771_);
                    v___x_6775_ = lean_string_append(v___x_6772_, v___x_6774_);
                    leanh::lean_dec_ref(v___x_6774_);
                    v___y_6754_ = v___y_6765_;
                    v___y_6755_ = v___y_6764_;
                    v___y_6756_ = v___x_6775_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_query_6740_);
                    leanh::lean_dec_ref(v___f_6701_);
                    v___x_6776_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6754_ = v___y_6765_;
                    v___y_6755_ = v___y_6764_;
                    v___y_6756_ = v___x_6776_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_segments_6779_ = leanh::lean_ctor_get(v_path_6739_, 0);
                leanh::lean_inc_ref(v_segments_6779_);
                v_absolute_6780_ = leanh::lean_ctor_get_uint8(
                    v_path_6739_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_path_6739_);
                v___x_6781_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
                v___x_6782_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
                v_sz_6783_ = lean_array_size(v_segments_6779_);
                v___x_6784_ = 0usize;
                v___x_6785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_6782_,
                    v___f_6702_,
                    v_sz_6783_,
                    v___x_6784_,
                    v_segments_6779_,
                );
                v___x_6786_ = lean_array_to_list(v___x_6785_);
                v_result_6787_ = l_String_intercalate(v___x_6781_, v___x_6786_);
                if v_absolute_6780_ == 0 {
                    v___y_6764_ = v___y_6778_;
                    v___y_6765_ = v_result_6787_;
                    state = 5;
                    continue;
                } else {
                    v___x_6788_ = lean_string_append(v___x_6781_, v_result_6787_);
                    leanh::lean_dec_ref(v_result_6787_);
                    v___y_6764_ = v___y_6778_;
                    v___y_6765_ = v___x_6788_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_6799_ = lean_string_append(v___y_6797_, v___y_6796_);
                leanh::lean_dec_ref(v___y_6796_);
                v___x_6800_ = lean_string_append(v___x_6799_, v___y_6798_);
                leanh::lean_dec_ref(v___y_6798_);
                v___x_6801_ = lean_string_append(v___x_6794_, v___x_6800_);
                leanh::lean_dec_ref(v___x_6800_);
                v___y_6778_ = v___x_6801_;
                state = 6;
                continue;
            }
            8 => match leanh::lean_obj_tag(v_port_6793_) {
                0 => {
                    v___x_6805_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6796_ = v___y_6804_;
                    v___y_6797_ = v___y_6803_;
                    v___y_6798_ = v___x_6805_;
                    state = 7;
                    continue;
                }
                1 => {
                    v___x_6806_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_6796_ = v___y_6804_;
                    v___y_6797_ = v___y_6803_;
                    v___y_6798_ = v___x_6806_;
                    state = 7;
                    continue;
                }
                _ => {
                    v_port_6807_ = leanh::lean_ctor_get_uint16(v_port_6793_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_6793_, 0);
                    v___x_6808_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_6809_ = lean_uint16_to_nat(v_port_6807_);
                    v___x_6810_ = l_Nat_reprFast(v___x_6809_);
                    v___x_6811_ = lean_string_append(v___x_6808_, v___x_6810_);
                    leanh::lean_dec_ref(v___x_6810_);
                    v___y_6796_ = v___y_6804_;
                    v___y_6797_ = v___y_6803_;
                    v___y_6798_ = v___x_6811_;
                    state = 7;
                    continue;
                }
            },
            9 => match leanh::lean_obj_tag(v_host_6792_) {
                0 => {
                    v_name_6814_ = leanh::lean_ctor_get(v_host_6792_, 0);
                    leanh::lean_inc_ref(v_name_6814_);
                    leanh::lean_dec_ref_known(v_host_6792_, 1);
                    v___y_6803_ = v___y_6813_;
                    v___y_6804_ = v_name_6814_;
                    state = 8;
                    continue;
                }
                1 => {
                    v_ipv4_6815_ = leanh::lean_ctor_get(v_host_6792_, 0);
                    leanh::lean_inc_ref(v_ipv4_6815_);
                    leanh::lean_dec_ref_known(v_host_6792_, 1);
                    v___x_6816_ = lean_uv_ntop_v4(v_ipv4_6815_);
                    leanh::lean_dec_ref(v_ipv4_6815_);
                    v___y_6803_ = v___y_6813_;
                    v___y_6804_ = v___x_6816_;
                    state = 8;
                    continue;
                }
                _ => {
                    v_ipv6_6817_ = leanh::lean_ctor_get(v_host_6792_, 0);
                    leanh::lean_inc_ref(v_ipv6_6817_);
                    leanh::lean_dec_ref_known(v_host_6792_, 1);
                    v___x_6818_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_6819_ = lean_uv_ntop_v6(v_ipv6_6817_);
                    leanh::lean_dec_ref(v_ipv6_6817_);
                    v___x_6820_ = lean_string_append(v___x_6818_, v___x_6819_);
                    leanh::lean_dec_ref(v___x_6819_);
                    v___x_6821_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_6822_ = lean_string_append(v___x_6820_, v___x_6821_);
                    v___y_6803_ = v___y_6813_;
                    v___y_6804_ = v___x_6822_;
                    state = 8;
                    continue;
                }
            },
            10 => match leanh::lean_obj_tag(v_port_6842_) {
                0 => {
                    v___x_6846_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6705_ = v___y_6845_;
                    v___y_6706_ = v___y_6844_;
                    v___y_6707_ = v___x_6846_;
                    state = 1;
                    continue;
                }
                1 => {
                    v___x_6847_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_6705_ = v___y_6845_;
                    v___y_6706_ = v___y_6844_;
                    v___y_6707_ = v___x_6847_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_port_6848_ = leanh::lean_ctor_get_uint16(v_port_6842_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_6842_, 0);
                    v___x_6849_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_6850_ = lean_uint16_to_nat(v_port_6848_);
                    v___x_6851_ = l_Nat_reprFast(v___x_6850_);
                    v___x_6852_ = lean_string_append(v___x_6849_, v___x_6851_);
                    leanh::lean_dec_ref(v___x_6851_);
                    v___y_6705_ = v___y_6845_;
                    v___y_6706_ = v___y_6844_;
                    v___y_6707_ = v___x_6852_;
                    state = 1;
                    continue;
                }
            },
            11 => match leanh::lean_obj_tag(v_host_6841_) {
                0 => {
                    v_name_6855_ = leanh::lean_ctor_get(v_host_6841_, 0);
                    leanh::lean_inc_ref(v_name_6855_);
                    leanh::lean_dec_ref_known(v_host_6841_, 1);
                    v___y_6844_ = v___y_6854_;
                    v___y_6845_ = v_name_6855_;
                    state = 10;
                    continue;
                }
                1 => {
                    v_ipv4_6856_ = leanh::lean_ctor_get(v_host_6841_, 0);
                    leanh::lean_inc_ref(v_ipv4_6856_);
                    leanh::lean_dec_ref_known(v_host_6841_, 1);
                    v___x_6857_ = lean_uv_ntop_v4(v_ipv4_6856_);
                    leanh::lean_dec_ref(v_ipv4_6856_);
                    v___y_6844_ = v___y_6854_;
                    v___y_6845_ = v___x_6857_;
                    state = 10;
                    continue;
                }
                _ => {
                    v_ipv6_6858_ = leanh::lean_ctor_get(v_host_6841_, 0);
                    leanh::lean_inc_ref(v_ipv6_6858_);
                    leanh::lean_dec_ref_known(v_host_6841_, 1);
                    v___x_6859_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_6860_ = lean_uv_ntop_v6(v_ipv6_6858_);
                    leanh::lean_dec_ref(v_ipv6_6858_);
                    v___x_6861_ = lean_string_append(v___x_6859_, v___x_6860_);
                    leanh::lean_dec_ref(v___x_6860_);
                    v___x_6862_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_6863_ = lean_string_append(v___x_6861_, v___x_6862_);
                    v___y_6844_ = v___y_6854_;
                    v___y_6845_ = v___x_6863_;
                    state = 10;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_instEncodeV11___lam__4(
    mut v___f_6885_: *mut leanh::LeanObject,
    mut v___f_6886_: *mut leanh::LeanObject,
    mut v___f_6887_: *mut leanh::LeanObject,
    mut v___f_6888_: *mut leanh::LeanObject,
    mut v_buffer_6889_: *mut leanh::LeanObject,
    mut v_target_6890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6897_: u8 = 0;
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6905_: u8 = 0;
    let mut v___y_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: u8 = 0;
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_6929_: u8 = 0;
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6932_: usize = 0;
    let mut v___x_6933_: usize = 0;
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scheme_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_query_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fragment_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_encodedParams_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_segments_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_absolute_6982_: u8 = 0;
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6985_: usize = 0;
    let mut v___x_6986_: usize = 0;
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_7009_: u16 = 0;
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_authority_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userInfo_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_host_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_port_7050_: u16 = 0;
    let mut v___x_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv4_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ipv6_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_password_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_target_6890_) {
                0 => {
                    leanh::lean_dec_ref(v___f_6888_);
                    leanh::lean_dec_ref(v___f_6887_);
                    v_path_6912_ = leanh::lean_ctor_get(v_target_6890_, 0);
                    leanh::lean_inc_ref(v_path_6912_);
                    v_query_6913_ = leanh::lean_ctor_get(v_target_6890_, 1);
                    leanh::lean_inc(v_query_6913_);
                    leanh::lean_dec_ref_known(v_target_6890_, 2);
                    v_segments_6928_ = leanh::lean_ctor_get(v_path_6912_, 0);
                    leanh::lean_inc_ref(v_segments_6928_);
                    v_absolute_6929_ = leanh::lean_ctor_get_uint8(
                        v_path_6912_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref(v_path_6912_);
                    v___x_6930_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
                    v___x_6931_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
                    v_sz_6932_ = lean_array_size(v_segments_6928_);
                    v___x_6933_ = 0usize;
                    v___x_6934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6931_,
                        v___f_6886_,
                        v_sz_6932_,
                        v___x_6933_,
                        v_segments_6928_,
                    );
                    v___x_6935_ = lean_array_to_list(v___x_6934_);
                    v_result_6936_ = l_String_intercalate(v___x_6930_, v___x_6935_);
                    if v_absolute_6929_ == 0 {
                        v___y_6915_ = v_result_6936_;
                        state = 5;
                        continue;
                    } else {
                        v___x_6937_ = lean_string_append(v___x_6930_, v_result_6936_);
                        leanh::lean_dec_ref(v_result_6936_);
                        v___y_6915_ = v___x_6937_;
                        state = 5;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec_ref(v___f_6886_);
                    leanh::lean_dec_ref(v___f_6885_);
                    v_uri_6938_ = leanh::lean_ctor_get(v_target_6890_, 0);
                    leanh::lean_inc_ref(v_uri_6938_);
                    leanh::lean_dec_ref_known(v_target_6890_, 1);
                    v_scheme_6939_ = leanh::lean_ctor_get(v_uri_6938_, 0);
                    leanh::lean_inc_ref(v_scheme_6939_);
                    v_authority_6940_ = leanh::lean_ctor_get(v_uri_6938_, 1);
                    leanh::lean_inc(v_authority_6940_);
                    v_path_6941_ = leanh::lean_ctor_get(v_uri_6938_, 2);
                    leanh::lean_inc_ref(v_path_6941_);
                    v_query_6942_ = leanh::lean_ctor_get(v_uri_6938_, 3);
                    leanh::lean_inc_ref(v_query_6942_);
                    v_fragment_6943_ = leanh::lean_ctor_get(v_uri_6938_, 4);
                    leanh::lean_inc(v_fragment_6943_);
                    leanh::lean_dec_ref(v_uri_6938_);
                    if leanh::lean_obj_tag(v_authority_6940_) == 0 {
                        v___x_6991_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                        v___y_6980_ = v___x_6991_;
                        state = 9;
                        continue;
                    } else {
                        v_val_6992_ = leanh::lean_ctor_get(v_authority_6940_, 0);
                        leanh::lean_inc(v_val_6992_);
                        leanh::lean_dec_ref_known(v_authority_6940_, 1);
                        v_userInfo_6993_ = leanh::lean_ctor_get(v_val_6992_, 0);
                        leanh::lean_inc(v_userInfo_6993_);
                        v_host_6994_ = leanh::lean_ctor_get(v_val_6992_, 1);
                        leanh::lean_inc_ref(v_host_6994_);
                        v_port_6995_ = leanh::lean_ctor_get(v_val_6992_, 2);
                        leanh::lean_inc(v_port_6995_);
                        leanh::lean_dec(v_val_6992_);
                        v___x_6996_ = l_Std_Http_instToStringURI___lam__2___closed__1;
                        if leanh::lean_obj_tag(v_userInfo_6993_) == 0 {
                            v___x_7025_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                            v___y_7015_ = v___x_7025_;
                            state = 12;
                            continue;
                        } else {
                            v_val_7026_ = leanh::lean_ctor_get(v_userInfo_6993_, 0);
                            leanh::lean_inc(v_val_7026_);
                            leanh::lean_dec_ref_known(v_userInfo_6993_, 1);
                            v_password_7027_ = leanh::lean_ctor_get(v_val_7026_, 1);
                            if leanh::lean_obj_tag(v_password_7027_) == 0 {
                                v_username_7028_ = leanh::lean_ctor_get(v_val_7026_, 0);
                                leanh::lean_inc_ref(v_username_7028_);
                                leanh::lean_dec(v_val_7026_);
                                v___x_7029_ = lean_string_from_utf8_unchecked(v_username_7028_);
                                v___x_7030_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                                v___x_7031_ = lean_string_append(v___x_7029_, v___x_7030_);
                                v___y_7015_ = v___x_7031_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_password_7027_);
                                v_username_7032_ = leanh::lean_ctor_get(v_val_7026_, 0);
                                leanh::lean_inc_ref(v_username_7032_);
                                leanh::lean_dec(v_val_7026_);
                                v_val_7033_ = leanh::lean_ctor_get(v_password_7027_, 0);
                                leanh::lean_inc(v_val_7033_);
                                leanh::lean_dec_ref_known(v_password_7027_, 1);
                                v___x_7034_ = lean_string_from_utf8_unchecked(v_username_7032_);
                                v___x_7035_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                                v___x_7036_ = lean_string_append(v___x_7034_, v___x_7035_);
                                v___x_7037_ = lean_string_from_utf8_unchecked(v_val_7033_);
                                v___x_7038_ = lean_string_append(v___x_7036_, v___x_7037_);
                                leanh::lean_dec_ref(v___x_7037_);
                                v___x_7039_ =
                                    l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                                v___x_7040_ = lean_string_append(v___x_7038_, v___x_7039_);
                                v___y_7015_ = v___x_7040_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
                2 => {
                    leanh::lean_dec_ref(v___f_6888_);
                    leanh::lean_dec_ref(v___f_6887_);
                    leanh::lean_dec_ref(v___f_6886_);
                    leanh::lean_dec_ref(v___f_6885_);
                    v_authority_7041_ = leanh::lean_ctor_get(v_target_6890_, 0);
                    leanh::lean_inc_ref(v_authority_7041_);
                    leanh::lean_dec_ref_known(v_target_6890_, 1);
                    v_userInfo_7042_ = leanh::lean_ctor_get(v_authority_7041_, 0);
                    leanh::lean_inc(v_userInfo_7042_);
                    v_host_7043_ = leanh::lean_ctor_get(v_authority_7041_, 1);
                    leanh::lean_inc_ref(v_host_7043_);
                    v_port_7044_ = leanh::lean_ctor_get(v_authority_7041_, 2);
                    leanh::lean_inc(v_port_7044_);
                    leanh::lean_dec_ref(v_authority_7041_);
                    if leanh::lean_obj_tag(v_userInfo_7042_) == 0 {
                        v___x_7066_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                        v___y_7056_ = v___x_7066_;
                        state = 14;
                        continue;
                    } else {
                        v_val_7067_ = leanh::lean_ctor_get(v_userInfo_7042_, 0);
                        leanh::lean_inc(v_val_7067_);
                        leanh::lean_dec_ref_known(v_userInfo_7042_, 1);
                        v_password_7068_ = leanh::lean_ctor_get(v_val_7067_, 1);
                        if leanh::lean_obj_tag(v_password_7068_) == 0 {
                            v_username_7069_ = leanh::lean_ctor_get(v_val_7067_, 0);
                            leanh::lean_inc_ref(v_username_7069_);
                            leanh::lean_dec(v_val_7067_);
                            v___x_7070_ = lean_string_from_utf8_unchecked(v_username_7069_);
                            v___x_7071_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_7072_ = lean_string_append(v___x_7070_, v___x_7071_);
                            v___y_7056_ = v___x_7072_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_password_7068_);
                            v_username_7073_ = leanh::lean_ctor_get(v_val_7067_, 0);
                            leanh::lean_inc_ref(v_username_7073_);
                            leanh::lean_dec(v_val_7067_);
                            v_val_7074_ = leanh::lean_ctor_get(v_password_7068_, 0);
                            leanh::lean_inc(v_val_7074_);
                            leanh::lean_dec_ref_known(v_password_7068_, 1);
                            v___x_7075_ = lean_string_from_utf8_unchecked(v_username_7073_);
                            v___x_7076_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                            v___x_7077_ = lean_string_append(v___x_7075_, v___x_7076_);
                            v___x_7078_ = lean_string_from_utf8_unchecked(v_val_7074_);
                            v___x_7079_ = lean_string_append(v___x_7077_, v___x_7078_);
                            leanh::lean_dec_ref(v___x_7078_);
                            v___x_7080_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__2;
                            v___x_7081_ = lean_string_append(v___x_7079_, v___x_7080_);
                            v___y_7056_ = v___x_7081_;
                            state = 14;
                            continue;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v___f_6888_);
                    leanh::lean_dec_ref(v___f_6887_);
                    leanh::lean_dec_ref(v___f_6886_);
                    leanh::lean_dec_ref(v___f_6885_);
                    v___x_7082_ = l_Std_Http_RequestTarget_instToString___lam__4___closed__0;
                    v___y_6892_ = v___x_7082_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v_data_6893_ = leanh::lean_ctor_get(v_buffer_6889_, 0);
                v_size_6894_ = leanh::lean_ctor_get(v_buffer_6889_, 1);
                v_isSharedCheck_6905_ = (!leanh::lean_is_exclusive(v_buffer_6889_)) as u8;
                if v_isSharedCheck_6905_ == 0 {
                    v___x_6896_ = v_buffer_6889_;
                    v_isShared_6897_ = v_isSharedCheck_6905_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_size_6894_);
                    leanh::lean_inc(v_data_6893_);
                    leanh::lean_dec(v_buffer_6889_);
                    v___x_6896_ = leanh::lean_box(0);
                    v_isShared_6897_ = v_isSharedCheck_6905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6898_ = lean_string_to_utf8(v___y_6892_);
                leanh::lean_dec_ref(v___y_6892_);
                leanh::lean_inc_ref(v___x_6898_);
                v___x_6899_ = lean_array_push(v_data_6893_, v___x_6898_);
                v___x_6900_ = lean_byte_array_size(v___x_6898_);
                leanh::lean_dec_ref(v___x_6898_);
                v___x_6901_ = lean_nat_add(v_size_6894_, v___x_6900_);
                leanh::lean_dec(v_size_6894_);
                if v_isShared_6897_ == 0 {
                    leanh::lean_ctor_set(v___x_6896_, 1, v___x_6901_);
                    leanh::lean_ctor_set(v___x_6896_, 0, v___x_6899_);
                    v___x_6903_ = v___x_6896_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 0, v___x_6899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 1, v___x_6901_);
                    v___x_6903_ = v_reuseFailAlloc_6904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6903_;
            }
            4 => {
                v___x_6910_ = lean_string_append(v___y_6908_, v___y_6907_);
                leanh::lean_dec_ref(v___y_6907_);
                v___x_6911_ = lean_string_append(v___x_6910_, v___y_6909_);
                leanh::lean_dec_ref(v___y_6909_);
                v___y_6892_ = v___x_6911_;
                state = 1;
                continue;
            }
            5 => {
                if leanh::lean_obj_tag(v_query_6913_) == 0 {
                    leanh::lean_dec_ref(v___f_6885_);
                    v___y_6892_ = v___y_6915_;
                    state = 1;
                    continue;
                } else {
                    v_val_6916_ = leanh::lean_ctor_get(v_query_6913_, 0);
                    leanh::lean_inc(v_val_6916_);
                    leanh::lean_dec_ref_known(v_query_6913_, 1);
                    v___x_6917_ = lean_array_get_size(v_val_6916_);
                    v___x_6918_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6919_ = lean_nat_dec_eq(v___x_6917_, v___x_6918_);
                    if v___x_6919_ == 0 {
                        v___x_6920_ = lean_array_to_list(v_val_6916_);
                        v___x_6921_ = leanh::lean_box(0);
                        v_encodedParams_6922_ =
                            l_List_mapTR_loop___redArg(v___f_6885_, v___x_6920_, v___x_6921_);
                        v___x_6923_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
                        v___x_6924_ = l_Std_Http_URI_Query_toRawString___closed__0;
                        v___x_6925_ = l_String_intercalate(v___x_6924_, v_encodedParams_6922_);
                        v___x_6926_ = lean_string_append(v___x_6923_, v___x_6925_);
                        leanh::lean_dec_ref(v___x_6925_);
                        v___x_6927_ = lean_string_append(v___y_6915_, v___x_6926_);
                        leanh::lean_dec_ref(v___x_6926_);
                        v___y_6892_ = v___x_6927_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_6916_);
                        leanh::lean_dec_ref(v___f_6885_);
                        v___y_6892_ = v___y_6915_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6949_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                v___x_6950_ = lean_string_append(v_scheme_6939_, v___x_6949_);
                v___x_6951_ = lean_string_append(v___x_6950_, v___y_6945_);
                leanh::lean_dec_ref(v___y_6945_);
                v___x_6952_ = lean_string_append(v___x_6951_, v___y_6946_);
                leanh::lean_dec_ref(v___y_6946_);
                v___x_6953_ = lean_string_append(v___x_6952_, v___y_6947_);
                leanh::lean_dec_ref(v___y_6947_);
                v___x_6954_ = lean_string_append(v___x_6953_, v___y_6948_);
                leanh::lean_dec_ref(v___y_6948_);
                v___y_6892_ = v___x_6954_;
                state = 1;
                continue;
            }
            7 => {
                if leanh::lean_obj_tag(v_fragment_6943_) == 0 {
                    v___x_6959_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6945_ = v___y_6956_;
                    v___y_6946_ = v___y_6957_;
                    v___y_6947_ = v___y_6958_;
                    v___y_6948_ = v___x_6959_;
                    state = 6;
                    continue;
                } else {
                    v_val_6960_ = leanh::lean_ctor_get(v_fragment_6943_, 0);
                    leanh::lean_inc(v_val_6960_);
                    leanh::lean_dec_ref_known(v_fragment_6943_, 1);
                    v___x_6961_ = l_Std_Http_instToStringURI___lam__2___closed__0;
                    v___x_6962_ = l_Std_Http_URI_EncodedFragment_encode(v_val_6960_);
                    leanh::lean_dec(v_val_6960_);
                    v___x_6963_ = lean_string_from_utf8_unchecked(v___x_6962_);
                    v___x_6964_ = lean_string_append(v___x_6961_, v___x_6963_);
                    leanh::lean_dec_ref(v___x_6963_);
                    v___y_6945_ = v___y_6956_;
                    v___y_6946_ = v___y_6957_;
                    v___y_6947_ = v___y_6958_;
                    v___y_6948_ = v___x_6964_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_6968_ = lean_array_get_size(v_query_6942_);
                v___x_6969_ = leanh::lean_unsigned_to_nat(0);
                v___x_6970_ = lean_nat_dec_eq(v___x_6968_, v___x_6969_);
                if v___x_6970_ == 0 {
                    v___x_6971_ = lean_array_to_list(v_query_6942_);
                    v___x_6972_ = leanh::lean_box(0);
                    v_encodedParams_6973_ =
                        l_List_mapTR_loop___redArg(v___f_6887_, v___x_6971_, v___x_6972_);
                    v___x_6974_ = l_Std_Http_URI_Query_instToString___lam__1___closed__0;
                    v___x_6975_ = l_Std_Http_URI_Query_toRawString___closed__0;
                    v___x_6976_ = l_String_intercalate(v___x_6975_, v_encodedParams_6973_);
                    v___x_6977_ = lean_string_append(v___x_6974_, v___x_6976_);
                    leanh::lean_dec_ref(v___x_6976_);
                    v___y_6956_ = v___y_6966_;
                    v___y_6957_ = v___y_6967_;
                    v___y_6958_ = v___x_6977_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_query_6942_);
                    leanh::lean_dec_ref(v___f_6887_);
                    v___x_6978_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6956_ = v___y_6966_;
                    v___y_6957_ = v___y_6967_;
                    v___y_6958_ = v___x_6978_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_segments_6981_ = leanh::lean_ctor_get(v_path_6941_, 0);
                leanh::lean_inc_ref(v_segments_6981_);
                v_absolute_6982_ = leanh::lean_ctor_get_uint8(
                    v_path_6941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_path_6941_);
                v___x_6983_ = l_Std_Http_URI_instToStringPath___lam__1___closed__0;
                v___x_6984_ = l_Std_Http_URI_instToStringPath___lam__1___closed__10;
                v_sz_6985_ = lean_array_size(v_segments_6981_);
                v___x_6986_ = 0usize;
                v___x_6987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_6984_,
                    v___f_6888_,
                    v_sz_6985_,
                    v___x_6986_,
                    v_segments_6981_,
                );
                v___x_6988_ = lean_array_to_list(v___x_6987_);
                v_result_6989_ = l_String_intercalate(v___x_6983_, v___x_6988_);
                if v_absolute_6982_ == 0 {
                    v___y_6966_ = v___y_6980_;
                    v___y_6967_ = v_result_6989_;
                    state = 8;
                    continue;
                } else {
                    v___x_6990_ = lean_string_append(v___x_6983_, v_result_6989_);
                    leanh::lean_dec_ref(v_result_6989_);
                    v___y_6966_ = v___y_6980_;
                    v___y_6967_ = v___x_6990_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_7001_ = lean_string_append(v___y_6999_, v___y_6998_);
                leanh::lean_dec_ref(v___y_6998_);
                v___x_7002_ = lean_string_append(v___x_7001_, v___y_7000_);
                leanh::lean_dec_ref(v___y_7000_);
                v___x_7003_ = lean_string_append(v___x_6996_, v___x_7002_);
                leanh::lean_dec_ref(v___x_7002_);
                v___y_6980_ = v___x_7003_;
                state = 9;
                continue;
            }
            11 => match leanh::lean_obj_tag(v_port_6995_) {
                0 => {
                    v___x_7007_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6998_ = v___y_7006_;
                    v___y_6999_ = v___y_7005_;
                    v___y_7000_ = v___x_7007_;
                    state = 10;
                    continue;
                }
                1 => {
                    v___x_7008_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_6998_ = v___y_7006_;
                    v___y_6999_ = v___y_7005_;
                    v___y_7000_ = v___x_7008_;
                    state = 10;
                    continue;
                }
                _ => {
                    v_port_7009_ = leanh::lean_ctor_get_uint16(v_port_6995_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_6995_, 0);
                    v___x_7010_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_7011_ = lean_uint16_to_nat(v_port_7009_);
                    v___x_7012_ = l_Nat_reprFast(v___x_7011_);
                    v___x_7013_ = lean_string_append(v___x_7010_, v___x_7012_);
                    leanh::lean_dec_ref(v___x_7012_);
                    v___y_6998_ = v___y_7006_;
                    v___y_6999_ = v___y_7005_;
                    v___y_7000_ = v___x_7013_;
                    state = 10;
                    continue;
                }
            },
            12 => match leanh::lean_obj_tag(v_host_6994_) {
                0 => {
                    v_name_7016_ = leanh::lean_ctor_get(v_host_6994_, 0);
                    leanh::lean_inc_ref(v_name_7016_);
                    leanh::lean_dec_ref_known(v_host_6994_, 1);
                    v___y_7005_ = v___y_7015_;
                    v___y_7006_ = v_name_7016_;
                    state = 11;
                    continue;
                }
                1 => {
                    v_ipv4_7017_ = leanh::lean_ctor_get(v_host_6994_, 0);
                    leanh::lean_inc_ref(v_ipv4_7017_);
                    leanh::lean_dec_ref_known(v_host_6994_, 1);
                    v___x_7018_ = lean_uv_ntop_v4(v_ipv4_7017_);
                    leanh::lean_dec_ref(v_ipv4_7017_);
                    v___y_7005_ = v___y_7015_;
                    v___y_7006_ = v___x_7018_;
                    state = 11;
                    continue;
                }
                _ => {
                    v_ipv6_7019_ = leanh::lean_ctor_get(v_host_6994_, 0);
                    leanh::lean_inc_ref(v_ipv6_7019_);
                    leanh::lean_dec_ref_known(v_host_6994_, 1);
                    v___x_7020_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_7021_ = lean_uv_ntop_v6(v_ipv6_7019_);
                    leanh::lean_dec_ref(v_ipv6_7019_);
                    v___x_7022_ = lean_string_append(v___x_7020_, v___x_7021_);
                    leanh::lean_dec_ref(v___x_7021_);
                    v___x_7023_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_7024_ = lean_string_append(v___x_7022_, v___x_7023_);
                    v___y_7005_ = v___y_7015_;
                    v___y_7006_ = v___x_7024_;
                    state = 11;
                    continue;
                }
            },
            13 => match leanh::lean_obj_tag(v_port_7044_) {
                0 => {
                    v___x_7048_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__0;
                    v___y_6907_ = v___y_7047_;
                    v___y_6908_ = v___y_7046_;
                    v___y_6909_ = v___x_7048_;
                    state = 4;
                    continue;
                }
                1 => {
                    v___x_7049_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___y_6907_ = v___y_7047_;
                    v___y_6908_ = v___y_7046_;
                    v___y_6909_ = v___x_7049_;
                    state = 4;
                    continue;
                }
                _ => {
                    v_port_7050_ = leanh::lean_ctor_get_uint16(v_port_7044_, 0 as u32);
                    leanh::lean_dec_ref_known(v_port_7044_, 0);
                    v___x_7051_ = l_Std_Http_URI_instToStringAuthority___lam__0___closed__1;
                    v___x_7052_ = lean_uint16_to_nat(v_port_7050_);
                    v___x_7053_ = l_Nat_reprFast(v___x_7052_);
                    v___x_7054_ = lean_string_append(v___x_7051_, v___x_7053_);
                    leanh::lean_dec_ref(v___x_7053_);
                    v___y_6907_ = v___y_7047_;
                    v___y_6908_ = v___y_7046_;
                    v___y_6909_ = v___x_7054_;
                    state = 4;
                    continue;
                }
            },
            14 => match leanh::lean_obj_tag(v_host_7043_) {
                0 => {
                    v_name_7057_ = leanh::lean_ctor_get(v_host_7043_, 0);
                    leanh::lean_inc_ref(v_name_7057_);
                    leanh::lean_dec_ref_known(v_host_7043_, 1);
                    v___y_7046_ = v___y_7056_;
                    v___y_7047_ = v_name_7057_;
                    state = 13;
                    continue;
                }
                1 => {
                    v_ipv4_7058_ = leanh::lean_ctor_get(v_host_7043_, 0);
                    leanh::lean_inc_ref(v_ipv4_7058_);
                    leanh::lean_dec_ref_known(v_host_7043_, 1);
                    v___x_7059_ = lean_uv_ntop_v4(v_ipv4_7058_);
                    leanh::lean_dec_ref(v_ipv4_7058_);
                    v___y_7046_ = v___y_7056_;
                    v___y_7047_ = v___x_7059_;
                    state = 13;
                    continue;
                }
                _ => {
                    v_ipv6_7060_ = leanh::lean_ctor_get(v_host_7043_, 0);
                    leanh::lean_inc_ref(v_ipv6_7060_);
                    leanh::lean_dec_ref_known(v_host_7043_, 1);
                    v___x_7061_ = l_Std_Http_URI_instToStringHost___lam__0___closed__0;
                    v___x_7062_ = lean_uv_ntop_v6(v_ipv6_7060_);
                    leanh::lean_dec_ref(v_ipv6_7060_);
                    v___x_7063_ = lean_string_append(v___x_7061_, v___x_7062_);
                    leanh::lean_dec_ref(v___x_7062_);
                    v___x_7064_ = l_Std_Http_URI_instToStringHost___lam__0___closed__1;
                    v___x_7065_ = lean_string_append(v___x_7063_, v___x_7064_);
                    v___y_7046_ = v___y_7056_;
                    v___y_7047_ = v___x_7065_;
                    state = 13;
                    continue;
                }
            },
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_URI_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Encoding(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Http_URI_instInhabitedUserInfo_default =
        _init_l_Std_Http_URI_instInhabitedUserInfo_default();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedUserInfo_default);
    l_Std_Http_URI_instInhabitedUserInfo = _init_l_Std_Http_URI_instInhabitedUserInfo();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedUserInfo);
    l_Std_Http_URI_instInhabitedHost_default = _init_l_Std_Http_URI_instInhabitedHost_default();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedHost_default);
    l_Std_Http_URI_instInhabitedHost = _init_l_Std_Http_URI_instInhabitedHost();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedHost);
    l_Std_Http_URI_instInhabitedPort_default = _init_l_Std_Http_URI_instInhabitedPort_default();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedPort_default);
    l_Std_Http_URI_instInhabitedPort = _init_l_Std_Http_URI_instInhabitedPort();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedPort);
    l_Std_Http_URI_instInhabitedAuthority_default =
        _init_l_Std_Http_URI_instInhabitedAuthority_default();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedAuthority_default);
    l_Std_Http_URI_instInhabitedAuthority = _init_l_Std_Http_URI_instInhabitedAuthority();
    leanh::lean_mark_persistent(l_Std_Http_URI_instInhabitedAuthority);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_URI_Basic(
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
pub unsafe fn initialize_Std_Http_Data_URI_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_URI_Encoding(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_URI_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_URI_Basic(builtin);
}