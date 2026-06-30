// Lean compiler output
// Module: Std.Http.Data.Response
// Imports: Std.Http.Data.Extensions Std.Http.Data.Status Std.Http.Data.Version Std.Http.Data.Headers
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_nat_to_int, lean_string_append, lean_string_dec_eq, lean_string_hash, lean_string_length,
    lean_string_to_utf8, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_string_utf8_set, lean_uint16_to_nat, lean_uint32_add, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_uint8, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_splitToSubslice___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_typeNameImpl;
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
use crate::r#gen::Std::Http::Data::Status::{
    initialize_Std_Http_Data_Status, l_Std_Http_Status_reasonPhrase, l_Std_Http_Status_toCode,
    l_Std_Http_instReprStatus_repr, runtime_initialize_Std_Http_Data_Status,
};
use crate::r#gen::Std::Http::Data::Version::{
    initialize_Std_Http_Data_Version, l_Std_Http_instReprVersion_repr,
    runtime_initialize_Std_Http_Data_Version,
};
static mut l_Std_Http_Response_instInhabitedHead_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instInhabitedHead_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Response_instInhabitedHead_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_instInhabitedHead: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value:
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
    m_data: [115, 116, 97, 116, 117, 115, 0],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value:
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
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__18_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead_repr___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instReprHead_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instReprHead___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Response_instReprHead_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Response_instReprHead___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Response_instReprHead: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instReprHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__1___closed__0_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__1___closed__2_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instToStringHead___lam__1___closed__4_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__0_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__1_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__2_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__3_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__4_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__5_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__6_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__7_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__8_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__12_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__13_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__14_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___lam__2___closed__15_value:
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
static mut l_Std_Http_Response_instToStringHead___lam__2___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___lam__2___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Response_instToStringHead___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Response_instToStringHead___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instToStringHead___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Response_instToStringHead___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instToStringHead___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Response_instToStringHead: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instToStringHead___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0: u8 = 0;
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Response_instEncodeV11Head___closed__0_value:
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
    m_fun: l_Std_Http_Response_instEncodeV11Head___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Response_instEncodeV11Head___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instEncodeV11Head___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Response_instEncodeV11Head___closed__1_value:
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
    m_fun: l_Std_Http_Response_instEncodeV11Head___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Response_instEncodeV11Head___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Response_instEncodeV11Head___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instEncodeV11Head___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Response_instEncodeV11Head: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_instEncodeV11Head___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_new___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_new___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_new: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Response_Builder_new: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Response_Builder_extension___redArg___closed__0_value:
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
static mut l_Std_Http_Response_Builder_extension___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Response_Builder_extension___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Response_ok___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_ok___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_ok: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_notFound___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_notFound___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_notFound: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_internalServerError___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_internalServerError___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_internalServerError: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Response_badRequest___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_badRequest___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_badRequest: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Response_created___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_created___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_created: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_accepted___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_accepted___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_accepted: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_unauthorized___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_unauthorized___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_unauthorized: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Response_forbidden___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_forbidden___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_forbidden: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_conflict___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_conflict___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_conflict: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Response_serviceUnavailable___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Response_serviceUnavailable___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Response_serviceUnavailable: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Http_Response_instInhabitedHead_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = l_Std_Http_Headers_empty;
    v___x_921_ = 1;
    v___x_922_ = leanh::lean_box(4);
    v___x_923_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    leanh::lean_ctor_set(v___x_923_, 1, v___x_920_);
    leanh::lean_ctor_set_uint8(
        v___x_923_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_921_,
    );
    return v___x_923_;
}
pub unsafe fn _init_l_Std_Http_Response_instInhabitedHead_default() -> *mut leanh::LeanObject
{
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0_once),
        _init_l_Std_Http_Response_instInhabitedHead_default___closed__0,
    );
    return v___x_924_;
}
pub unsafe fn _init_l_Std_Http_Response_instInhabitedHead() -> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Std_Http_Response_instInhabitedHead_default;
    return v___x_925_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Response_instReprHead_repr_spec__0(
    mut v_a_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = lean_nat_to_int(v_a_926_);
    return v___x_927_;
}
pub unsafe fn _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = leanh::lean_unsigned_to_nat(10);
    v___x_942_ = lean_nat_to_int(v___x_941_);
    return v___x_942_;
}
pub unsafe fn _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = leanh::lean_unsigned_to_nat(11);
    v___x_950_ = lean_nat_to_int(v___x_949_);
    return v___x_950_;
}
pub unsafe fn _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__0;
    v___x_956_ = lean_string_length(v___x_955_);
    return v___x_956_;
}
pub unsafe fn _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__16_once),
        _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__16,
    );
    v___x_958_ = lean_nat_to_int(v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_Std_Http_Response_instReprHead_repr___redArg(
    mut v_x_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_965_: u8 = 0;
    let mut v_headers_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: u8 = 0;
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_964_ = leanh::lean_ctor_get(v_x_963_, 0);
    leanh::lean_inc(v_status_964_);
    v_version_965_ = leanh::lean_ctor_get_uint8(
        v_x_963_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_headers_966_ = leanh::lean_ctor_get(v_x_963_, 1);
    leanh::lean_inc_ref(v_headers_966_);
    leanh::lean_dec_ref(v_x_963_);
    v___x_967_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__5;
    v___x_968_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__6;
    v___x_969_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once),
        _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7,
    );
    v___x_970_ = leanh::lean_unsigned_to_nat(0);
    v___x_971_ = l_Std_Http_instReprStatus_repr(v_status_964_, v___x_970_);
    v___x_972_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_972_, 0, v___x_969_);
    leanh::lean_ctor_set(v___x_972_, 1, v___x_971_);
    v___x_973_ = 0;
    v___x_974_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_974_, 0, v___x_972_);
    leanh::lean_ctor_set_uint8(
        v___x_974_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_973_,
    );
    v___x_975_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_975_, 0, v___x_968_);
    leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
    v___x_976_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__9;
    v___x_977_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_975_);
    leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
    v___x_978_ = leanh::lean_box(1);
    v___x_979_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_979_, 0, v___x_977_);
    leanh::lean_ctor_set(v___x_979_, 1, v___x_978_);
    v___x_980_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__11;
    v___x_981_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_981_, 0, v___x_979_);
    leanh::lean_ctor_set(v___x_981_, 1, v___x_980_);
    v___x_982_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
    leanh::lean_ctor_set(v___x_982_, 1, v___x_967_);
    v___x_983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once),
        _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12,
    );
    v___x_984_ = l_Std_Http_instReprVersion_repr(v_version_965_, v___x_970_);
    v___x_985_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_985_, 0, v___x_983_);
    leanh::lean_ctor_set(v___x_985_, 1, v___x_984_);
    v___x_986_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_986_, 0, v___x_985_);
    leanh::lean_ctor_set_uint8(
        v___x_986_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_973_,
    );
    v___x_987_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_987_, 0, v___x_982_);
    leanh::lean_ctor_set(v___x_987_, 1, v___x_986_);
    v___x_988_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_988_, 0, v___x_987_);
    leanh::lean_ctor_set(v___x_988_, 1, v___x_976_);
    v___x_989_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_989_, 0, v___x_988_);
    leanh::lean_ctor_set(v___x_989_, 1, v___x_978_);
    v___x_990_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__14;
    v___x_991_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_991_, 0, v___x_989_);
    leanh::lean_ctor_set(v___x_991_, 1, v___x_990_);
    v___x_992_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
    leanh::lean_ctor_set(v___x_992_, 1, v___x_967_);
    v___x_993_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_966_);
    v___x_994_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_994_, 0, v___x_983_);
    leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
    v___x_995_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_995_, 0, v___x_994_);
    leanh::lean_ctor_set_uint8(
        v___x_995_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_973_,
    );
    v___x_996_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_996_, 0, v___x_992_);
    leanh::lean_ctor_set(v___x_996_, 1, v___x_995_);
    v___x_997_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instReprHead_repr___redArg___closed__17_once),
        _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__17,
    );
    v___x_998_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__18;
    v___x_999_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_999_, 0, v___x_998_);
    leanh::lean_ctor_set(v___x_999_, 1, v___x_996_);
    v___x_1000_ = l_Std_Http_Response_instReprHead_repr___redArg___closed__19;
    v___x_1001_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1001_, 0, v___x_999_);
    leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
    v___x_1002_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1002_, 0, v___x_997_);
    leanh::lean_ctor_set(v___x_1002_, 1, v___x_1001_);
    v___x_1003_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    leanh::lean_ctor_set_uint8(
        v___x_1003_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_973_,
    );
    return v___x_1003_;
}
pub unsafe fn l_Std_Http_Response_instReprHead_repr(
    mut v_x_1004_: *mut leanh::LeanObject,
    mut v_prec_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_1004_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Http_Response_instReprHead_repr___boxed(
    mut v_x_1007_: *mut leanh::LeanObject,
    mut v_prec_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l_Std_Http_Response_instReprHead_repr(v_x_1007_, v_prec_1008_);
    leanh::lean_dec(v_prec_1008_);
    return v_res_1009_;
}
pub unsafe fn l_Std_Http_instInhabitedResponse_default___redArg(
    mut v_inst_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0_once),
        _init_l_Std_Http_Response_instInhabitedHead_default___closed__0,
    );
    v___x_1014_ = l_Std_Http_Extensions_empty;
    v___x_1015_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1015_, 0, v___x_1013_);
    leanh::lean_ctor_set(v___x_1015_, 1, v_inst_1012_);
    leanh::lean_ctor_set(v___x_1015_, 2, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Std_Http_instInhabitedResponse_default(
    mut v_t_1016_: *mut leanh::LeanObject,
    mut v_inst_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_1017_);
    return v___x_1018_;
}
pub unsafe fn l_Std_Http_instInhabitedResponse___redArg(
    mut v_inst_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_1019_);
    return v___x_1020_;
}
pub unsafe fn l_Std_Http_instInhabitedResponse(
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_inst_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_1022_);
    return v___x_1023_;
}
pub unsafe fn l_Std_Http_Response_instToStringHead___lam__0(
    mut v___x_1024_: *mut leanh::LeanObject,
    mut v___x_1025_: *mut leanh::LeanObject,
    mut v___x_1026_: *mut leanh::LeanObject,
    mut v_fst_1027_: *mut leanh::LeanObject,
    mut v___x_1028_: *mut leanh::LeanObject,
    mut v___x_1029_: u32,
    mut v___x_1030_: *mut leanh::LeanObject,
    mut v_it_1031_: *mut leanh::LeanObject,
    mut v_acc_1032_: *mut leanh::LeanObject,
    mut v_hP_1033_: *mut leanh::LeanObject,
    mut v_recur_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v_it_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: u32 = 0;
    let mut v___x_1058_: u32 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: u32 = 0;
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: u32 = 0;
    let mut v___x_1065_: u32 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: u32 = 0;
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_1031_) == 0 {
                    v_currPos_1067_ = leanh::lean_ctor_get(v_it_1031_, 0);
                    v_searcher_1068_ = leanh::lean_ctor_get(v_it_1031_, 1);
                    v_isSharedCheck_1090_ = (!leanh::lean_is_exclusive(v_it_1031_)) as u8;
                    if v_isSharedCheck_1090_ == 0 {
                        v___x_1070_ = v_it_1031_;
                        v_isShared_1071_ = v_isSharedCheck_1090_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1068_);
                        leanh::lean_inc(v_currPos_1067_);
                        leanh::lean_dec(v_it_1031_);
                        v___x_1070_ = leanh::lean_box(0);
                        v_isShared_1071_ = v_isSharedCheck_1090_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_recur_1034_);
                    leanh::lean_dec(v___x_1028_);
                    return v_acc_1032_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_acc_1032_) == 0 {
                    v___x_1038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1038_, 0, v_out_1037_);
                    v___x_1039_ = leanh::lean_apply_4(
                        v_recur_1034_,
                        v_it_1036_,
                        v___x_1038_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_1039_;
                } else {
                    v_val_1040_ = leanh::lean_ctor_get(v_acc_1032_, 0);
                    v_isSharedCheck_1051_ = (!leanh::lean_is_exclusive(v_acc_1032_)) as u8;
                    if v_isSharedCheck_1051_ == 0 {
                        v___x_1042_ = v_acc_1032_;
                        v_isShared_1043_ = v_isSharedCheck_1051_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1040_);
                        leanh::lean_dec(v_acc_1032_);
                        v___x_1042_ = leanh::lean_box(0);
                        v_isShared_1043_ = v_isSharedCheck_1051_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1044_ = lean_string_utf8_extract(v___x_1024_, v___x_1025_, v___x_1026_);
                v___x_1045_ = lean_string_append(v_val_1040_, v___x_1044_);
                leanh::lean_dec_ref(v___x_1044_);
                v___x_1046_ = lean_string_append(v___x_1045_, v_out_1037_);
                leanh::lean_dec_ref(v_out_1037_);
                if v_isShared_1043_ == 0 {
                    leanh::lean_ctor_set(v___x_1042_, 0, v___x_1046_);
                    v___x_1048_ = v___x_1042_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1046_);
                    v___x_1048_ = v_reuseFailAlloc_1050_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1049_ = leanh::lean_apply_4(
                    v_recur_1034_,
                    v_it_1036_,
                    v___x_1048_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1049_;
            }
            4 => {
                v___x_1056_ = lean_string_utf8_extract(
                    v_fst_1027_,
                    v_startInclusive_1054_,
                    v_endExclusive_1055_,
                );
                leanh::lean_dec(v_endExclusive_1055_);
                leanh::lean_dec(v_startInclusive_1054_);
                v___x_1057_ = lean_string_utf8_get(v___x_1056_, v___x_1025_);
                v___x_1058_ = 97;
                v___x_1059_ = lean_uint32_dec_le(v___x_1058_, v___x_1057_);
                if v___x_1059_ == 0 {
                    v___x_1060_ = lean_string_utf8_set(v___x_1056_, v___x_1025_, v___x_1057_);
                    v_it_1036_ = v_it_1053_;
                    v_out_1037_ = v___x_1060_;
                    state = 1;
                    continue;
                } else {
                    v___x_1061_ = 122;
                    v___x_1062_ = lean_uint32_dec_le(v___x_1057_, v___x_1061_);
                    if v___x_1062_ == 0 {
                        v___x_1063_ = lean_string_utf8_set(v___x_1056_, v___x_1025_, v___x_1057_);
                        v_it_1036_ = v_it_1053_;
                        v_out_1037_ = v___x_1063_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1064_ = 4294967264;
                        v___x_1065_ = lean_uint32_add(v___x_1057_, v___x_1064_);
                        v___x_1066_ = lean_string_utf8_set(v___x_1056_, v___x_1025_, v___x_1065_);
                        v_it_1036_ = v_it_1053_;
                        v_out_1037_ = v___x_1066_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1072_ = lean_nat_dec_eq(v_searcher_1068_, v___x_1028_);
                if v___x_1072_ == 0 {
                    leanh::lean_dec(v___x_1028_);
                    v___x_1073_ = lean_string_utf8_get_fast(v_fst_1027_, v_searcher_1068_);
                    v___x_1074_ = lean_uint32_dec_eq(v___x_1073_, v___x_1029_);
                    if v___x_1074_ == 0 {
                        v___x_1075_ = lean_string_utf8_next_fast(v_fst_1027_, v_searcher_1068_);
                        leanh::lean_dec(v_searcher_1068_);
                        if v_isShared_1071_ == 0 {
                            leanh::lean_ctor_set(v___x_1070_, 1, v___x_1075_);
                            v___x_1077_ = v___x_1070_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1079_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_currPos_1067_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1075_);
                            v___x_1077_ = v_reuseFailAlloc_1079_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1080_ = lean_string_utf8_next_fast(v_fst_1027_, v_searcher_1068_);
                        v___x_1081_ = lean_nat_sub(v___x_1080_, v_searcher_1068_);
                        v___x_1082_ = lean_nat_add(v_searcher_1068_, v___x_1081_);
                        leanh::lean_dec(v___x_1081_);
                        v_slice_1083_ = l_String_Slice_subslice_x21(
                            v___x_1030_,
                            v_currPos_1067_,
                            v_searcher_1068_,
                        );
                        leanh::lean_inc(v___x_1082_);
                        if v_isShared_1071_ == 0 {
                            leanh::lean_ctor_set(v___x_1070_, 1, v___x_1082_);
                            leanh::lean_ctor_set(v___x_1070_, 0, v___x_1082_);
                            v_nextIt_1085_ = v___x_1070_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1088_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1082_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1082_);
                            v_nextIt_1085_ = v_reuseFailAlloc_1088_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1070_);
                    leanh::lean_dec(v_searcher_1068_);
                    v___x_1089_ = leanh::lean_box(1);
                    v_it_1053_ = v___x_1089_;
                    v_startInclusive_1054_ = v_currPos_1067_;
                    v_endExclusive_1055_ = v___x_1028_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1078_ = leanh::lean_apply_4(
                    v_recur_1034_,
                    v___x_1077_,
                    v_acc_1032_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1078_;
            }
            7 => {
                v_startInclusive_1086_ = leanh::lean_ctor_get(v_slice_1083_, 0);
                leanh::lean_inc(v_startInclusive_1086_);
                v_endExclusive_1087_ = leanh::lean_ctor_get(v_slice_1083_, 1);
                leanh::lean_inc(v_endExclusive_1087_);
                leanh::lean_dec_ref(v_slice_1083_);
                v_it_1053_ = v_nextIt_1085_;
                v_startInclusive_1054_ = v_startInclusive_1086_;
                v_endExclusive_1055_ = v_endExclusive_1087_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instToStringHead___lam__0___boxed(
    mut v___x_1091_: *mut leanh::LeanObject,
    mut v___x_1092_: *mut leanh::LeanObject,
    mut v___x_1093_: *mut leanh::LeanObject,
    mut v_fst_1094_: *mut leanh::LeanObject,
    mut v___x_1095_: *mut leanh::LeanObject,
    mut v___x_1096_: *mut leanh::LeanObject,
    mut v___x_1097_: *mut leanh::LeanObject,
    mut v_it_1098_: *mut leanh::LeanObject,
    mut v_acc_1099_: *mut leanh::LeanObject,
    mut v_hP_1100_: *mut leanh::LeanObject,
    mut v_recur_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_729__boxed_1102_: u32 = 0;
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_729__boxed_1102_ = leanh::lean_unbox_uint32(v___x_1096_);
    leanh::lean_dec(v___x_1096_);
    v_res_1103_ = l_Std_Http_Response_instToStringHead___lam__0(
        v___x_1091_,
        v___x_1092_,
        v___x_1093_,
        v_fst_1094_,
        v___x_1095_,
        v___x_729__boxed_1102_,
        v___x_1097_,
        v_it_1098_,
        v_acc_1099_,
        v_hP_1100_,
        v_recur_1101_,
    );
    leanh::lean_dec_ref(v___x_1097_);
    leanh::lean_dec_ref(v_fst_1094_);
    leanh::lean_dec(v___x_1093_);
    leanh::lean_dec(v___x_1092_);
    leanh::lean_dec_ref(v___x_1091_);
    return v_res_1103_;
}
pub unsafe fn _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Std_Http_Response_instToStringHead___lam__1___closed__2;
    v___x_1108_ = lean_string_utf8_byte_size(v___x_1107_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1110_: u32 = 0;
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = 45;
    v___x_1111_ = leanh::lean_box_uint32(v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Std_Http_Response_instToStringHead___lam__1(
    mut v_x_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1113_ = leanh::lean_ctor_get(v_x_1112_, 0);
                leanh::lean_inc_n(v_fst_1113_, 2);
                v_snd_1114_ = leanh::lean_ctor_get(v_x_1112_, 1);
                leanh::lean_inc(v_snd_1114_);
                leanh::lean_dec_ref(v_x_1112_);
                v___f_1120_ = l_Std_Http_Response_instToStringHead___lam__1___closed__1;
                v___x_1121_ = leanh::lean_unsigned_to_nat(0);
                v___x_1122_ = lean_string_utf8_byte_size(v_fst_1113_);
                v___x_1123_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1123_, 0, v_fst_1113_);
                leanh::lean_ctor_set(v___x_1123_, 1, v___x_1121_);
                leanh::lean_ctor_set(v___x_1123_, 2, v___x_1122_);
                leanh::lean_inc_ref(v___x_1123_);
                v_it_1124_ = l_String_Slice_splitToSubslice___redArg(v___x_1123_, v___f_1120_);
                v___x_1125_ = l_Std_Http_Response_instToStringHead___lam__1___closed__2;
                v___x_1126_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instToStringHead___lam__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instToStringHead___lam__1___closed__3_once
                    ),
                    _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3,
                );
                v___x_1127_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
                v___f_1128_ = leanh::lean_alloc_closure(
                    l_Std_Http_Response_instToStringHead___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_1128_, 0, v___x_1125_);
                leanh::lean_closure_set(v___f_1128_, 1, v___x_1121_);
                leanh::lean_closure_set(v___f_1128_, 2, v___x_1126_);
                leanh::lean_closure_set(v___f_1128_, 3, v_fst_1113_);
                leanh::lean_closure_set(v___f_1128_, 4, v___x_1122_);
                leanh::lean_closure_set(v___f_1128_, 5, v___x_1127_);
                leanh::lean_closure_set(v___f_1128_, 6, v___x_1123_);
                v___x_1129_ = leanh::lean_box(0);
                v___x_1130_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1128_,
                    v_it_1124_,
                    v___x_1129_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1130_) == 0 {
                    v___x_1131_ = l_Std_Http_Response_instToStringHead___lam__1___closed__4;
                    v___y_1116_ = v___x_1131_;
                    state = 1;
                    continue;
                } else {
                    v_val_1132_ = leanh::lean_ctor_get(v___x_1130_, 0);
                    leanh::lean_inc(v_val_1132_);
                    leanh::lean_dec_ref_known(v___x_1130_, 1);
                    v___y_1116_ = v_val_1132_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1117_ = l_Std_Http_Response_instToStringHead___lam__1___closed__0;
                v___x_1118_ = lean_string_append(v___y_1116_, v___x_1117_);
                v___x_1119_ = lean_string_append(v___x_1118_, v_snd_1114_);
                leanh::lean_dec(v_snd_1114_);
                return v___x_1119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instToStringHead___lam__2(
    mut v___f_1158_: *mut leanh::LeanObject,
    mut v_r_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1161_: u8 = 0;
    let mut v_headers_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u16 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1178_: usize = 0;
    let mut v___x_1179_: usize = 0;
    let mut v_pairs_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_status_1160_ = leanh::lean_ctor_get(v_r_1159_, 0);
                leanh::lean_inc(v_status_1160_);
                v_version_1161_ = leanh::lean_ctor_get_uint8(
                    v_r_1159_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_headers_1162_ = leanh::lean_ctor_get(v_r_1159_, 1);
                leanh::lean_inc_ref(v_headers_1162_);
                leanh::lean_dec_ref(v_r_1159_);
                match v_version_1161_ {
                    0 => {
                        v___x_1185_ = l_Std_Http_Response_instToStringHead___lam__2___closed__12;
                        v___y_1164_ = v___x_1185_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1186_ = l_Std_Http_Response_instToStringHead___lam__2___closed__13;
                        v___y_1164_ = v___x_1186_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_1187_ = l_Std_Http_Response_instToStringHead___lam__2___closed__14;
                        v___y_1164_ = v___x_1187_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1188_ = l_Std_Http_Response_instToStringHead___lam__2___closed__15;
                        v___y_1164_ = v___x_1188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_entries_1165_ = leanh::lean_ctor_get(v_headers_1162_, 0);
                leanh::lean_inc_ref(v_entries_1165_);
                leanh::lean_dec_ref(v_headers_1162_);
                v___x_1166_ = l_Std_Http_Response_instToStringHead___lam__2___closed__0;
                leanh::lean_inc_ref(v___y_1164_);
                v___x_1167_ = lean_string_append(v___y_1164_, v___x_1166_);
                v___x_1168_ = l_Std_Http_Status_toCode(v_status_1160_);
                v___x_1169_ = lean_uint16_to_nat(v___x_1168_);
                v___x_1170_ = l_Nat_reprFast(v___x_1169_);
                v___x_1171_ = lean_string_append(v___x_1167_, v___x_1170_);
                leanh::lean_dec_ref(v___x_1170_);
                v___x_1172_ = lean_string_append(v___x_1171_, v___x_1166_);
                v___x_1173_ = l_Std_Http_Status_reasonPhrase(v_status_1160_);
                leanh::lean_dec(v_status_1160_);
                v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
                leanh::lean_dec_ref(v___x_1173_);
                v___x_1175_ = l_Std_Http_Response_instToStringHead___lam__2___closed__1;
                v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
                v___x_1177_ = l_Std_Http_Response_instToStringHead___lam__2___closed__11;
                v_sz_1178_ = lean_array_size(v_entries_1165_);
                v___x_1179_ = 0usize;
                v_pairs_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1177_,
                    v___f_1158_,
                    v_sz_1178_,
                    v___x_1179_,
                    v_entries_1165_,
                );
                v___x_1181_ = lean_array_to_list(v_pairs_1180_);
                v___x_1182_ = l_String_intercalate(v___x_1175_, v___x_1181_);
                v___x_1183_ = lean_string_append(v___x_1176_, v___x_1182_);
                leanh::lean_dec_ref(v___x_1182_);
                v___x_1184_ = lean_string_append(v___x_1183_, v___x_1175_);
                return v___x_1184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__0(
    mut v___x_1193_: *mut leanh::LeanObject,
    mut v___x_1194_: *mut leanh::LeanObject,
    mut v___x_1195_: *mut leanh::LeanObject,
    mut v_name_1196_: *mut leanh::LeanObject,
    mut v___x_1197_: *mut leanh::LeanObject,
    mut v___x_1198_: u32,
    mut v___x_1199_: *mut leanh::LeanObject,
    mut v_it_1200_: *mut leanh::LeanObject,
    mut v_acc_1201_: *mut leanh::LeanObject,
    mut v_hP_1202_: *mut leanh::LeanObject,
    mut v_recur_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut v_it_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u32 = 0;
    let mut v___x_1227_: u32 = 0;
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u32 = 0;
    let mut v___x_1231_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u32 = 0;
    let mut v___x_1234_: u32 = 0;
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: u32 = 0;
    let mut v___x_1243_: u8 = 0;
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_1200_) == 0 {
                    v_currPos_1236_ = leanh::lean_ctor_get(v_it_1200_, 0);
                    v_searcher_1237_ = leanh::lean_ctor_get(v_it_1200_, 1);
                    v_isSharedCheck_1259_ = (!leanh::lean_is_exclusive(v_it_1200_)) as u8;
                    if v_isSharedCheck_1259_ == 0 {
                        v___x_1239_ = v_it_1200_;
                        v_isShared_1240_ = v_isSharedCheck_1259_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1237_);
                        leanh::lean_inc(v_currPos_1236_);
                        leanh::lean_dec(v_it_1200_);
                        v___x_1239_ = leanh::lean_box(0);
                        v_isShared_1240_ = v_isSharedCheck_1259_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_recur_1203_);
                    leanh::lean_dec(v___x_1197_);
                    return v_acc_1201_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_acc_1201_) == 0 {
                    v___x_1207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1207_, 0, v_out_1206_);
                    v___x_1208_ = leanh::lean_apply_4(
                        v_recur_1203_,
                        v_it_1205_,
                        v___x_1207_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_1208_;
                } else {
                    v_val_1209_ = leanh::lean_ctor_get(v_acc_1201_, 0);
                    v_isSharedCheck_1220_ = (!leanh::lean_is_exclusive(v_acc_1201_)) as u8;
                    if v_isSharedCheck_1220_ == 0 {
                        v___x_1211_ = v_acc_1201_;
                        v_isShared_1212_ = v_isSharedCheck_1220_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1209_);
                        leanh::lean_dec(v_acc_1201_);
                        v___x_1211_ = leanh::lean_box(0);
                        v_isShared_1212_ = v_isSharedCheck_1220_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1213_ = lean_string_utf8_extract(v___x_1193_, v___x_1194_, v___x_1195_);
                v___x_1214_ = lean_string_append(v_val_1209_, v___x_1213_);
                leanh::lean_dec_ref(v___x_1213_);
                v___x_1215_ = lean_string_append(v___x_1214_, v_out_1206_);
                leanh::lean_dec_ref(v_out_1206_);
                if v_isShared_1212_ == 0 {
                    leanh::lean_ctor_set(v___x_1211_, 0, v___x_1215_);
                    v___x_1217_ = v___x_1211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1215_);
                    v___x_1217_ = v_reuseFailAlloc_1219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1218_ = leanh::lean_apply_4(
                    v_recur_1203_,
                    v_it_1205_,
                    v___x_1217_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1218_;
            }
            4 => {
                v___x_1225_ = lean_string_utf8_extract(
                    v_name_1196_,
                    v_startInclusive_1223_,
                    v_endExclusive_1224_,
                );
                leanh::lean_dec(v_endExclusive_1224_);
                leanh::lean_dec(v_startInclusive_1223_);
                v___x_1226_ = lean_string_utf8_get(v___x_1225_, v___x_1194_);
                v___x_1227_ = 97;
                v___x_1228_ = lean_uint32_dec_le(v___x_1227_, v___x_1226_);
                if v___x_1228_ == 0 {
                    v___x_1229_ = lean_string_utf8_set(v___x_1225_, v___x_1194_, v___x_1226_);
                    v_it_1205_ = v_it_1222_;
                    v_out_1206_ = v___x_1229_;
                    state = 1;
                    continue;
                } else {
                    v___x_1230_ = 122;
                    v___x_1231_ = lean_uint32_dec_le(v___x_1226_, v___x_1230_);
                    if v___x_1231_ == 0 {
                        v___x_1232_ = lean_string_utf8_set(v___x_1225_, v___x_1194_, v___x_1226_);
                        v_it_1205_ = v_it_1222_;
                        v_out_1206_ = v___x_1232_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1233_ = 4294967264;
                        v___x_1234_ = lean_uint32_add(v___x_1226_, v___x_1233_);
                        v___x_1235_ = lean_string_utf8_set(v___x_1225_, v___x_1194_, v___x_1234_);
                        v_it_1205_ = v_it_1222_;
                        v_out_1206_ = v___x_1235_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1241_ = lean_nat_dec_eq(v_searcher_1237_, v___x_1197_);
                if v___x_1241_ == 0 {
                    leanh::lean_dec(v___x_1197_);
                    v___x_1242_ = lean_string_utf8_get_fast(v_name_1196_, v_searcher_1237_);
                    v___x_1243_ = lean_uint32_dec_eq(v___x_1242_, v___x_1198_);
                    if v___x_1243_ == 0 {
                        v___x_1244_ = lean_string_utf8_next_fast(v_name_1196_, v_searcher_1237_);
                        leanh::lean_dec(v_searcher_1237_);
                        if v_isShared_1240_ == 0 {
                            leanh::lean_ctor_set(v___x_1239_, 1, v___x_1244_);
                            v___x_1246_ = v___x_1239_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1248_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_currPos_1236_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1244_);
                            v___x_1246_ = v_reuseFailAlloc_1248_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1249_ = lean_string_utf8_next_fast(v_name_1196_, v_searcher_1237_);
                        v___x_1250_ = lean_nat_sub(v___x_1249_, v_searcher_1237_);
                        v___x_1251_ = lean_nat_add(v_searcher_1237_, v___x_1250_);
                        leanh::lean_dec(v___x_1250_);
                        v_slice_1252_ = l_String_Slice_subslice_x21(
                            v___x_1199_,
                            v_currPos_1236_,
                            v_searcher_1237_,
                        );
                        leanh::lean_inc(v___x_1251_);
                        if v_isShared_1240_ == 0 {
                            leanh::lean_ctor_set(v___x_1239_, 1, v___x_1251_);
                            leanh::lean_ctor_set(v___x_1239_, 0, v___x_1251_);
                            v_nextIt_1254_ = v___x_1239_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1257_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1251_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1251_);
                            v_nextIt_1254_ = v_reuseFailAlloc_1257_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1239_);
                    leanh::lean_dec(v_searcher_1237_);
                    v___x_1258_ = leanh::lean_box(1);
                    v_it_1222_ = v___x_1258_;
                    v_startInclusive_1223_ = v_currPos_1236_;
                    v_endExclusive_1224_ = v___x_1197_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1247_ = leanh::lean_apply_4(
                    v_recur_1203_,
                    v___x_1246_,
                    v_acc_1201_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1247_;
            }
            7 => {
                v_startInclusive_1255_ = leanh::lean_ctor_get(v_slice_1252_, 0);
                leanh::lean_inc(v_startInclusive_1255_);
                v_endExclusive_1256_ = leanh::lean_ctor_get(v_slice_1252_, 1);
                leanh::lean_inc(v_endExclusive_1256_);
                leanh::lean_dec_ref(v_slice_1252_);
                v_it_1222_ = v_nextIt_1254_;
                v_startInclusive_1223_ = v_startInclusive_1255_;
                v_endExclusive_1224_ = v_endExclusive_1256_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(
    mut v___x_1260_: *mut leanh::LeanObject,
    mut v___x_1261_: *mut leanh::LeanObject,
    mut v___x_1262_: *mut leanh::LeanObject,
    mut v_name_1263_: *mut leanh::LeanObject,
    mut v___x_1264_: *mut leanh::LeanObject,
    mut v___x_1265_: *mut leanh::LeanObject,
    mut v___x_1266_: *mut leanh::LeanObject,
    mut v_it_1267_: *mut leanh::LeanObject,
    mut v_acc_1268_: *mut leanh::LeanObject,
    mut v_hP_1269_: *mut leanh::LeanObject,
    mut v_recur_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1176__boxed_1271_: u32 = 0;
    let mut v_res_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1176__boxed_1271_ = leanh::lean_unbox_uint32(v___x_1265_);
    leanh::lean_dec(v___x_1265_);
    v_res_1272_ = l_Std_Http_Response_instEncodeV11Head___lam__0(
        v___x_1260_,
        v___x_1261_,
        v___x_1262_,
        v_name_1263_,
        v___x_1264_,
        v___x_1176__boxed_1271_,
        v___x_1266_,
        v_it_1267_,
        v_acc_1268_,
        v_hP_1269_,
        v_recur_1270_,
    );
    leanh::lean_dec_ref(v___x_1266_);
    leanh::lean_dec_ref(v_name_1263_);
    leanh::lean_dec(v___x_1262_);
    leanh::lean_dec(v___x_1261_);
    leanh::lean_dec_ref(v___x_1260_);
    return v_res_1272_;
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__1(
    mut v_buf_1273_: *mut leanh::LeanObject,
    mut v_name_1274_: *mut leanh::LeanObject,
    mut v_value_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut v___f_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1296_ = l_Std_Http_Response_instToStringHead___lam__1___closed__1;
                v___x_1297_ = leanh::lean_unsigned_to_nat(0);
                v___x_1298_ = lean_string_utf8_byte_size(v_name_1274_);
                leanh::lean_inc_ref(v_name_1274_);
                v___x_1299_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1299_, 0, v_name_1274_);
                leanh::lean_ctor_set(v___x_1299_, 1, v___x_1297_);
                leanh::lean_ctor_set(v___x_1299_, 2, v___x_1298_);
                leanh::lean_inc_ref(v___x_1299_);
                v_it_1300_ = l_String_Slice_splitToSubslice___redArg(v___x_1299_, v___f_1296_);
                v___x_1301_ = l_Std_Http_Response_instToStringHead___lam__1___closed__2;
                v___x_1302_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instToStringHead___lam__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instToStringHead___lam__1___closed__3_once
                    ),
                    _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3,
                );
                v___x_1303_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
                v___f_1304_ = leanh::lean_alloc_closure(
                    l_Std_Http_Response_instEncodeV11Head___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_1304_, 0, v___x_1301_);
                leanh::lean_closure_set(v___f_1304_, 1, v___x_1297_);
                leanh::lean_closure_set(v___f_1304_, 2, v___x_1302_);
                leanh::lean_closure_set(v___f_1304_, 3, v_name_1274_);
                leanh::lean_closure_set(v___f_1304_, 4, v___x_1298_);
                leanh::lean_closure_set(v___f_1304_, 5, v___x_1303_);
                leanh::lean_closure_set(v___f_1304_, 6, v___x_1299_);
                v___x_1305_ = leanh::lean_box(0);
                v___x_1306_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1304_,
                    v_it_1300_,
                    v___x_1305_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1306_) == 0 {
                    v___x_1307_ = l_Std_Http_Response_instToStringHead___lam__1___closed__4;
                    v___y_1277_ = v___x_1307_;
                    state = 1;
                    continue;
                } else {
                    v_val_1308_ = leanh::lean_ctor_get(v___x_1306_, 0);
                    leanh::lean_inc(v_val_1308_);
                    leanh::lean_dec_ref_known(v___x_1306_, 1);
                    v___y_1277_ = v_val_1308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_1278_ = leanh::lean_ctor_get(v_buf_1273_, 0);
                v_size_1279_ = leanh::lean_ctor_get(v_buf_1273_, 1);
                v_isSharedCheck_1295_ = (!leanh::lean_is_exclusive(v_buf_1273_)) as u8;
                if v_isSharedCheck_1295_ == 0 {
                    v___x_1281_ = v_buf_1273_;
                    v_isShared_1282_ = v_isSharedCheck_1295_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_size_1279_);
                    leanh::lean_inc(v_data_1278_);
                    leanh::lean_dec(v_buf_1273_);
                    v___x_1281_ = leanh::lean_box(0);
                    v_isShared_1282_ = v_isSharedCheck_1295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1283_ = l_Std_Http_Response_instToStringHead___lam__1___closed__0;
                v___x_1284_ = lean_string_append(v___y_1277_, v___x_1283_);
                v___x_1285_ = lean_string_append(v___x_1284_, v_value_1275_);
                v___x_1286_ = l_Std_Http_Response_instToStringHead___lam__2___closed__1;
                v___x_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
                v___x_1288_ = lean_string_to_utf8(v___x_1287_);
                leanh::lean_dec_ref(v___x_1287_);
                leanh::lean_inc_ref(v___x_1288_);
                v___x_1289_ = lean_array_push(v_data_1278_, v___x_1288_);
                v___x_1290_ = lean_byte_array_size(v___x_1288_);
                leanh::lean_dec_ref(v___x_1288_);
                v___x_1291_ = lean_nat_add(v_size_1279_, v___x_1290_);
                leanh::lean_dec(v_size_1279_);
                if v_isShared_1282_ == 0 {
                    leanh::lean_ctor_set(v___x_1281_, 1, v___x_1291_);
                    leanh::lean_ctor_set(v___x_1281_, 0, v___x_1289_);
                    v___x_1293_ = v___x_1281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1291_);
                    v___x_1293_ = v_reuseFailAlloc_1294_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(
    mut v_buf_1309_: *mut leanh::LeanObject,
    mut v_name_1310_: *mut leanh::LeanObject,
    mut v_value_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ =
        l_Std_Http_Response_instEncodeV11Head___lam__1(v_buf_1309_, v_name_1310_, v_value_1311_);
    leanh::lean_dec_ref(v_value_1311_);
    return v_res_1312_;
}
pub unsafe fn _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0() -> u8 {
    let mut v___x_1313_: u32 = 0;
    let mut v___x_1314_: u8 = 0;
    v___x_1313_ = 32;
    v___x_1314_ = lean_uint32_to_uint8(v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_once),
        _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0,
    );
    v___x_1316_ = leanh::lean_unsigned_to_nat(1);
    v___x_1317_ = lean_mk_empty_array_with_capacity(v___x_1316_);
    v___x_1318_ = leanh::lean_box((v___x_1315_) as usize);
    v___x_1319_ = lean_array_push(v___x_1317_, v___x_1318_);
    v___x_1320_ = lean_byte_array_mk(v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once),
        _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1,
    );
    v___x_1322_ = lean_byte_array_size(v___x_1321_);
    return v___x_1322_;
}
pub unsafe fn _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = l_Std_Http_Response_instToStringHead___lam__2___closed__1;
    v___x_1324_ = lean_string_to_utf8(v___x_1323_);
    return v___x_1324_;
}
pub unsafe fn _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once),
        _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3,
    );
    v___x_1326_ = lean_byte_array_size(v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__2(
    mut v___f_1327_: *mut leanh::LeanObject,
    mut v_buffer_1328_: *mut leanh::LeanObject,
    mut v_r_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1331_: u8 = 0;
    let mut v_headers_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: u16 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buffer_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_reuseFailAlloc_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_status_1330_ = leanh::lean_ctor_get(v_r_1329_, 0);
                v_version_1331_ = leanh::lean_ctor_get_uint8(
                    v_r_1329_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_headers_1332_ = leanh::lean_ctor_get(v_r_1329_, 1);
                match v_version_1331_ {
                    0 => {
                        v___x_1382_ = l_Std_Http_Response_instToStringHead___lam__2___closed__12;
                        v___y_1334_ = v___x_1382_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1383_ = l_Std_Http_Response_instToStringHead___lam__2___closed__13;
                        v___y_1334_ = v___x_1383_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_1384_ = l_Std_Http_Response_instToStringHead___lam__2___closed__14;
                        v___y_1334_ = v___x_1384_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1385_ = l_Std_Http_Response_instToStringHead___lam__2___closed__15;
                        v___y_1334_ = v___x_1385_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_data_1335_ = leanh::lean_ctor_get(v_buffer_1328_, 0);
                v_size_1336_ = leanh::lean_ctor_get(v_buffer_1328_, 1);
                v_isSharedCheck_1381_ = (!leanh::lean_is_exclusive(v_buffer_1328_)) as u8;
                if v_isSharedCheck_1381_ == 0 {
                    v___x_1338_ = v_buffer_1328_;
                    v_isShared_1339_ = v_isSharedCheck_1381_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_size_1336_);
                    leanh::lean_inc(v_data_1335_);
                    leanh::lean_dec(v_buffer_1328_);
                    v___x_1338_ = leanh::lean_box(0);
                    v_isShared_1339_ = v_isSharedCheck_1381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1340_ = lean_string_to_utf8(v___y_1334_);
                leanh::lean_inc_ref(v___x_1340_);
                v___x_1341_ = lean_array_push(v_data_1335_, v___x_1340_);
                v___x_1342_ = lean_byte_array_size(v___x_1340_);
                leanh::lean_dec_ref(v___x_1340_);
                v___x_1343_ = lean_nat_add(v_size_1336_, v___x_1342_);
                leanh::lean_dec(v_size_1336_);
                v___x_1344_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once
                    ),
                    _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1,
                );
                v___x_1345_ = lean_array_push(v___x_1341_, v___x_1344_);
                v___x_1346_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once
                    ),
                    _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2,
                );
                v___x_1347_ = lean_nat_add(v___x_1343_, v___x_1346_);
                leanh::lean_dec(v___x_1343_);
                v___x_1348_ = l_Std_Http_Status_toCode(v_status_1330_);
                v___x_1349_ = lean_uint16_to_nat(v___x_1348_);
                v___x_1350_ = l_Nat_reprFast(v___x_1349_);
                v___x_1351_ = lean_string_to_utf8(v___x_1350_);
                leanh::lean_dec_ref(v___x_1350_);
                leanh::lean_inc_ref(v___x_1351_);
                v___x_1352_ = lean_array_push(v___x_1345_, v___x_1351_);
                v___x_1353_ = lean_byte_array_size(v___x_1351_);
                leanh::lean_dec_ref(v___x_1351_);
                v___x_1354_ = lean_nat_add(v___x_1347_, v___x_1353_);
                leanh::lean_dec(v___x_1347_);
                v___x_1355_ = lean_array_push(v___x_1352_, v___x_1344_);
                v___x_1356_ = lean_nat_add(v___x_1354_, v___x_1346_);
                leanh::lean_dec(v___x_1354_);
                v___x_1357_ = l_Std_Http_Status_reasonPhrase(v_status_1330_);
                v___x_1358_ = lean_string_to_utf8(v___x_1357_);
                leanh::lean_dec_ref(v___x_1357_);
                leanh::lean_inc_ref(v___x_1358_);
                v___x_1359_ = lean_array_push(v___x_1355_, v___x_1358_);
                v___x_1360_ = lean_byte_array_size(v___x_1358_);
                leanh::lean_dec_ref(v___x_1358_);
                v___x_1361_ = lean_nat_add(v___x_1356_, v___x_1360_);
                leanh::lean_dec(v___x_1356_);
                v___x_1362_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once
                    ),
                    _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3,
                );
                v___x_1363_ = lean_array_push(v___x_1359_, v___x_1362_);
                v___x_1364_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4_once
                    ),
                    _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4,
                );
                v___x_1365_ = lean_nat_add(v___x_1361_, v___x_1364_);
                leanh::lean_dec(v___x_1361_);
                if v_isShared_1339_ == 0 {
                    leanh::lean_ctor_set(v___x_1338_, 1, v___x_1365_);
                    leanh::lean_ctor_set(v___x_1338_, 0, v___x_1363_);
                    v_buffer_1367_ = v___x_1338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1365_);
                    v_buffer_1367_ = v_reuseFailAlloc_1380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_buffer_1368_ =
                    l_Std_Http_Headers_fold___redArg(v_headers_1332_, v_buffer_1367_, v___f_1327_);
                v_data_1369_ = leanh::lean_ctor_get(v_buffer_1368_, 0);
                v_size_1370_ = leanh::lean_ctor_get(v_buffer_1368_, 1);
                v_isSharedCheck_1379_ = (!leanh::lean_is_exclusive(v_buffer_1368_)) as u8;
                if v_isSharedCheck_1379_ == 0 {
                    v___x_1372_ = v_buffer_1368_;
                    v_isShared_1373_ = v_isSharedCheck_1379_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_size_1370_);
                    leanh::lean_inc(v_data_1369_);
                    leanh::lean_dec(v_buffer_1368_);
                    v___x_1372_ = leanh::lean_box(0);
                    v_isShared_1373_ = v_isSharedCheck_1379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1374_ = lean_array_push(v_data_1369_, v___x_1362_);
                v___x_1375_ = lean_nat_add(v_size_1370_, v___x_1364_);
                leanh::lean_dec(v_size_1370_);
                if v_isShared_1373_ == 0 {
                    leanh::lean_ctor_set(v___x_1372_, 1, v___x_1375_);
                    leanh::lean_ctor_set(v___x_1372_, 0, v___x_1374_);
                    v___x_1377_ = v___x_1372_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
                    v___x_1377_ = v_reuseFailAlloc_1378_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(
    mut v___f_1386_: *mut leanh::LeanObject,
    mut v_buffer_1387_: *mut leanh::LeanObject,
    mut v_r_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1389_ =
        l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_1386_, v_buffer_1387_, v_r_1388_);
    leanh::lean_dec_ref(v_r_1388_);
    return v_res_1389_;
}
pub unsafe fn _init_l_Std_Http_Response_new___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Std_Http_Extensions_empty;
    v___x_1395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_instInhabitedHead_default___closed__0_once),
        _init_l_Std_Http_Response_instInhabitedHead_default___closed__0,
    );
    v___x_1396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    leanh::lean_ctor_set(v___x_1396_, 1, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Std_Http_Response_new() -> *mut leanh::LeanObject {
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_new___closed__0_once),
        _init_l_Std_Http_Response_new___closed__0,
    );
    return v___x_1397_;
}
pub unsafe fn _init_l_Std_Http_Response_Builder_new() -> *mut leanh::LeanObject {
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_new___closed__0_once),
        _init_l_Std_Http_Response_new___closed__0,
    );
    return v___x_1398_;
}
pub unsafe fn l_Std_Http_Response_Builder_status(
    mut v_builder_1399_: *mut leanh::LeanObject,
    mut v_status_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v_version_1406_: u8 = 0;
    let mut v_headers_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut v_unused_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1401_ = leanh::lean_ctor_get(v_builder_1399_, 0);
                v_extensions_1402_ = leanh::lean_ctor_get(v_builder_1399_, 1);
                v_isSharedCheck_1419_ = (!leanh::lean_is_exclusive(v_builder_1399_)) as u8;
                if v_isSharedCheck_1419_ == 0 {
                    v___x_1404_ = v_builder_1399_;
                    v_isShared_1405_ = v_isSharedCheck_1419_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1402_);
                    leanh::lean_inc(v_line_1401_);
                    leanh::lean_dec(v_builder_1399_);
                    v___x_1404_ = leanh::lean_box(0);
                    v_isShared_1405_ = v_isSharedCheck_1419_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_version_1406_ = leanh::lean_ctor_get_uint8(
                    v_line_1401_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_headers_1407_ = leanh::lean_ctor_get(v_line_1401_, 1);
                v_isSharedCheck_1417_ = (!leanh::lean_is_exclusive(v_line_1401_)) as u8;
                if v_isSharedCheck_1417_ == 0 {
                    v_unused_1418_ = leanh::lean_ctor_get(v_line_1401_, 0);
                    leanh::lean_dec(v_unused_1418_);
                    v___x_1409_ = v_line_1401_;
                    v_isShared_1410_ = v_isSharedCheck_1417_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_headers_1407_);
                    leanh::lean_dec(v_line_1401_);
                    v___x_1409_ = leanh::lean_box(0);
                    v_isShared_1410_ = v_isSharedCheck_1417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1410_ == 0 {
                    leanh::lean_ctor_set(v___x_1409_, 0, v_status_1400_);
                    v___x_1412_ = v___x_1409_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_status_1400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_headers_1407_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1416_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_1406_,
                    );
                    v___x_1412_ = v_reuseFailAlloc_1416_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1405_ == 0 {
                    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1412_);
                    v___x_1414_ = v___x_1404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_extensions_1402_);
                    v___x_1414_ = v_reuseFailAlloc_1415_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_headers(
    mut v_builder_1420_: *mut leanh::LeanObject,
    mut v_headers_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v_status_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1428_: u8 = 0;
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1431_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1438_: u8 = 0;
    let mut v_unused_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1422_ = leanh::lean_ctor_get(v_builder_1420_, 0);
                v_extensions_1423_ = leanh::lean_ctor_get(v_builder_1420_, 1);
                v_isSharedCheck_1440_ = (!leanh::lean_is_exclusive(v_builder_1420_)) as u8;
                if v_isSharedCheck_1440_ == 0 {
                    v___x_1425_ = v_builder_1420_;
                    v_isShared_1426_ = v_isSharedCheck_1440_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1423_);
                    leanh::lean_inc(v_line_1422_);
                    leanh::lean_dec(v_builder_1420_);
                    v___x_1425_ = leanh::lean_box(0);
                    v_isShared_1426_ = v_isSharedCheck_1440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_status_1427_ = leanh::lean_ctor_get(v_line_1422_, 0);
                v_version_1428_ = leanh::lean_ctor_get_uint8(
                    v_line_1422_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1438_ = (!leanh::lean_is_exclusive(v_line_1422_)) as u8;
                if v_isSharedCheck_1438_ == 0 {
                    v_unused_1439_ = leanh::lean_ctor_get(v_line_1422_, 1);
                    leanh::lean_dec(v_unused_1439_);
                    v___x_1430_ = v_line_1422_;
                    v_isShared_1431_ = v_isSharedCheck_1438_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_status_1427_);
                    leanh::lean_dec(v_line_1422_);
                    v___x_1430_ = leanh::lean_box(0);
                    v_isShared_1431_ = v_isSharedCheck_1438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1431_ == 0 {
                    leanh::lean_ctor_set(v___x_1430_, 1, v_headers_1421_);
                    v___x_1433_ = v___x_1430_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1437_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_status_1427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_headers_1421_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1437_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_1428_,
                    );
                    v___x_1433_ = v_reuseFailAlloc_1437_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1426_ == 0 {
                    leanh::lean_ctor_set(v___x_1425_, 0, v___x_1433_);
                    v___x_1435_ = v___x_1425_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_extensions_1423_);
                    v___x_1435_ = v_reuseFailAlloc_1436_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(
    mut v_a_1441_: *mut leanh::LeanObject,
    mut v_x_1442_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1443_: u8 = 0;
    let mut v_key_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1442_) == 0 {
                    v___x_1443_ = 0;
                    return v___x_1443_;
                } else {
                    v_key_1444_ = leanh::lean_ctor_get(v_x_1442_, 0);
                    v_tail_1445_ = leanh::lean_ctor_get(v_x_1442_, 2);
                    v___x_1446_ = lean_string_dec_eq(v_key_1444_, v_a_1441_);
                    if v___x_1446_ == 0 {
                        v_x_1442_ = v_tail_1445_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1446_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(
    mut v_a_1448_: *mut leanh::LeanObject,
    mut v_x_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: u8 = 0;
    let mut v_r_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_1448_, v_x_1449_);
    leanh::lean_dec(v_x_1449_);
    leanh::lean_dec_ref(v_a_1448_);
    v_r_1451_ = leanh::lean_box((v_res_1450_) as usize);
    return v_r_1451_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1452_: *mut leanh::LeanObject,
    mut v_x_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u64 = 0;
    let mut v___x_1462_: u64 = 0;
    let mut v___x_1463_: u64 = 0;
    let mut v_fold_1464_: u64 = 0;
    let mut v___x_1465_: u64 = 0;
    let mut v___x_1466_: u64 = 0;
    let mut v___x_1467_: u64 = 0;
    let mut v___x_1468_: usize = 0;
    let mut v___x_1469_: usize = 0;
    let mut v___x_1470_: usize = 0;
    let mut v___x_1471_: usize = 0;
    let mut v___x_1472_: usize = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1453_) == 0 {
                    return v_x_1452_;
                } else {
                    v_key_1454_ = leanh::lean_ctor_get(v_x_1453_, 0);
                    v_value_1455_ = leanh::lean_ctor_get(v_x_1453_, 1);
                    v_tail_1456_ = leanh::lean_ctor_get(v_x_1453_, 2);
                    v_isSharedCheck_1479_ = (!leanh::lean_is_exclusive(v_x_1453_)) as u8;
                    if v_isSharedCheck_1479_ == 0 {
                        v___x_1458_ = v_x_1453_;
                        v_isShared_1459_ = v_isSharedCheck_1479_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1456_);
                        leanh::lean_inc(v_value_1455_);
                        leanh::lean_inc(v_key_1454_);
                        leanh::lean_dec(v_x_1453_);
                        v___x_1458_ = leanh::lean_box(0);
                        v_isShared_1459_ = v_isSharedCheck_1479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1460_ = lean_array_get_size(v_x_1452_);
                v___x_1461_ = lean_string_hash(v_key_1454_);
                v___x_1462_ = 32u64;
                v___x_1463_ = lean_uint64_shift_right(v___x_1461_, v___x_1462_);
                v_fold_1464_ = lean_uint64_xor(v___x_1461_, v___x_1463_);
                v___x_1465_ = 16u64;
                v___x_1466_ = lean_uint64_shift_right(v_fold_1464_, v___x_1465_);
                v___x_1467_ = lean_uint64_xor(v_fold_1464_, v___x_1466_);
                v___x_1468_ = lean_uint64_to_usize(v___x_1467_);
                v___x_1469_ = lean_usize_of_nat(v___x_1460_);
                v___x_1470_ = 1usize;
                v___x_1471_ = lean_usize_sub(v___x_1469_, v___x_1470_);
                v___x_1472_ = lean_usize_land(v___x_1468_, v___x_1471_);
                v___x_1473_ = lean_array_uget_borrowed(v_x_1452_, v___x_1472_);
                leanh::lean_inc(v___x_1473_);
                if v_isShared_1459_ == 0 {
                    leanh::lean_ctor_set(v___x_1458_, 2, v___x_1473_);
                    v___x_1475_ = v___x_1458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_key_1454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_value_1455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 2, v___x_1473_);
                    v___x_1475_ = v_reuseFailAlloc_1478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1476_ = lean_array_uset(v_x_1452_, v___x_1472_, v___x_1475_);
                v_x_1452_ = v___x_1476_;
                v_x_1453_ = v_tail_1456_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(
    mut v_i_1480_: *mut leanh::LeanObject,
    mut v_source_1481_: *mut leanh::LeanObject,
    mut v_target_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v_es_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1483_ = lean_array_get_size(v_source_1481_);
                v___x_1484_ = lean_nat_dec_lt(v_i_1480_, v___x_1483_);
                if v___x_1484_ == 0 {
                    leanh::lean_dec_ref(v_source_1481_);
                    leanh::lean_dec(v_i_1480_);
                    return v_target_1482_;
                } else {
                    v_es_1485_ = lean_array_fget(v_source_1481_, v_i_1480_);
                    v___x_1486_ = leanh::lean_box(0);
                    v_source_1487_ = lean_array_fset(v_source_1481_, v_i_1480_, v___x_1486_);
                    v_target_1488_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1482_, v_es_1485_);
                    v___x_1489_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1490_ = lean_nat_add(v_i_1480_, v___x_1489_);
                    leanh::lean_dec(v_i_1480_);
                    v_i_1480_ = v___x_1490_;
                    v_source_1481_ = v_source_1487_;
                    v_target_1482_ = v_target_1488_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(
    mut v_data_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = lean_array_get_size(v_data_1492_);
    v___x_1494_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1495_ = lean_nat_mul(v___x_1493_, v___x_1494_);
    v___x_1496_ = leanh::lean_unsigned_to_nat(0);
    v___x_1497_ = leanh::lean_box(0);
    v___x_1498_ = lean_mk_array(v_nbuckets_1495_, v___x_1497_);
    v___x_1499_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1496_, v_data_1492_, v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(
    mut v_i_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1501_) == 0 {
                    v___x_1502_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
                    v___x_1504_ = lean_array_push(v___x_1503_, v_i_1500_);
                    v___x_1505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                    return v___x_1505_;
                } else {
                    v_val_1506_ = leanh::lean_ctor_get(v_x_1501_, 0);
                    v_isSharedCheck_1514_ = (!leanh::lean_is_exclusive(v_x_1501_)) as u8;
                    if v_isSharedCheck_1514_ == 0 {
                        v___x_1508_ = v_x_1501_;
                        v_isShared_1509_ = v_isSharedCheck_1514_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1506_);
                        leanh::lean_dec(v_x_1501_);
                        v___x_1508_ = leanh::lean_box(0);
                        v_isShared_1509_ = v_isSharedCheck_1514_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1510_ = lean_array_push(v_val_1506_, v_i_1500_);
                if v_isShared_1509_ == 0 {
                    leanh::lean_ctor_set(v___x_1508_, 0, v___x_1510_);
                    v___x_1512_ = v___x_1508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
                    v___x_1512_ = v_reuseFailAlloc_1513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(
    mut v_i_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_x_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1528_: u8 = 0;
    let mut v_tail_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1517_) == 0 {
                    v___x_1518_ = leanh::lean_box(0);
                    v___x_1519_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_1515_, v___x_1518_);
                    v_val_1520_ = leanh::lean_ctor_get(v___x_1519_, 0);
                    leanh::lean_inc(v_val_1520_);
                    leanh::lean_dec(v___x_1519_);
                    v___x_1521_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1521_, 0, v_a_1516_);
                    leanh::lean_ctor_set(v___x_1521_, 1, v_val_1520_);
                    leanh::lean_ctor_set(v___x_1521_, 2, v_x_1517_);
                    return v___x_1521_;
                } else {
                    v_key_1522_ = leanh::lean_ctor_get(v_x_1517_, 0);
                    v_value_1523_ = leanh::lean_ctor_get(v_x_1517_, 1);
                    v_tail_1524_ = leanh::lean_ctor_get(v_x_1517_, 2);
                    v_isSharedCheck_1539_ = (!leanh::lean_is_exclusive(v_x_1517_)) as u8;
                    if v_isSharedCheck_1539_ == 0 {
                        v___x_1526_ = v_x_1517_;
                        v_isShared_1527_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1524_);
                        leanh::lean_inc(v_value_1523_);
                        leanh::lean_inc(v_key_1522_);
                        leanh::lean_dec(v_x_1517_);
                        v___x_1526_ = leanh::lean_box(0);
                        v_isShared_1527_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1528_ = lean_string_dec_eq(v_key_1522_, v_a_1516_);
                if v___x_1528_ == 0 {
                    v_tail_1529_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_1515_, v_a_1516_, v_tail_1524_);
                    if v_isShared_1527_ == 0 {
                        leanh::lean_ctor_set(v___x_1526_, 2, v_tail_1529_);
                        v___x_1531_ = v___x_1526_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1532_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_key_1522_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_value_1523_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_tail_1529_);
                        v___x_1531_ = v_reuseFailAlloc_1532_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_1522_);
                    v___x_1533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1533_, 0, v_value_1523_);
                    v___x_1534_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_1515_, v___x_1533_);
                    v_val_1535_ = leanh::lean_ctor_get(v___x_1534_, 0);
                    leanh::lean_inc(v_val_1535_);
                    leanh::lean_dec(v___x_1534_);
                    if v_isShared_1527_ == 0 {
                        leanh::lean_ctor_set(v___x_1526_, 1, v_val_1535_);
                        leanh::lean_ctor_set(v___x_1526_, 0, v_a_1516_);
                        v___x_1537_ = v___x_1526_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1538_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1516_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_val_1535_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_tail_1524_);
                        v___x_1537_ = v_reuseFailAlloc_1538_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1531_;
            }
            3 => {
                return v___x_1537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(
    mut v_i_1540_: *mut leanh::LeanObject,
    mut v_m_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1547_: u8 = 0;
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u64 = 0;
    let mut v___x_1550_: u64 = 0;
    let mut v___x_1551_: u64 = 0;
    let mut v_fold_1552_: u64 = 0;
    let mut v___x_1553_: u64 = 0;
    let mut v___x_1554_: u64 = 0;
    let mut v___x_1555_: u64 = 0;
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: usize = 0;
    let mut v___x_1558_: usize = 0;
    let mut v___x_1559_: usize = 0;
    let mut v___x_1560_: usize = 0;
    let mut v_bkt_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v_val_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1543_ = leanh::lean_ctor_get(v_m_1541_, 0);
                v_buckets_1544_ = leanh::lean_ctor_get(v_m_1541_, 1);
                v_isSharedCheck_1594_ = (!leanh::lean_is_exclusive(v_m_1541_)) as u8;
                if v_isSharedCheck_1594_ == 0 {
                    v___x_1546_ = v_m_1541_;
                    v_isShared_1547_ = v_isSharedCheck_1594_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1544_);
                    leanh::lean_inc(v_size_1543_);
                    leanh::lean_dec(v_m_1541_);
                    v___x_1546_ = leanh::lean_box(0);
                    v_isShared_1547_ = v_isSharedCheck_1594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1548_ = lean_array_get_size(v_buckets_1544_);
                v___x_1549_ = lean_string_hash(v_a_1542_);
                v___x_1550_ = 32u64;
                v___x_1551_ = lean_uint64_shift_right(v___x_1549_, v___x_1550_);
                v_fold_1552_ = lean_uint64_xor(v___x_1549_, v___x_1551_);
                v___x_1553_ = 16u64;
                v___x_1554_ = lean_uint64_shift_right(v_fold_1552_, v___x_1553_);
                v___x_1555_ = lean_uint64_xor(v_fold_1552_, v___x_1554_);
                v___x_1556_ = lean_uint64_to_usize(v___x_1555_);
                v___x_1557_ = lean_usize_of_nat(v___x_1548_);
                v___x_1558_ = 1usize;
                v___x_1559_ = lean_usize_sub(v___x_1557_, v___x_1558_);
                v___x_1560_ = lean_usize_land(v___x_1556_, v___x_1559_);
                v_bkt_1561_ = lean_array_uget_borrowed(v_buckets_1544_, v___x_1560_);
                v___x_1562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_1542_, v_bkt_1561_);
                if v___x_1562_ == 0 {
                    v___x_1563_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
                    v___x_1565_ = lean_array_push(v___x_1564_, v_i_1540_);
                    v_size_x27_1566_ = lean_nat_add(v_size_1543_, v___x_1563_);
                    leanh::lean_dec(v_size_1543_);
                    leanh::lean_inc(v_bkt_1561_);
                    v___x_1567_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1567_, 0, v_a_1542_);
                    leanh::lean_ctor_set(v___x_1567_, 1, v___x_1565_);
                    leanh::lean_ctor_set(v___x_1567_, 2, v_bkt_1561_);
                    v_buckets_x27_1568_ =
                        lean_array_uset(v_buckets_1544_, v___x_1560_, v___x_1567_);
                    v___x_1569_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1570_ = lean_nat_mul(v_size_x27_1566_, v___x_1569_);
                    v___x_1571_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1572_ = lean_nat_div(v___x_1570_, v___x_1571_);
                    leanh::lean_dec(v___x_1570_);
                    v___x_1573_ = lean_array_get_size(v_buckets_x27_1568_);
                    v___x_1574_ = lean_nat_dec_le(v___x_1572_, v___x_1573_);
                    leanh::lean_dec(v___x_1572_);
                    if v___x_1574_ == 0 {
                        v_val_1575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1568_);
                        if v_isShared_1547_ == 0 {
                            leanh::lean_ctor_set(v___x_1546_, 1, v_val_1575_);
                            leanh::lean_ctor_set(v___x_1546_, 0, v_size_x27_1566_);
                            v___x_1577_ = v___x_1546_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1578_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1578_,
                                0,
                                v_size_x27_1566_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_val_1575_);
                            v___x_1577_ = v_reuseFailAlloc_1578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1547_ == 0 {
                            leanh::lean_ctor_set(v___x_1546_, 1, v_buckets_x27_1568_);
                            leanh::lean_ctor_set(v___x_1546_, 0, v_size_x27_1566_);
                            v___x_1580_ = v___x_1546_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1581_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1581_,
                                0,
                                v_size_x27_1566_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1581_,
                                1,
                                v_buckets_x27_1568_,
                            );
                            v___x_1580_ = v_reuseFailAlloc_1581_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1561_);
                    v___x_1582_ = leanh::lean_box(0);
                    v_buckets_x27_1583_ =
                        lean_array_uset(v_buckets_1544_, v___x_1560_, v___x_1582_);
                    leanh::lean_inc_ref(v_a_1542_);
                    v_bkt_x27_1584_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_1540_, v_a_1542_, v_bkt_1561_);
                    v___x_1591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_1542_, v_bkt_x27_1584_);
                    leanh::lean_dec_ref(v_a_1542_);
                    if v___x_1591_ == 0 {
                        v___x_1592_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1593_ = lean_nat_sub(v_size_1543_, v___x_1592_);
                        leanh::lean_dec(v_size_1543_);
                        v___y_1586_ = v___x_1593_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1586_ = v_size_1543_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1577_;
            }
            3 => {
                return v___x_1580_;
            }
            4 => {
                v___x_1587_ = lean_array_uset(v_buckets_x27_1583_, v___x_1560_, v_bkt_x27_1584_);
                if v_isShared_1547_ == 0 {
                    leanh::lean_ctor_set(v___x_1546_, 1, v___x_1587_);
                    leanh::lean_ctor_set(v___x_1546_, 0, v___y_1586_);
                    v___x_1589_ = v___x_1546_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___y_1586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1587_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_header(
    mut v_builder_1595_: *mut leanh::LeanObject,
    mut v_key_1596_: *mut leanh::LeanObject,
    mut v_value_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v_status_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1605_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v_entries_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v_i_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_unused_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut v_unused_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1598_ = leanh::lean_ctor_get(v_builder_1595_, 0);
                leanh::lean_inc_ref(v_line_1598_);
                v_headers_1599_ = leanh::lean_ctor_get(v_line_1598_, 1);
                leanh::lean_inc_ref(v_headers_1599_);
                v_extensions_1600_ = leanh::lean_ctor_get(v_builder_1595_, 1);
                v_isSharedCheck_1630_ = (!leanh::lean_is_exclusive(v_builder_1595_)) as u8;
                if v_isSharedCheck_1630_ == 0 {
                    v_unused_1631_ = leanh::lean_ctor_get(v_builder_1595_, 0);
                    leanh::lean_dec(v_unused_1631_);
                    v___x_1602_ = v_builder_1595_;
                    v_isShared_1603_ = v_isSharedCheck_1630_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1600_);
                    leanh::lean_dec(v_builder_1595_);
                    v___x_1602_ = leanh::lean_box(0);
                    v_isShared_1603_ = v_isSharedCheck_1630_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_status_1604_ = leanh::lean_ctor_get(v_line_1598_, 0);
                v_version_1605_ = leanh::lean_ctor_get_uint8(
                    v_line_1598_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1628_ = (!leanh::lean_is_exclusive(v_line_1598_)) as u8;
                if v_isSharedCheck_1628_ == 0 {
                    v_unused_1629_ = leanh::lean_ctor_get(v_line_1598_, 1);
                    leanh::lean_dec(v_unused_1629_);
                    v___x_1607_ = v_line_1598_;
                    v_isShared_1608_ = v_isSharedCheck_1628_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_status_1604_);
                    leanh::lean_dec(v_line_1598_);
                    v___x_1607_ = leanh::lean_box(0);
                    v_isShared_1608_ = v_isSharedCheck_1628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_1609_ = leanh::lean_ctor_get(v_headers_1599_, 0);
                v_indexes_1610_ = leanh::lean_ctor_get(v_headers_1599_, 1);
                v_isSharedCheck_1627_ = (!leanh::lean_is_exclusive(v_headers_1599_)) as u8;
                if v_isSharedCheck_1627_ == 0 {
                    v___x_1612_ = v_headers_1599_;
                    v_isShared_1613_ = v_isSharedCheck_1627_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1610_);
                    leanh::lean_inc(v_entries_1609_);
                    leanh::lean_dec(v_headers_1599_);
                    v___x_1612_ = leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_1614_ = lean_array_get_size(v_entries_1609_);
                leanh::lean_inc_ref(v_key_1596_);
                v___x_1615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1615_, 0, v_key_1596_);
                leanh::lean_ctor_set(v___x_1615_, 1, v_value_1597_);
                v_entries_1616_ = lean_array_push(v_entries_1609_, v___x_1615_);
                v_indexes_1617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_1614_, v_indexes_1610_, v_key_1596_);
                if v_isShared_1613_ == 0 {
                    leanh::lean_ctor_set(v___x_1612_, 1, v_indexes_1617_);
                    leanh::lean_ctor_set(v___x_1612_, 0, v_entries_1616_);
                    v___x_1619_ = v___x_1612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_entries_1616_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_indexes_1617_);
                    v___x_1619_ = v_reuseFailAlloc_1626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1608_ == 0 {
                    leanh::lean_ctor_set(v___x_1607_, 1, v___x_1619_);
                    v___x_1621_ = v___x_1607_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_status_1604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1619_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1625_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_1605_,
                    );
                    v___x_1621_ = v_reuseFailAlloc_1625_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1603_ == 0 {
                    leanh::lean_ctor_set(v___x_1602_, 0, v___x_1621_);
                    v___x_1623_ = v___x_1602_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_extensions_1600_);
                    v___x_1623_ = v_reuseFailAlloc_1624_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(
    mut v_00_u03b2_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_x_1634_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1635_: u8 = 0;
    v___x_1635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_1633_, v_x_1634_);
    return v___x_1635_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(
    mut v_00_u03b2_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
    mut v_x_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1639_: u8 = 0;
    let mut v_r_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_1636_, v_a_1637_, v_x_1638_);
    leanh::lean_dec(v_x_1638_);
    leanh::lean_dec_ref(v_a_1637_);
    v_r_1640_ = leanh::lean_box((v_res_1639_) as usize);
    return v_r_1640_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_data_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_1642_);
    return v___x_1643_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1644_: *mut leanh::LeanObject,
    mut v_i_1645_: *mut leanh::LeanObject,
    mut v_source_1646_: *mut leanh::LeanObject,
    mut v_target_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1645_, v_source_1646_, v_target_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1649_: *mut leanh::LeanObject,
    mut v_x_1650_: *mut leanh::LeanObject,
    mut v_x_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1650_, v_x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_Http_Response_Builder_header_x21(
    mut v_builder_1653_: *mut leanh::LeanObject,
    mut v_key_1654_: *mut leanh::LeanObject,
    mut v_value_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v_status_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1663_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v_entries_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v_key_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_unused_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1656_ = leanh::lean_ctor_get(v_builder_1653_, 0);
                leanh::lean_inc_ref(v_line_1656_);
                v_headers_1657_ = leanh::lean_ctor_get(v_line_1656_, 1);
                leanh::lean_inc_ref(v_headers_1657_);
                v_extensions_1658_ = leanh::lean_ctor_get(v_builder_1653_, 1);
                v_isSharedCheck_1690_ = (!leanh::lean_is_exclusive(v_builder_1653_)) as u8;
                if v_isSharedCheck_1690_ == 0 {
                    v_unused_1691_ = leanh::lean_ctor_get(v_builder_1653_, 0);
                    leanh::lean_dec(v_unused_1691_);
                    v___x_1660_ = v_builder_1653_;
                    v_isShared_1661_ = v_isSharedCheck_1690_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1658_);
                    leanh::lean_dec(v_builder_1653_);
                    v___x_1660_ = leanh::lean_box(0);
                    v_isShared_1661_ = v_isSharedCheck_1690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_status_1662_ = leanh::lean_ctor_get(v_line_1656_, 0);
                v_version_1663_ = leanh::lean_ctor_get_uint8(
                    v_line_1656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1688_ = (!leanh::lean_is_exclusive(v_line_1656_)) as u8;
                if v_isSharedCheck_1688_ == 0 {
                    v_unused_1689_ = leanh::lean_ctor_get(v_line_1656_, 1);
                    leanh::lean_dec(v_unused_1689_);
                    v___x_1665_ = v_line_1656_;
                    v_isShared_1666_ = v_isSharedCheck_1688_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_status_1662_);
                    leanh::lean_dec(v_line_1656_);
                    v___x_1665_ = leanh::lean_box(0);
                    v_isShared_1666_ = v_isSharedCheck_1688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_1667_ = leanh::lean_ctor_get(v_headers_1657_, 0);
                v_indexes_1668_ = leanh::lean_ctor_get(v_headers_1657_, 1);
                v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v_headers_1657_)) as u8;
                if v_isSharedCheck_1687_ == 0 {
                    v___x_1670_ = v_headers_1657_;
                    v_isShared_1671_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1668_);
                    leanh::lean_inc(v_entries_1667_);
                    leanh::lean_dec(v_headers_1657_);
                    v___x_1670_ = leanh::lean_box(0);
                    v_isShared_1671_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_key_1672_ = l_Std_Http_Header_Name_ofString_x21(v_key_1654_);
                v_value_1673_ = l_Std_Http_Header_Value_ofString_x21(v_value_1655_);
                v_i_1674_ = lean_array_get_size(v_entries_1667_);
                leanh::lean_inc_ref(v_key_1672_);
                v___x_1675_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1675_, 0, v_key_1672_);
                leanh::lean_ctor_set(v___x_1675_, 1, v_value_1673_);
                v_entries_1676_ = lean_array_push(v_entries_1667_, v___x_1675_);
                v_indexes_1677_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_1674_, v_indexes_1668_, v_key_1672_);
                if v_isShared_1671_ == 0 {
                    leanh::lean_ctor_set(v___x_1670_, 1, v_indexes_1677_);
                    leanh::lean_ctor_set(v___x_1670_, 0, v_entries_1676_);
                    v___x_1679_ = v___x_1670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_entries_1676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_indexes_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1666_ == 0 {
                    leanh::lean_ctor_set(v___x_1665_, 1, v___x_1679_);
                    v___x_1681_ = v___x_1665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_status_1662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1679_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1685_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_1663_,
                    );
                    v___x_1681_ = v_reuseFailAlloc_1685_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1661_ == 0 {
                    leanh::lean_ctor_set(v___x_1660_, 0, v___x_1681_);
                    v___x_1683_ = v___x_1660_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_extensions_1658_);
                    v___x_1683_ = v_reuseFailAlloc_1684_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_header_x3f(
    mut v_builder_1692_: *mut leanh::LeanObject,
    mut v_key_1693_: *mut leanh::LeanObject,
    mut v_value_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headers_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v_extensions_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v_status_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1711_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v_entries_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_i_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_unused_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_unused_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1695_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1693_);
                if leanh::lean_obj_tag(v___x_1695_) == 0 {
                    leanh::lean_dec_ref(v_value_1694_);
                    leanh::lean_dec_ref(v_builder_1692_);
                    v___x_1696_ = leanh::lean_box(0);
                    return v___x_1696_;
                } else {
                    v_val_1697_ = leanh::lean_ctor_get(v___x_1695_, 0);
                    leanh::lean_inc(v_val_1697_);
                    leanh::lean_dec_ref_known(v___x_1695_, 1);
                    v___x_1698_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1694_);
                    if leanh::lean_obj_tag(v___x_1698_) == 0 {
                        leanh::lean_dec(v_val_1697_);
                        leanh::lean_dec_ref(v_builder_1692_);
                        v___x_1699_ = leanh::lean_box(0);
                        return v___x_1699_;
                    } else {
                        v_line_1700_ = leanh::lean_ctor_get(v_builder_1692_, 0);
                        leanh::lean_inc_ref(v_line_1700_);
                        v_headers_1701_ = leanh::lean_ctor_get(v_line_1700_, 1);
                        leanh::lean_inc_ref(v_headers_1701_);
                        v_val_1702_ = leanh::lean_ctor_get(v___x_1698_, 0);
                        v_isSharedCheck_1741_ =
                            (!leanh::lean_is_exclusive(v___x_1698_)) as u8;
                        if v_isSharedCheck_1741_ == 0 {
                            v___x_1704_ = v___x_1698_;
                            v_isShared_1705_ = v_isSharedCheck_1741_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1702_);
                            leanh::lean_dec(v___x_1698_);
                            v___x_1704_ = leanh::lean_box(0);
                            v_isShared_1705_ = v_isSharedCheck_1741_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_extensions_1706_ = leanh::lean_ctor_get(v_builder_1692_, 1);
                v_isSharedCheck_1739_ = (!leanh::lean_is_exclusive(v_builder_1692_)) as u8;
                if v_isSharedCheck_1739_ == 0 {
                    v_unused_1740_ = leanh::lean_ctor_get(v_builder_1692_, 0);
                    leanh::lean_dec(v_unused_1740_);
                    v___x_1708_ = v_builder_1692_;
                    v_isShared_1709_ = v_isSharedCheck_1739_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1706_);
                    leanh::lean_dec(v_builder_1692_);
                    v___x_1708_ = leanh::lean_box(0);
                    v_isShared_1709_ = v_isSharedCheck_1739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_status_1710_ = leanh::lean_ctor_get(v_line_1700_, 0);
                v_version_1711_ = leanh::lean_ctor_get_uint8(
                    v_line_1700_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1737_ = (!leanh::lean_is_exclusive(v_line_1700_)) as u8;
                if v_isSharedCheck_1737_ == 0 {
                    v_unused_1738_ = leanh::lean_ctor_get(v_line_1700_, 1);
                    leanh::lean_dec(v_unused_1738_);
                    v___x_1713_ = v_line_1700_;
                    v_isShared_1714_ = v_isSharedCheck_1737_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_status_1710_);
                    leanh::lean_dec(v_line_1700_);
                    v___x_1713_ = leanh::lean_box(0);
                    v_isShared_1714_ = v_isSharedCheck_1737_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_entries_1715_ = leanh::lean_ctor_get(v_headers_1701_, 0);
                v_indexes_1716_ = leanh::lean_ctor_get(v_headers_1701_, 1);
                v_isSharedCheck_1736_ = (!leanh::lean_is_exclusive(v_headers_1701_)) as u8;
                if v_isSharedCheck_1736_ == 0 {
                    v___x_1718_ = v_headers_1701_;
                    v_isShared_1719_ = v_isSharedCheck_1736_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1716_);
                    leanh::lean_inc(v_entries_1715_);
                    leanh::lean_dec(v_headers_1701_);
                    v___x_1718_ = leanh::lean_box(0);
                    v_isShared_1719_ = v_isSharedCheck_1736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_i_1720_ = lean_array_get_size(v_entries_1715_);
                leanh::lean_inc(v_val_1697_);
                v___x_1721_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1721_, 0, v_val_1697_);
                leanh::lean_ctor_set(v___x_1721_, 1, v_val_1702_);
                v_entries_1722_ = lean_array_push(v_entries_1715_, v___x_1721_);
                v_indexes_1723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_1720_, v_indexes_1716_, v_val_1697_);
                if v_isShared_1719_ == 0 {
                    leanh::lean_ctor_set(v___x_1718_, 1, v_indexes_1723_);
                    leanh::lean_ctor_set(v___x_1718_, 0, v_entries_1722_);
                    v___x_1725_ = v___x_1718_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_entries_1722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_indexes_1723_);
                    v___x_1725_ = v_reuseFailAlloc_1735_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1714_ == 0 {
                    leanh::lean_ctor_set(v___x_1713_, 1, v___x_1725_);
                    v___x_1727_ = v___x_1713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_status_1710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1725_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1734_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_1711_,
                    );
                    v___x_1727_ = v_reuseFailAlloc_1734_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1709_ == 0 {
                    leanh::lean_ctor_set(v___x_1708_, 0, v___x_1727_);
                    v___x_1729_ = v___x_1708_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_extensions_1706_);
                    v___x_1729_ = v_reuseFailAlloc_1733_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1705_ == 0 {
                    leanh::lean_ctor_set(v___x_1704_, 0, v___x_1729_);
                    v___x_1731_ = v___x_1704_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
                    v___x_1731_ = v_reuseFailAlloc_1732_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_extension___redArg(
    mut v_builder_1743_: *mut leanh::LeanObject,
    mut v_inst_1744_: *mut leanh::LeanObject,
    mut v_data_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v_dyn_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1746_ = leanh::lean_ctor_get(v_builder_1743_, 0);
                v_extensions_1747_ = leanh::lean_ctor_get(v_builder_1743_, 1);
                v_isSharedCheck_1758_ = (!leanh::lean_is_exclusive(v_builder_1743_)) as u8;
                if v_isSharedCheck_1758_ == 0 {
                    v___x_1749_ = v_builder_1743_;
                    v_isShared_1750_ = v_isSharedCheck_1758_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1747_);
                    leanh::lean_inc(v_line_1746_);
                    leanh::lean_dec(v_builder_1743_);
                    v___x_1749_ = leanh::lean_box(0);
                    v_isShared_1750_ = v_isSharedCheck_1758_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dyn_1751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_dyn_1751_, 0, v_inst_1744_);
                leanh::lean_ctor_set(v_dyn_1751_, 1, v_data_1745_);
                v___x_1752_ = l_Std_Http_Response_Builder_extension___redArg___closed__0;
                v___x_1753_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1751_);
                v___x_1754_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_1752_,
                    v___x_1753_,
                    v_dyn_1751_,
                    v_extensions_1747_,
                );
                if v_isShared_1750_ == 0 {
                    leanh::lean_ctor_set(v___x_1749_, 1, v___x_1754_);
                    v___x_1756_ = v___x_1749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_line_1746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1754_);
                    v___x_1756_ = v_reuseFailAlloc_1757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_extension(
    mut v_00_u03b1_1759_: *mut leanh::LeanObject,
    mut v_builder_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
    mut v_data_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ =
        l_Std_Http_Response_Builder_extension___redArg(v_builder_1760_, v_inst_1761_, v_data_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Std_Http_Response_Builder_body___redArg(
    mut v_builder_1764_: *mut leanh::LeanObject,
    mut v_body_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_line_1766_ = leanh::lean_ctor_get(v_builder_1764_, 0);
    v_extensions_1767_ = leanh::lean_ctor_get(v_builder_1764_, 1);
    leanh::lean_inc(v_extensions_1767_);
    leanh::lean_inc_ref(v_line_1766_);
    v___x_1768_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1768_, 0, v_line_1766_);
    leanh::lean_ctor_set(v___x_1768_, 1, v_body_1765_);
    leanh::lean_ctor_set(v___x_1768_, 2, v_extensions_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Std_Http_Response_Builder_body___redArg___boxed(
    mut v_builder_1769_: *mut leanh::LeanObject,
    mut v_body_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Std_Http_Response_Builder_body___redArg(v_builder_1769_, v_body_1770_);
    leanh::lean_dec_ref(v_builder_1769_);
    return v_res_1771_;
}
pub unsafe fn l_Std_Http_Response_Builder_body(
    mut v_t_1772_: *mut leanh::LeanObject,
    mut v_builder_1773_: *mut leanh::LeanObject,
    mut v_body_1774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1775_ = l_Std_Http_Response_Builder_body___redArg(v_builder_1773_, v_body_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Std_Http_Response_Builder_body___boxed(
    mut v_t_1776_: *mut leanh::LeanObject,
    mut v_builder_1777_: *mut leanh::LeanObject,
    mut v_body_1778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1779_ = l_Std_Http_Response_Builder_body(v_t_1776_, v_builder_1777_, v_body_1778_);
    leanh::lean_dec_ref(v_builder_1777_);
    return v_res_1779_;
}
pub unsafe fn l_Std_Http_Response_Builder_build___redArg(
    mut v_inst_1780_: *mut leanh::LeanObject,
    mut v_builder_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_line_1782_ = leanh::lean_ctor_get(v_builder_1781_, 0);
    v_extensions_1783_ = leanh::lean_ctor_get(v_builder_1781_, 1);
    leanh::lean_inc(v_extensions_1783_);
    leanh::lean_inc_ref(v_line_1782_);
    v___x_1784_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v_line_1782_);
    leanh::lean_ctor_set(v___x_1784_, 1, v_inst_1780_);
    leanh::lean_ctor_set(v___x_1784_, 2, v_extensions_1783_);
    return v___x_1784_;
}
pub unsafe fn l_Std_Http_Response_Builder_build___redArg___boxed(
    mut v_inst_1785_: *mut leanh::LeanObject,
    mut v_builder_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_Http_Response_Builder_build___redArg(v_inst_1785_, v_builder_1786_);
    leanh::lean_dec_ref(v_builder_1786_);
    return v_res_1787_;
}
pub unsafe fn l_Std_Http_Response_Builder_build(
    mut v_t_1788_: *mut leanh::LeanObject,
    mut v_inst_1789_: *mut leanh::LeanObject,
    mut v_builder_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = l_Std_Http_Response_Builder_build___redArg(v_inst_1789_, v_builder_1790_);
    return v___x_1791_;
}
pub unsafe fn l_Std_Http_Response_Builder_build___boxed(
    mut v_t_1792_: *mut leanh::LeanObject,
    mut v_inst_1793_: *mut leanh::LeanObject,
    mut v_builder_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Std_Http_Response_Builder_build(v_t_1792_, v_inst_1793_, v_builder_1794_);
    leanh::lean_dec_ref(v_builder_1794_);
    return v_res_1795_;
}
pub unsafe fn _init_l_Std_Http_Response_ok___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = leanh::lean_box(4);
    v___x_1797_ = l_Std_Http_Response_Builder_new;
    v___x_1798_ = l_Std_Http_Response_Builder_status(v___x_1797_, v___x_1796_);
    return v___x_1798_;
}
pub unsafe fn _init_l_Std_Http_Response_ok() -> *mut leanh::LeanObject {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_ok___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_ok___closed__0_once),
        _init_l_Std_Http_Response_ok___closed__0,
    );
    return v___x_1799_;
}
pub unsafe fn l_Std_Http_Response_withStatus(
    mut v_status_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = l_Std_Http_Response_Builder_new;
    v___x_1802_ = l_Std_Http_Response_Builder_status(v___x_1801_, v_status_1800_);
    return v___x_1802_;
}
pub unsafe fn _init_l_Std_Http_Response_notFound___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = leanh::lean_box(27);
    v___x_1804_ = l_Std_Http_Response_Builder_new;
    v___x_1805_ = l_Std_Http_Response_Builder_status(v___x_1804_, v___x_1803_);
    return v___x_1805_;
}
pub unsafe fn _init_l_Std_Http_Response_notFound() -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_notFound___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_notFound___closed__0_once),
        _init_l_Std_Http_Response_notFound___closed__0,
    );
    return v___x_1806_;
}
pub unsafe fn _init_l_Std_Http_Response_internalServerError___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = leanh::lean_box(52);
    v___x_1808_ = l_Std_Http_Response_Builder_new;
    v___x_1809_ = l_Std_Http_Response_Builder_status(v___x_1808_, v___x_1807_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Std_Http_Response_internalServerError() -> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_internalServerError___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_internalServerError___closed__0_once),
        _init_l_Std_Http_Response_internalServerError___closed__0,
    );
    return v___x_1810_;
}
pub unsafe fn _init_l_Std_Http_Response_badRequest___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = leanh::lean_box(23);
    v___x_1812_ = l_Std_Http_Response_Builder_new;
    v___x_1813_ = l_Std_Http_Response_Builder_status(v___x_1812_, v___x_1811_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Std_Http_Response_badRequest() -> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_badRequest___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_badRequest___closed__0_once),
        _init_l_Std_Http_Response_badRequest___closed__0,
    );
    return v___x_1814_;
}
pub unsafe fn _init_l_Std_Http_Response_created___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = leanh::lean_box(5);
    v___x_1816_ = l_Std_Http_Response_Builder_new;
    v___x_1817_ = l_Std_Http_Response_Builder_status(v___x_1816_, v___x_1815_);
    return v___x_1817_;
}
pub unsafe fn _init_l_Std_Http_Response_created() -> *mut leanh::LeanObject {
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_created___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_created___closed__0_once),
        _init_l_Std_Http_Response_created___closed__0,
    );
    return v___x_1818_;
}
pub unsafe fn _init_l_Std_Http_Response_accepted___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = leanh::lean_box(6);
    v___x_1820_ = l_Std_Http_Response_Builder_new;
    v___x_1821_ = l_Std_Http_Response_Builder_status(v___x_1820_, v___x_1819_);
    return v___x_1821_;
}
pub unsafe fn _init_l_Std_Http_Response_accepted() -> *mut leanh::LeanObject {
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_accepted___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_accepted___closed__0_once),
        _init_l_Std_Http_Response_accepted___closed__0,
    );
    return v___x_1822_;
}
pub unsafe fn _init_l_Std_Http_Response_unauthorized___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ = leanh::lean_box(24);
    v___x_1824_ = l_Std_Http_Response_Builder_new;
    v___x_1825_ = l_Std_Http_Response_Builder_status(v___x_1824_, v___x_1823_);
    return v___x_1825_;
}
pub unsafe fn _init_l_Std_Http_Response_unauthorized() -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_unauthorized___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_unauthorized___closed__0_once),
        _init_l_Std_Http_Response_unauthorized___closed__0,
    );
    return v___x_1826_;
}
pub unsafe fn _init_l_Std_Http_Response_forbidden___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = leanh::lean_box(26);
    v___x_1828_ = l_Std_Http_Response_Builder_new;
    v___x_1829_ = l_Std_Http_Response_Builder_status(v___x_1828_, v___x_1827_);
    return v___x_1829_;
}
pub unsafe fn _init_l_Std_Http_Response_forbidden() -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_forbidden___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_forbidden___closed__0_once),
        _init_l_Std_Http_Response_forbidden___closed__0,
    );
    return v___x_1830_;
}
pub unsafe fn _init_l_Std_Http_Response_conflict___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = leanh::lean_box(32);
    v___x_1832_ = l_Std_Http_Response_Builder_new;
    v___x_1833_ = l_Std_Http_Response_Builder_status(v___x_1832_, v___x_1831_);
    return v___x_1833_;
}
pub unsafe fn _init_l_Std_Http_Response_conflict() -> *mut leanh::LeanObject {
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_conflict___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_conflict___closed__0_once),
        _init_l_Std_Http_Response_conflict___closed__0,
    );
    return v___x_1834_;
}
pub unsafe fn _init_l_Std_Http_Response_serviceUnavailable___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = leanh::lean_box(55);
    v___x_1836_ = l_Std_Http_Response_Builder_new;
    v___x_1837_ = l_Std_Http_Response_Builder_status(v___x_1836_, v___x_1835_);
    return v___x_1837_;
}
pub unsafe fn _init_l_Std_Http_Response_serviceUnavailable() -> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Response_serviceUnavailable___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Response_serviceUnavailable___closed__0_once),
        _init_l_Std_Http_Response_serviceUnavailable___closed__0,
    );
    return v___x_1838_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Response(
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
    res = runtime_initialize_Std_Http_Data_Status(builtin);
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
    l_Std_Http_Response_instInhabitedHead_default =
        _init_l_Std_Http_Response_instInhabitedHead_default();
    leanh::lean_mark_persistent(l_Std_Http_Response_instInhabitedHead_default);
    l_Std_Http_Response_instInhabitedHead = _init_l_Std_Http_Response_instInhabitedHead();
    leanh::lean_mark_persistent(l_Std_Http_Response_instInhabitedHead);
    l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1 =
        _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1,
    );
    l_Std_Http_Response_new = _init_l_Std_Http_Response_new();
    leanh::lean_mark_persistent(l_Std_Http_Response_new);
    l_Std_Http_Response_Builder_new = _init_l_Std_Http_Response_Builder_new();
    leanh::lean_mark_persistent(l_Std_Http_Response_Builder_new);
    l_Std_Http_Response_ok = _init_l_Std_Http_Response_ok();
    leanh::lean_mark_persistent(l_Std_Http_Response_ok);
    l_Std_Http_Response_notFound = _init_l_Std_Http_Response_notFound();
    leanh::lean_mark_persistent(l_Std_Http_Response_notFound);
    l_Std_Http_Response_internalServerError = _init_l_Std_Http_Response_internalServerError();
    leanh::lean_mark_persistent(l_Std_Http_Response_internalServerError);
    l_Std_Http_Response_badRequest = _init_l_Std_Http_Response_badRequest();
    leanh::lean_mark_persistent(l_Std_Http_Response_badRequest);
    l_Std_Http_Response_created = _init_l_Std_Http_Response_created();
    leanh::lean_mark_persistent(l_Std_Http_Response_created);
    l_Std_Http_Response_accepted = _init_l_Std_Http_Response_accepted();
    leanh::lean_mark_persistent(l_Std_Http_Response_accepted);
    l_Std_Http_Response_unauthorized = _init_l_Std_Http_Response_unauthorized();
    leanh::lean_mark_persistent(l_Std_Http_Response_unauthorized);
    l_Std_Http_Response_forbidden = _init_l_Std_Http_Response_forbidden();
    leanh::lean_mark_persistent(l_Std_Http_Response_forbidden);
    l_Std_Http_Response_conflict = _init_l_Std_Http_Response_conflict();
    leanh::lean_mark_persistent(l_Std_Http_Response_conflict);
    l_Std_Http_Response_serviceUnavailable = _init_l_Std_Http_Response_serviceUnavailable();
    leanh::lean_mark_persistent(l_Std_Http_Response_serviceUnavailable);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Response(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Response(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Std_Http_Data_Status(builtin);
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
    res = runtime_initialize_Std_Http_Data_Response(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Response(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Response(builtin);
}