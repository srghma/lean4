// Lean compiler output
// Module: Std.Http.Protocol.H1.Reader
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message Std.Http.Protocol.H1.Error
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_byte_array_copy_slice, lean_byte_array_size, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_nat_to_int,
    lean_string_length,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{l_ByteArray_extract, l_ByteArray_mkIterator};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{l_String_decEq___boxed, l_String_hash___boxed};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg;
use crate::r#gen::Std::Http::Data::Chunk::{
    l_Std_Http_Chunk_instBEqExtensionName_beq, l_Std_Http_Chunk_instBEqExtensionValue_beq,
    l_Std_Http_Chunk_instReprExtensionName_repr___redArg,
    l_Std_Http_Chunk_instReprExtensionValue_repr___redArg,
};
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Http::Protocol::H1::Config::{
    initialize_Std_Http_Protocol_H1_Config, runtime_initialize_Std_Http_Protocol_H1_Config,
};
use crate::r#gen::Std::Http::Protocol::H1::Error::{
    initialize_Std_Http_Protocol_H1_Error, l_Std_Http_Protocol_H1_instBEqError_beq,
    l_Std_Http_Protocol_H1_instReprError_repr, runtime_initialize_Std_Http_Protocol_H1_Error,
};
use crate::r#gen::Std::Http::Protocol::H1::Message::{
    initialize_Std_Http_Protocol_H1_Message, l_Std_Http_Protocol_H1_Message_Head_headers,
    l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive,
    l_Std_Http_Protocol_H1_instEmptyCollectionHead,
    runtime_initialize_Std_Http_Protocol_H1_Message,
};
use crate::r#gen::Std::Http::Protocol::H1::Parser::{
    initialize_Std_Http_Protocol_H1_Parser, runtime_initialize_Std_Http_Protocol_H1_Parser,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub static l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value:
    leanh::LeanStringObject<50> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 66, 111, 100, 121, 83, 116, 97, 116, 101, 46, 99, 104,
        117, 110, 107, 101, 100, 83, 105, 122, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value:
    leanh::LeanStringObject<53> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 66, 111, 100, 121, 83, 116, 97, 116, 101, 46, 99, 108,
        111, 115, 101, 68, 101, 108, 105, 109, 105, 116, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 66, 111, 100, 121, 83, 116, 97, 116, 101, 46, 102, 105,
        120, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value:
    leanh::LeanStringObject<50> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 66, 111, 100, 121, 83, 116, 97, 116, 101, 46, 99, 104,
        117, 110, 107, 101, 100, 66, 111, 100, 121, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instBEqBodyState: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 99, 108, 111, 115, 101, 100,
        0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 99, 111, 109, 112, 108, 101,
        116, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 112, 101, 110, 100, 105,
        110, 103, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 110, 101, 101, 100, 83, 116,
        97, 114, 116, 76, 105, 110, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 110, 101, 101, 100, 72, 101,
        97, 100, 101, 114, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 114, 101, 97, 100, 66, 111,
        100, 121, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 99, 111, 110, 116, 105, 110,
        117, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 82, 101, 97, 100, 101, 114, 46, 83, 116, 97, 116, 101, 46, 102, 97, 105, 108, 101, 100,
        0,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value:
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
    m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_addHeader___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_addHeader___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(
    mut v_x_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1626_) {
        0 => {
            let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1627_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1627_;
        }
        1 => {
            let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1628_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1628_;
        }
        2 => {
            let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1629_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1629_;
        }
        _ => {
            let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1630_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1630_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___boxed(
    mut v_x_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(v_x_1631_);
    leanh::lean_dec(v_x_1631_);
    return v_res_1632_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
    mut v_t_1633_: *mut leanh::LeanObject,
    mut v_k_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1633_) {
        0 => {
            let mut v_remaining_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_remaining_1635_ = leanh::lean_ctor_get(v_t_1633_, 0);
            leanh::lean_inc(v_remaining_1635_);
            leanh::lean_dec_ref_known(v_t_1633_, 1);
            v___x_1636_ = leanh::lean_apply_1(v_k_1634_, v_remaining_1635_);
            return v___x_1636_;
        }
        2 => {
            let mut v_ext_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_remaining_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ext_1637_ = leanh::lean_ctor_get(v_t_1633_, 0);
            leanh::lean_inc_ref(v_ext_1637_);
            v_remaining_1638_ = leanh::lean_ctor_get(v_t_1633_, 1);
            leanh::lean_inc(v_remaining_1638_);
            leanh::lean_dec_ref_known(v_t_1633_, 2);
            v___x_1639_ = leanh::lean_apply_2(v_k_1634_, v_ext_1637_, v_remaining_1638_);
            return v___x_1639_;
        }
        _ => {
            leanh::lean_dec(v_t_1633_);
            return v_k_1634_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(
    mut v_motive_1640_: *mut leanh::LeanObject,
    mut v_ctorIdx_1641_: *mut leanh::LeanObject,
    mut v_t_1642_: *mut leanh::LeanObject,
    mut v_h_1643_: *mut leanh::LeanObject,
    mut v_k_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1642_, v_k_1644_);
    return v___x_1645_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(
    mut v_motive_1646_: *mut leanh::LeanObject,
    mut v_ctorIdx_1647_: *mut leanh::LeanObject,
    mut v_t_1648_: *mut leanh::LeanObject,
    mut v_h_1649_: *mut leanh::LeanObject,
    mut v_k_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(
        v_motive_1646_,
        v_ctorIdx_1647_,
        v_t_1648_,
        v_h_1649_,
        v_k_1650_,
    );
    leanh::lean_dec(v_ctorIdx_1647_);
    return v_res_1651_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(
    mut v_t_1652_: *mut leanh::LeanObject,
    mut v_fixed_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1652_, v_fixed_1653_);
    return v___x_1654_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(
    mut v_motive_1655_: *mut leanh::LeanObject,
    mut v_t_1656_: *mut leanh::LeanObject,
    mut v_h_1657_: *mut leanh::LeanObject,
    mut v_fixed_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1656_, v_fixed_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(
    mut v_t_1660_: *mut leanh::LeanObject,
    mut v_chunkedSize_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1660_, v_chunkedSize_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(
    mut v_motive_1663_: *mut leanh::LeanObject,
    mut v_t_1664_: *mut leanh::LeanObject,
    mut v_h_1665_: *mut leanh::LeanObject,
    mut v_chunkedSize_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1664_, v_chunkedSize_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(
    mut v_t_1668_: *mut leanh::LeanObject,
    mut v_chunkedBody_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1668_, v_chunkedBody_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(
    mut v_motive_1671_: *mut leanh::LeanObject,
    mut v_t_1672_: *mut leanh::LeanObject,
    mut v_h_1673_: *mut leanh::LeanObject,
    mut v_chunkedBody_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1672_, v_chunkedBody_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(
    mut v_t_1676_: *mut leanh::LeanObject,
    mut v_closeDelimited_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
        v_t_1676_,
        v_closeDelimited_1677_,
    );
    return v___x_1678_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(
    mut v_motive_1679_: *mut leanh::LeanObject,
    mut v_t_1680_: *mut leanh::LeanObject,
    mut v_h_1681_: *mut leanh::LeanObject,
    mut v_closeDelimited_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
        v_t_1680_,
        v_closeDelimited_1682_,
    );
    return v___x_1683_;
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(
    mut v_x_1694_: *mut leanh::LeanObject,
    mut v_x_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1694_) == 0 {
        let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1696_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1;
        return v___x_1696_;
    } else {
        let mut v_val_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1697_ = leanh::lean_ctor_get(v_x_1694_, 0);
        leanh::lean_inc(v_val_1697_);
        leanh::lean_dec_ref_known(v_x_1694_, 1);
        v___x_1698_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3;
        v___x_1699_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_val_1697_);
        v___x_1700_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1700_, 0, v___x_1698_);
        leanh::lean_ctor_set(v___x_1700_, 1, v___x_1699_);
        v___x_1701_ = l_Repr_addAppParen(v___x_1700_, v_x_1695_);
        return v___x_1701_;
    }
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(
    mut v_x_1702_: *mut leanh::LeanObject,
    mut v_x_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_x_1702_, v_x_1703_);
    leanh::lean_dec(v_x_1703_);
    return v_res_1704_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v_x_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1707_) == 0 {
                    leanh::lean_dec(v_x_1705_);
                    return v_x_1706_;
                } else {
                    v_head_1708_ = leanh::lean_ctor_get(v_x_1707_, 0);
                    v_tail_1709_ = leanh::lean_ctor_get(v_x_1707_, 1);
                    v_isSharedCheck_1718_ = (!leanh::lean_is_exclusive(v_x_1707_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1711_ = v_x_1707_;
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1709_);
                        leanh::lean_inc(v_head_1708_);
                        leanh::lean_dec(v_x_1707_);
                        v___x_1711_ = leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1705_);
                if v_isShared_1712_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1711_, 5);
                    leanh::lean_ctor_set(v___x_1711_, 1, v_x_1705_);
                    leanh::lean_ctor_set(v___x_1711_, 0, v_x_1706_);
                    v___x_1714_ = v___x_1711_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_x_1706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_x_1705_);
                    v___x_1714_ = v_reuseFailAlloc_1717_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1715_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                leanh::lean_ctor_set(v___x_1715_, 1, v_head_1708_);
                v_x_1706_ = v___x_1715_;
                v_x_1707_ = v_tail_1709_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(
    mut v_x_1719_: *mut leanh::LeanObject,
    mut v_x_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1719_) == 0 {
        let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1720_);
        v___x_1721_ = leanh::lean_box(0);
        return v___x_1721_;
    } else {
        let mut v_tail_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1722_ = leanh::lean_ctor_get(v_x_1719_, 1);
        if leanh::lean_obj_tag(v_tail_1722_) == 0 {
            let mut v_head_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1720_);
            v_head_1723_ = leanh::lean_ctor_get(v_x_1719_, 0);
            leanh::lean_inc(v_head_1723_);
            leanh::lean_dec_ref_known(v_x_1719_, 2);
            return v_head_1723_;
        } else {
            let mut v_head_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1722_);
            v_head_1724_ = leanh::lean_ctor_get(v_x_1719_, 0);
            leanh::lean_inc(v_head_1724_);
            leanh::lean_dec_ref_known(v_x_1719_, 2);
            v___x_1725_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(v_x_1720_, v_head_1724_, v_tail_1722_);
            return v___x_1725_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0;
    v___x_1735_ = lean_string_length(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5);
    v___x_1737_ = lean_nat_to_int(v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(
    mut v_x_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1743_ = leanh::lean_ctor_get(v_x_1742_, 0);
                v_snd_1744_ = leanh::lean_ctor_get(v_x_1742_, 1);
                v_isSharedCheck_1767_ = (!leanh::lean_is_exclusive(v_x_1742_)) as u8;
                if v_isSharedCheck_1767_ == 0 {
                    v___x_1746_ = v_x_1742_;
                    v_isShared_1747_ = v_isSharedCheck_1767_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1744_);
                    leanh::lean_inc(v_fst_1743_);
                    leanh::lean_dec(v_x_1742_);
                    v___x_1746_ = leanh::lean_box(0);
                    v_isShared_1747_ = v_isSharedCheck_1767_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1748_ = leanh::lean_unsigned_to_nat(0);
                v___x_1749_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_fst_1743_);
                v___x_1750_ = leanh::lean_box(0);
                if v_isShared_1747_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1746_, 1);
                    leanh::lean_ctor_set(v___x_1746_, 1, v___x_1750_);
                    leanh::lean_ctor_set(v___x_1746_, 0, v___x_1749_);
                    v___x_1752_ = v___x_1746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1753_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_snd_1744_, v___x_1748_);
                v___x_1754_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                leanh::lean_ctor_set(v___x_1754_, 1, v___x_1752_);
                v___x_1755_ = l_List_reverse___redArg(v___x_1754_);
                v___x_1756_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3;
                v___x_1757_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(v___x_1755_, v___x_1756_);
                v___x_1758_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6);
                v___x_1759_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7;
                v___x_1760_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1760_, 0, v___x_1759_);
                leanh::lean_ctor_set(v___x_1760_, 1, v___x_1757_);
                v___x_1761_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8;
                v___x_1762_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1762_, 0, v___x_1760_);
                leanh::lean_ctor_set(v___x_1762_, 1, v___x_1761_);
                v___x_1763_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1763_, 0, v___x_1758_);
                leanh::lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                v___x_1764_ = 0;
                v___x_1765_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                leanh::lean_ctor_set_uint8(
                    v___x_1765_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1764_,
                );
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(
    mut v_x_1768_: *mut leanh::LeanObject,
    mut v_x_1769_: *mut leanh::LeanObject,
    mut v_x_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1770_) == 0 {
                    leanh::lean_dec(v_x_1768_);
                    return v_x_1769_;
                } else {
                    v_head_1771_ = leanh::lean_ctor_get(v_x_1770_, 0);
                    v_tail_1772_ = leanh::lean_ctor_get(v_x_1770_, 1);
                    v_isSharedCheck_1782_ = (!leanh::lean_is_exclusive(v_x_1770_)) as u8;
                    if v_isSharedCheck_1782_ == 0 {
                        v___x_1774_ = v_x_1770_;
                        v_isShared_1775_ = v_isSharedCheck_1782_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1772_);
                        leanh::lean_inc(v_head_1771_);
                        leanh::lean_dec(v_x_1770_);
                        v___x_1774_ = leanh::lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1782_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1768_);
                if v_isShared_1775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1774_, 5);
                    leanh::lean_ctor_set(v___x_1774_, 1, v_x_1768_);
                    leanh::lean_ctor_set(v___x_1774_, 0, v_x_1769_);
                    v___x_1777_ = v___x_1774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_x_1769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_x_1768_);
                    v___x_1777_ = v_reuseFailAlloc_1781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1778_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1771_);
                v___x_1779_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1779_, 0, v___x_1777_);
                leanh::lean_ctor_set(v___x_1779_, 1, v___x_1778_);
                v_x_1769_ = v___x_1779_;
                v_x_1770_ = v_tail_1772_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(
    mut v_x_1783_: *mut leanh::LeanObject,
    mut v_x_1784_: *mut leanh::LeanObject,
    mut v_x_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1785_) == 0 {
                    leanh::lean_dec(v_x_1783_);
                    return v_x_1784_;
                } else {
                    v_head_1786_ = leanh::lean_ctor_get(v_x_1785_, 0);
                    v_tail_1787_ = leanh::lean_ctor_get(v_x_1785_, 1);
                    v_isSharedCheck_1797_ = (!leanh::lean_is_exclusive(v_x_1785_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1789_ = v_x_1785_;
                        v_isShared_1790_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1787_);
                        leanh::lean_inc(v_head_1786_);
                        leanh::lean_dec(v_x_1785_);
                        v___x_1789_ = leanh::lean_box(0);
                        v_isShared_1790_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1783_);
                if v_isShared_1790_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1789_, 5);
                    leanh::lean_ctor_set(v___x_1789_, 1, v_x_1783_);
                    leanh::lean_ctor_set(v___x_1789_, 0, v_x_1784_);
                    v___x_1792_ = v___x_1789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_x_1784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_x_1783_);
                    v___x_1792_ = v_reuseFailAlloc_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1793_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1786_);
                v___x_1794_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1794_, 0, v___x_1792_);
                leanh::lean_ctor_set(v___x_1794_, 1, v___x_1793_);
                v___x_1795_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(v_x_1783_, v___x_1794_, v_tail_1787_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(
    mut v_x_1798_: *mut leanh::LeanObject,
    mut v_x_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1798_) == 0 {
        let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1799_);
        v___x_1800_ = leanh::lean_box(0);
        return v___x_1800_;
    } else {
        let mut v_tail_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1801_ = leanh::lean_ctor_get(v_x_1798_, 1);
        if leanh::lean_obj_tag(v_tail_1801_) == 0 {
            let mut v_head_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1799_);
            v_head_1802_ = leanh::lean_ctor_get(v_x_1798_, 0);
            leanh::lean_inc(v_head_1802_);
            leanh::lean_dec_ref_known(v_x_1798_, 2);
            v___x_1803_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1802_);
            return v___x_1803_;
        } else {
            let mut v_head_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1801_);
            v_head_1804_ = leanh::lean_ctor_get(v_x_1798_, 0);
            leanh::lean_inc(v_head_1804_);
            leanh::lean_dec_ref_known(v_x_1798_, 2);
            v___x_1805_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1804_);
            v___x_1806_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(v_x_1799_, v___x_1805_, v_tail_1801_);
            return v___x_1806_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0;
    v___x_1810_ = lean_string_length(v___x_1809_);
    return v___x_1810_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2);
    v___x_1812_ = lean_nat_to_int(v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(
    mut v_xs_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    v___x_1821_ = lean_array_get_size(v_xs_1820_);
    v___x_1822_ = leanh::lean_unsigned_to_nat(0);
    v___x_1823_ = lean_nat_dec_eq(v___x_1821_, v___x_1822_);
    if v___x_1823_ == 0 {
        let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1824_ = lean_array_to_list(v_xs_1820_);
        v___x_1825_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3;
        v___x_1826_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(v___x_1824_, v___x_1825_);
        v___x_1827_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once), _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3);
        v___x_1828_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4;
        v___x_1829_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1829_, 0, v___x_1828_);
        leanh::lean_ctor_set(v___x_1829_, 1, v___x_1826_);
        v___x_1830_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5;
        v___x_1831_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1831_, 0, v___x_1829_);
        leanh::lean_ctor_set(v___x_1831_, 1, v___x_1830_);
        v___x_1832_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1832_, 0, v___x_1827_);
        leanh::lean_ctor_set(v___x_1832_, 1, v___x_1831_);
        v___x_1833_ = l_Std_Format_fill(v___x_1832_);
        return v___x_1833_;
    } else {
        let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1820_);
        v___x_1834_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7;
        return v___x_1834_;
    }
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = leanh::lean_unsigned_to_nat(2);
    v___x_1848_ = lean_nat_to_int(v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = leanh::lean_unsigned_to_nat(1);
    v___x_1850_ = lean_nat_to_int(v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(
    mut v_x_1857_: *mut leanh::LeanObject,
    mut v_prec_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___y_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___y_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1857_) {
                0 => {
                    v_remaining_1873_ = leanh::lean_ctor_get(v_x_1857_, 0);
                    v_isSharedCheck_1893_ = (!leanh::lean_is_exclusive(v_x_1857_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1875_ = v_x_1857_;
                        v_isShared_1876_ = v_isSharedCheck_1893_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_remaining_1873_);
                        leanh::lean_dec(v_x_1857_);
                        v___x_1875_ = leanh::lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1893_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v___x_1894_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1895_ = lean_nat_dec_le(v___x_1894_, v_prec_1858_);
                    if v___x_1895_ == 0 {
                        v___x_1896_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_1860_ = v___x_1896_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1897_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_1860_ = v___x_1897_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ext_1898_ = leanh::lean_ctor_get(v_x_1857_, 0);
                    v_remaining_1899_ = leanh::lean_ctor_get(v_x_1857_, 1);
                    v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v_x_1857_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1901_ = v_x_1857_;
                        v_isShared_1902_ = v_isSharedCheck_1923_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_remaining_1899_);
                        leanh::lean_inc(v_ext_1898_);
                        leanh::lean_dec(v_x_1857_);
                        v___x_1901_ = leanh::lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1923_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v___x_1924_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1925_ = lean_nat_dec_le(v___x_1924_, v_prec_1858_);
                    if v___x_1925_ == 0 {
                        v___x_1926_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_1867_ = v___x_1926_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_1867_ = v___x_1927_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1861_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1;
                leanh::lean_inc(v___y_1860_);
                v___x_1862_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1862_, 0, v___y_1860_);
                leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
                v___x_1863_ = 0;
                v___x_1864_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1864_, 0, v___x_1862_);
                leanh::lean_ctor_set_uint8(
                    v___x_1864_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1863_,
                );
                v___x_1865_ = l_Repr_addAppParen(v___x_1864_, v_prec_1858_);
                return v___x_1865_;
            }
            2 => {
                v___x_1868_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3;
                leanh::lean_inc(v___y_1867_);
                v___x_1869_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1869_, 0, v___y_1867_);
                leanh::lean_ctor_set(v___x_1869_, 1, v___x_1868_);
                v___x_1870_ = 0;
                v___x_1871_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1871_, 0, v___x_1869_);
                leanh::lean_ctor_set_uint8(
                    v___x_1871_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1870_,
                );
                v___x_1872_ = l_Repr_addAppParen(v___x_1871_, v_prec_1858_);
                return v___x_1872_;
            }
            3 => {
                v___x_1889_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1890_ = lean_nat_dec_le(v___x_1889_, v_prec_1858_);
                if v___x_1890_ == 0 {
                    v___x_1891_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7,
                    );
                    v___y_1878_ = v___x_1891_;
                    state = 4;
                    continue;
                } else {
                    v___x_1892_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8,
                    );
                    v___y_1878_ = v___x_1892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1879_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6;
                v___x_1880_ = l_Nat_reprFast(v_remaining_1873_);
                if v_isShared_1876_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1875_, 3);
                    leanh::lean_ctor_set(v___x_1875_, 0, v___x_1880_);
                    v___x_1882_ = v___x_1875_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1888_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1880_);
                    v___x_1882_ = v_reuseFailAlloc_1888_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1883_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1883_, 0, v___x_1879_);
                leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                leanh::lean_inc(v___y_1878_);
                v___x_1884_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1884_, 0, v___y_1878_);
                leanh::lean_ctor_set(v___x_1884_, 1, v___x_1883_);
                v___x_1885_ = 0;
                v___x_1886_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1886_, 0, v___x_1884_);
                leanh::lean_ctor_set_uint8(
                    v___x_1886_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1885_,
                );
                v___x_1887_ = l_Repr_addAppParen(v___x_1886_, v_prec_1858_);
                return v___x_1887_;
            }
            6 => {
                v___x_1919_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1920_ = lean_nat_dec_le(v___x_1919_, v_prec_1858_);
                if v___x_1920_ == 0 {
                    v___x_1921_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7,
                    );
                    v___y_1904_ = v___x_1921_;
                    state = 7;
                    continue;
                } else {
                    v___x_1922_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8,
                    );
                    v___y_1904_ = v___x_1922_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1905_ = leanh::lean_box(1);
                v___x_1906_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11;
                v___x_1907_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_1898_);
                if v_isShared_1902_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1901_, 5);
                    leanh::lean_ctor_set(v___x_1901_, 1, v___x_1907_);
                    leanh::lean_ctor_set(v___x_1901_, 0, v___x_1906_);
                    v___x_1909_ = v___x_1901_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1907_);
                    v___x_1909_ = v_reuseFailAlloc_1918_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1910_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
                leanh::lean_ctor_set(v___x_1910_, 1, v___x_1905_);
                v___x_1911_ = l_Nat_reprFast(v_remaining_1899_);
                v___x_1912_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1912_, 0, v___x_1911_);
                v___x_1913_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1913_, 0, v___x_1910_);
                leanh::lean_ctor_set(v___x_1913_, 1, v___x_1912_);
                leanh::lean_inc(v___y_1904_);
                v___x_1914_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1914_, 0, v___y_1904_);
                leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                v___x_1915_ = 0;
                v___x_1916_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1916_, 0, v___x_1914_);
                leanh::lean_ctor_set_uint8(
                    v___x_1916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1915_,
                );
                v___x_1917_ = l_Repr_addAppParen(v___x_1916_, v_prec_1858_);
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(
    mut v_x_1928_: *mut leanh::LeanObject,
    mut v_prec_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_x_1928_, v_prec_1929_);
    leanh::lean_dec(v_prec_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(
    mut v_a_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_nat_to_int(v_a_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(
    mut v_x_1933_: *mut leanh::LeanObject,
    mut v_x_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_x_1933_);
    return v___x_1935_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(
    mut v_x_1936_: *mut leanh::LeanObject,
    mut v_x_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(v_x_1936_, v_x_1937_);
    leanh::lean_dec(v_x_1937_);
    return v_res_1938_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(
    mut v_x_1941_: *mut leanh::LeanObject,
    mut v_x_1942_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1941_) == 0 {
        if leanh::lean_obj_tag(v_x_1942_) == 0 {
            let mut v___x_1943_: u8 = 0;
            v___x_1943_ = 1;
            return v___x_1943_;
        } else {
            let mut v___x_1944_: u8 = 0;
            v___x_1944_ = 0;
            return v___x_1944_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1942_) == 0 {
            let mut v___x_1945_: u8 = 0;
            v___x_1945_ = 0;
            return v___x_1945_;
        } else {
            let mut v_val_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1948_: u8 = 0;
            v_val_1946_ = leanh::lean_ctor_get(v_x_1941_, 0);
            v_val_1947_ = leanh::lean_ctor_get(v_x_1942_, 0);
            v___x_1948_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_val_1946_, v_val_1947_);
            return v___x_1948_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(
    mut v_x_1949_: *mut leanh::LeanObject,
    mut v_x_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1951_: u8 = 0;
    let mut v_r_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ =
        l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(
            v_x_1949_, v_x_1950_,
        );
    leanh::lean_dec(v_x_1950_);
    leanh::lean_dec(v_x_1949_);
    v_r_1952_ = leanh::lean_box((v_res_1951_) as usize);
    return v_r_1952_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
    mut v_xs_1953_: *mut leanh::LeanObject,
    mut v_ys_1954_: *mut leanh::LeanObject,
    mut v_x_1955_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1957_: u8 = 0;
    let mut v_one_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1956_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1957_ = lean_nat_dec_eq(v_x_1955_, v_zero_1956_);
                if v_isZero_1957_ == 1 {
                    leanh::lean_dec(v_x_1955_);
                    return v_isZero_1957_;
                } else {
                    v_one_1958_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1959_ = lean_nat_sub(v_x_1955_, v_one_1958_);
                    leanh::lean_dec(v_x_1955_);
                    v___x_1963_ = lean_array_fget_borrowed(v_xs_1953_, v_n_1959_);
                    v_fst_1964_ = leanh::lean_ctor_get(v___x_1963_, 0);
                    v_snd_1965_ = leanh::lean_ctor_get(v___x_1963_, 1);
                    v___x_1966_ = lean_array_fget_borrowed(v_ys_1954_, v_n_1959_);
                    v_fst_1967_ = leanh::lean_ctor_get(v___x_1966_, 0);
                    v_snd_1968_ = leanh::lean_ctor_get(v___x_1966_, 1);
                    v___x_1969_ =
                        l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_1964_, v_fst_1967_);
                    if v___x_1969_ == 0 {
                        v___y_1961_ = v___x_1969_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1970_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_1965_, v_snd_1968_);
                        v___y_1961_ = v___x_1970_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1961_ == 0 {
                    leanh::lean_dec(v_n_1959_);
                    return v___y_1961_;
                } else {
                    v_x_1955_ = v_n_1959_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(
    mut v_xs_1971_: *mut leanh::LeanObject,
    mut v_ys_1972_: *mut leanh::LeanObject,
    mut v_x_1973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1974_: u8 = 0;
    let mut v_r_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1974_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
            v_xs_1971_, v_ys_1972_, v_x_1973_,
        );
    leanh::lean_dec_ref(v_ys_1972_);
    leanh::lean_dec_ref(v_xs_1971_);
    v_r_1975_ = leanh::lean_box((v_res_1974_) as usize);
    return v_r_1975_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(
    mut v_x_1976_: *mut leanh::LeanObject,
    mut v_x_1977_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1976_) {
        0 => {
            if leanh::lean_obj_tag(v_x_1977_) == 0 {
                let mut v_remaining_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1980_: u8 = 0;
                v_remaining_1978_ = leanh::lean_ctor_get(v_x_1976_, 0);
                v_remaining_1979_ = leanh::lean_ctor_get(v_x_1977_, 0);
                v___x_1980_ = lean_nat_dec_eq(v_remaining_1978_, v_remaining_1979_);
                return v___x_1980_;
            } else {
                let mut v___x_1981_: u8 = 0;
                v___x_1981_ = 0;
                return v___x_1981_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_1977_) == 1 {
                let mut v___x_1982_: u8 = 0;
                v___x_1982_ = 1;
                return v___x_1982_;
            } else {
                let mut v___x_1983_: u8 = 0;
                v___x_1983_ = 0;
                return v___x_1983_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_1977_) == 2 {
                let mut v_ext_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ext_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1990_: u8 = 0;
                v_ext_1984_ = leanh::lean_ctor_get(v_x_1976_, 0);
                v_remaining_1985_ = leanh::lean_ctor_get(v_x_1976_, 1);
                v_ext_1986_ = leanh::lean_ctor_get(v_x_1977_, 0);
                v_remaining_1987_ = leanh::lean_ctor_get(v_x_1977_, 1);
                v___x_1988_ = lean_array_get_size(v_ext_1984_);
                v___x_1989_ = lean_array_get_size(v_ext_1986_);
                v___x_1990_ = lean_nat_dec_eq(v___x_1988_, v___x_1989_);
                if v___x_1990_ == 0 {
                    return v___x_1990_;
                } else {
                    let mut v___x_1991_: u8 = 0;
                    v___x_1991_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_ext_1984_, v_ext_1986_, v___x_1988_);
                    if v___x_1991_ == 0 {
                        return v___x_1991_;
                    } else {
                        let mut v___x_1992_: u8 = 0;
                        v___x_1992_ = lean_nat_dec_eq(v_remaining_1985_, v_remaining_1987_);
                        return v___x_1992_;
                    }
                }
            } else {
                let mut v___x_1993_: u8 = 0;
                v___x_1993_ = 0;
                return v___x_1993_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_1977_) == 3 {
                let mut v___x_1994_: u8 = 0;
                v___x_1994_ = 1;
                return v___x_1994_;
            } else {
                let mut v___x_1995_: u8 = 0;
                v___x_1995_ = 0;
                return v___x_1995_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(
    mut v_x_1996_: *mut leanh::LeanObject,
    mut v_x_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1998_: u8 = 0;
    let mut v_r_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_1996_, v_x_1997_);
    leanh::lean_dec(v_x_1997_);
    leanh::lean_dec(v_x_1996_);
    v_r_1999_ = leanh::lean_box((v_res_1998_) as usize);
    return v_r_1999_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(
    mut v_xs_2000_: *mut leanh::LeanObject,
    mut v_ys_2001_: *mut leanh::LeanObject,
    mut v_hsz_2002_: *mut leanh::LeanObject,
    mut v_x_2003_: *mut leanh::LeanObject,
    mut v_x_2004_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2005_: u8 = 0;
    v___x_2005_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
            v_xs_2000_, v_ys_2001_, v_x_2003_,
        );
    return v___x_2005_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(
    mut v_xs_2006_: *mut leanh::LeanObject,
    mut v_ys_2007_: *mut leanh::LeanObject,
    mut v_hsz_2008_: *mut leanh::LeanObject,
    mut v_x_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2011_: u8 = 0;
    let mut v_r_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(
            v_xs_2006_,
            v_ys_2007_,
            v_hsz_2008_,
            v_x_2009_,
            v_x_2010_,
        );
    leanh::lean_dec_ref(v_ys_2007_);
    leanh::lean_dec_ref(v_xs_2006_);
    v_r_2012_ = leanh::lean_box((v_res_2011_) as usize);
    return v_r_2012_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(
    mut v_x_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2015_) {
        0 => {
            let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2016_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2016_;
        }
        1 => {
            let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2017_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2017_;
        }
        2 => {
            let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2018_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2018_;
        }
        3 => {
            let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2019_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2019_;
        }
        4 => {
            let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2020_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2020_;
        }
        5 => {
            let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2021_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2021_;
        }
        6 => {
            let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2022_ = leanh::lean_unsigned_to_nat(6);
            return v___x_2022_;
        }
        _ => {
            let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2023_ = leanh::lean_unsigned_to_nat(7);
            return v___x_2023_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg___boxed(
    mut v_x_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_2024_);
    leanh::lean_dec(v_x_2024_);
    return v_res_2025_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx(
    mut v_dir_2026_: u8,
    mut v_x_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_2027_);
    return v___x_2028_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___boxed(
    mut v_dir_2029_: *mut leanh::LeanObject,
    mut v_x_2030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2031_: u8 = 0;
    let mut v_res_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2031_ = (leanh::lean_unbox(v_dir_2029_) as u8);
    v_res_2032_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx(v_dir_boxed_2031_, v_x_2030_);
    leanh::lean_dec(v_x_2030_);
    return v_res_2032_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(
    mut v_t_2033_: *mut leanh::LeanObject,
    mut v_k_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2033_) {
        1 => {
            let mut v_a_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2035_ = leanh::lean_ctor_get(v_t_2033_, 0);
            leanh::lean_inc(v_a_2035_);
            leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2036_ = leanh::lean_apply_1(v_k_2034_, v_a_2035_);
            return v___x_2036_;
        }
        2 => {
            let mut v_a_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2037_ = leanh::lean_ctor_get(v_t_2033_, 0);
            leanh::lean_inc(v_a_2037_);
            leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2038_ = leanh::lean_apply_1(v_k_2034_, v_a_2037_);
            return v___x_2038_;
        }
        3 => {
            let mut v_a_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2039_ = leanh::lean_ctor_get(v_t_2033_, 0);
            leanh::lean_inc(v_a_2039_);
            leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2040_ = leanh::lean_apply_1(v_k_2034_, v_a_2039_);
            return v___x_2040_;
        }
        7 => {
            let mut v_error_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_error_2041_ = leanh::lean_ctor_get(v_t_2033_, 0);
            leanh::lean_inc(v_error_2041_);
            leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2042_ = leanh::lean_apply_1(v_k_2034_, v_error_2041_);
            return v___x_2042_;
        }
        _ => {
            leanh::lean_dec(v_t_2033_);
            return v_k_2034_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim(
    mut v_dir_2043_: u8,
    mut v_motive_2044_: *mut leanh::LeanObject,
    mut v_ctorIdx_2045_: *mut leanh::LeanObject,
    mut v_t_2046_: *mut leanh::LeanObject,
    mut v_h_2047_: *mut leanh::LeanObject,
    mut v_k_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2046_, v_k_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(
    mut v_dir_2050_: *mut leanh::LeanObject,
    mut v_motive_2051_: *mut leanh::LeanObject,
    mut v_ctorIdx_2052_: *mut leanh::LeanObject,
    mut v_t_2053_: *mut leanh::LeanObject,
    mut v_h_2054_: *mut leanh::LeanObject,
    mut v_k_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2056_: u8 = 0;
    let mut v_res_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2056_ = (leanh::lean_unbox(v_dir_2050_) as u8);
    v_res_2057_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(
        v_dir_boxed_2056_,
        v_motive_2051_,
        v_ctorIdx_2052_,
        v_t_2053_,
        v_h_2054_,
        v_k_2055_,
    );
    leanh::lean_dec(v_ctorIdx_2052_);
    return v_res_2057_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(
    mut v_t_2058_: *mut leanh::LeanObject,
    mut v_needStartLine_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2058_, v_needStartLine_2059_);
    return v___x_2060_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(
    mut v_dir_2061_: u8,
    mut v_motive_2062_: *mut leanh::LeanObject,
    mut v_t_2063_: *mut leanh::LeanObject,
    mut v_h_2064_: *mut leanh::LeanObject,
    mut v_needStartLine_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2063_, v_needStartLine_2065_);
    return v___x_2066_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(
    mut v_dir_2067_: *mut leanh::LeanObject,
    mut v_motive_2068_: *mut leanh::LeanObject,
    mut v_t_2069_: *mut leanh::LeanObject,
    mut v_h_2070_: *mut leanh::LeanObject,
    mut v_needStartLine_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2072_: u8 = 0;
    let mut v_res_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2072_ = (leanh::lean_unbox(v_dir_2067_) as u8);
    v_res_2073_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(
        v_dir_boxed_2072_,
        v_motive_2068_,
        v_t_2069_,
        v_h_2070_,
        v_needStartLine_2071_,
    );
    return v_res_2073_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(
    mut v_t_2074_: *mut leanh::LeanObject,
    mut v_needHeader_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2074_, v_needHeader_2075_);
    return v___x_2076_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(
    mut v_dir_2077_: u8,
    mut v_motive_2078_: *mut leanh::LeanObject,
    mut v_t_2079_: *mut leanh::LeanObject,
    mut v_h_2080_: *mut leanh::LeanObject,
    mut v_needHeader_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2079_, v_needHeader_2081_);
    return v___x_2082_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(
    mut v_dir_2083_: *mut leanh::LeanObject,
    mut v_motive_2084_: *mut leanh::LeanObject,
    mut v_t_2085_: *mut leanh::LeanObject,
    mut v_h_2086_: *mut leanh::LeanObject,
    mut v_needHeader_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2088_: u8 = 0;
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2088_ = (leanh::lean_unbox(v_dir_2083_) as u8);
    v_res_2089_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(
        v_dir_boxed_2088_,
        v_motive_2084_,
        v_t_2085_,
        v_h_2086_,
        v_needHeader_2087_,
    );
    return v_res_2089_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(
    mut v_t_2090_: *mut leanh::LeanObject,
    mut v_readBody_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2090_, v_readBody_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_readBody_elim(
    mut v_dir_2093_: u8,
    mut v_motive_2094_: *mut leanh::LeanObject,
    mut v_t_2095_: *mut leanh::LeanObject,
    mut v_h_2096_: *mut leanh::LeanObject,
    mut v_readBody_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2095_, v_readBody_2097_);
    return v___x_2098_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(
    mut v_dir_2099_: *mut leanh::LeanObject,
    mut v_motive_2100_: *mut leanh::LeanObject,
    mut v_t_2101_: *mut leanh::LeanObject,
    mut v_h_2102_: *mut leanh::LeanObject,
    mut v_readBody_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2104_: u8 = 0;
    let mut v_res_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2104_ = (leanh::lean_unbox(v_dir_2099_) as u8);
    v_res_2105_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(
        v_dir_boxed_2104_,
        v_motive_2100_,
        v_t_2101_,
        v_h_2102_,
        v_readBody_2103_,
    );
    return v_res_2105_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(
    mut v_t_2106_: *mut leanh::LeanObject,
    mut v_continue_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2106_, v_continue_2107_);
    return v___x_2108_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_continue_elim(
    mut v_dir_2109_: u8,
    mut v_motive_2110_: *mut leanh::LeanObject,
    mut v_t_2111_: *mut leanh::LeanObject,
    mut v_h_2112_: *mut leanh::LeanObject,
    mut v_continue_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2111_, v_continue_2113_);
    return v___x_2114_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(
    mut v_dir_2115_: *mut leanh::LeanObject,
    mut v_motive_2116_: *mut leanh::LeanObject,
    mut v_t_2117_: *mut leanh::LeanObject,
    mut v_h_2118_: *mut leanh::LeanObject,
    mut v_continue_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2120_: u8 = 0;
    let mut v_res_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2120_ = (leanh::lean_unbox(v_dir_2115_) as u8);
    v_res_2121_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(
        v_dir_boxed_2120_,
        v_motive_2116_,
        v_t_2117_,
        v_h_2118_,
        v_continue_2119_,
    );
    return v_res_2121_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(
    mut v_t_2122_: *mut leanh::LeanObject,
    mut v_pending_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2122_, v_pending_2123_);
    return v___x_2124_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_pending_elim(
    mut v_dir_2125_: u8,
    mut v_motive_2126_: *mut leanh::LeanObject,
    mut v_t_2127_: *mut leanh::LeanObject,
    mut v_h_2128_: *mut leanh::LeanObject,
    mut v_pending_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2127_, v_pending_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(
    mut v_dir_2131_: *mut leanh::LeanObject,
    mut v_motive_2132_: *mut leanh::LeanObject,
    mut v_t_2133_: *mut leanh::LeanObject,
    mut v_h_2134_: *mut leanh::LeanObject,
    mut v_pending_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2136_: u8 = 0;
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2136_ = (leanh::lean_unbox(v_dir_2131_) as u8);
    v_res_2137_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(
        v_dir_boxed_2136_,
        v_motive_2132_,
        v_t_2133_,
        v_h_2134_,
        v_pending_2135_,
    );
    return v_res_2137_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(
    mut v_t_2138_: *mut leanh::LeanObject,
    mut v_complete_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2138_, v_complete_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_complete_elim(
    mut v_dir_2141_: u8,
    mut v_motive_2142_: *mut leanh::LeanObject,
    mut v_t_2143_: *mut leanh::LeanObject,
    mut v_h_2144_: *mut leanh::LeanObject,
    mut v_complete_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2143_, v_complete_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(
    mut v_dir_2147_: *mut leanh::LeanObject,
    mut v_motive_2148_: *mut leanh::LeanObject,
    mut v_t_2149_: *mut leanh::LeanObject,
    mut v_h_2150_: *mut leanh::LeanObject,
    mut v_complete_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2152_: u8 = 0;
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2152_ = (leanh::lean_unbox(v_dir_2147_) as u8);
    v_res_2153_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(
        v_dir_boxed_2152_,
        v_motive_2148_,
        v_t_2149_,
        v_h_2150_,
        v_complete_2151_,
    );
    return v_res_2153_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(
    mut v_t_2154_: *mut leanh::LeanObject,
    mut v_closed_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2154_, v_closed_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_closed_elim(
    mut v_dir_2157_: u8,
    mut v_motive_2158_: *mut leanh::LeanObject,
    mut v_t_2159_: *mut leanh::LeanObject,
    mut v_h_2160_: *mut leanh::LeanObject,
    mut v_closed_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2159_, v_closed_2161_);
    return v___x_2162_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(
    mut v_dir_2163_: *mut leanh::LeanObject,
    mut v_motive_2164_: *mut leanh::LeanObject,
    mut v_t_2165_: *mut leanh::LeanObject,
    mut v_h_2166_: *mut leanh::LeanObject,
    mut v_closed_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2168_: u8 = 0;
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2168_ = (leanh::lean_unbox(v_dir_2163_) as u8);
    v_res_2169_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(
        v_dir_boxed_2168_,
        v_motive_2164_,
        v_t_2165_,
        v_h_2166_,
        v_closed_2167_,
    );
    return v_res_2169_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(
    mut v_t_2170_: *mut leanh::LeanObject,
    mut v_failed_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2170_, v_failed_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_failed_elim(
    mut v_dir_2173_: u8,
    mut v_motive_2174_: *mut leanh::LeanObject,
    mut v_t_2175_: *mut leanh::LeanObject,
    mut v_h_2176_: *mut leanh::LeanObject,
    mut v_failed_2177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2175_, v_failed_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(
    mut v_dir_2179_: *mut leanh::LeanObject,
    mut v_motive_2180_: *mut leanh::LeanObject,
    mut v_t_2181_: *mut leanh::LeanObject,
    mut v_h_2182_: *mut leanh::LeanObject,
    mut v_failed_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2184_: u8 = 0;
    let mut v_res_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2184_ = (leanh::lean_unbox(v_dir_2179_) as u8);
    v_res_2185_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(
        v_dir_boxed_2184_,
        v_motive_2180_,
        v_t_2181_,
        v_h_2182_,
        v_failed_2183_,
    );
    return v_res_2185_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(
    mut v_dir_2186_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = leanh::lean_box(0);
    return v___x_2187_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(
    mut v_dir_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2189_: u8 = 0;
    let mut v_res_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2189_ = (leanh::lean_unbox(v_dir_2188_) as u8);
    v_res_2190_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_2189_);
    return v_res_2190_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState(
    mut v_a_2191_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = leanh::lean_box(0);
    return v___x_2192_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(
    mut v_a_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6__boxed_2194_: u8 = 0;
    let mut v_res_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_6__boxed_2194_ = (leanh::lean_unbox(v_a_2193_) as u8);
    v_res_2195_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_6__boxed_2194_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(
    mut v_x_2232_: *mut leanh::LeanObject,
    mut v_prec_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___y_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_a_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2232_) {
                0 => {
                    v___x_2262_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2263_ = lean_nat_dec_le(v___x_2262_, v_prec_2233_);
                    if v___x_2263_ == 0 {
                        v___x_2264_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2256_ = v___x_2264_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2265_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2256_ = v___x_2265_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v_a_2266_ = leanh::lean_ctor_get(v_x_2232_, 0);
                    v_isSharedCheck_2286_ = (!leanh::lean_is_exclusive(v_x_2232_)) as u8;
                    if v_isSharedCheck_2286_ == 0 {
                        v___x_2268_ = v_x_2232_;
                        v_isShared_2269_ = v_isSharedCheck_2286_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2266_);
                        leanh::lean_dec(v_x_2232_);
                        v___x_2268_ = leanh::lean_box(0);
                        v_isShared_2269_ = v_isSharedCheck_2286_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_a_2287_ = leanh::lean_ctor_get(v_x_2232_, 0);
                    leanh::lean_inc(v_a_2287_);
                    leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2298_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2299_ = lean_nat_dec_le(v___x_2298_, v_prec_2233_);
                    if v___x_2299_ == 0 {
                        v___x_2300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2289_ = v___x_2300_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2289_ = v___x_2301_;
                        state = 8;
                        continue;
                    }
                }
                3 => {
                    v_a_2302_ = leanh::lean_ctor_get(v_x_2232_, 0);
                    leanh::lean_inc(v_a_2302_);
                    leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2303_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2313_ = lean_nat_dec_le(v___x_2303_, v_prec_2233_);
                    if v___x_2313_ == 0 {
                        v___x_2314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2305_ = v___x_2314_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2315_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2305_ = v___x_2315_;
                        state = 9;
                        continue;
                    }
                }
                4 => {
                    v___x_2316_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2317_ = lean_nat_dec_le(v___x_2316_, v_prec_2233_);
                    if v___x_2317_ == 0 {
                        v___x_2318_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2249_ = v___x_2318_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2249_ = v___x_2319_;
                        state = 3;
                        continue;
                    }
                }
                5 => {
                    v___x_2320_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2321_ = lean_nat_dec_le(v___x_2320_, v_prec_2233_);
                    if v___x_2321_ == 0 {
                        v___x_2322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2242_ = v___x_2322_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2242_ = v___x_2323_;
                        state = 2;
                        continue;
                    }
                }
                6 => {
                    v___x_2324_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2325_ = lean_nat_dec_le(v___x_2324_, v_prec_2233_);
                    if v___x_2325_ == 0 {
                        v___x_2326_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2235_ = v___x_2326_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2235_ = v___x_2327_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_error_2328_ = leanh::lean_ctor_get(v_x_2232_, 0);
                    leanh::lean_inc(v_error_2328_);
                    leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2339_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2340_ = lean_nat_dec_le(v___x_2339_, v_prec_2233_);
                    if v___x_2340_ == 0 {
                        v___x_2341_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2330_ = v___x_2341_;
                        state = 10;
                        continue;
                    } else {
                        v___x_2342_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2330_ = v___x_2342_;
                        state = 10;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2236_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1;
                leanh::lean_inc(v___y_2235_);
                v___x_2237_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2237_, 0, v___y_2235_);
                leanh::lean_ctor_set(v___x_2237_, 1, v___x_2236_);
                v___x_2238_ = 0;
                v___x_2239_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2239_, 0, v___x_2237_);
                leanh::lean_ctor_set_uint8(
                    v___x_2239_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2238_,
                );
                v___x_2240_ = l_Repr_addAppParen(v___x_2239_, v_prec_2233_);
                return v___x_2240_;
            }
            2 => {
                v___x_2243_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3;
                leanh::lean_inc(v___y_2242_);
                v___x_2244_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2244_, 0, v___y_2242_);
                leanh::lean_ctor_set(v___x_2244_, 1, v___x_2243_);
                v___x_2245_ = 0;
                v___x_2246_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2246_, 0, v___x_2244_);
                leanh::lean_ctor_set_uint8(
                    v___x_2246_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2245_,
                );
                v___x_2247_ = l_Repr_addAppParen(v___x_2246_, v_prec_2233_);
                return v___x_2247_;
            }
            3 => {
                v___x_2250_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5;
                leanh::lean_inc(v___y_2249_);
                v___x_2251_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2251_, 0, v___y_2249_);
                leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
                v___x_2252_ = 0;
                v___x_2253_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2253_, 0, v___x_2251_);
                leanh::lean_ctor_set_uint8(
                    v___x_2253_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2252_,
                );
                v___x_2254_ = l_Repr_addAppParen(v___x_2253_, v_prec_2233_);
                return v___x_2254_;
            }
            4 => {
                v___x_2257_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7;
                leanh::lean_inc(v___y_2256_);
                v___x_2258_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2258_, 0, v___y_2256_);
                leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                v___x_2259_ = 0;
                v___x_2260_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2260_, 0, v___x_2258_);
                leanh::lean_ctor_set_uint8(
                    v___x_2260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2259_,
                );
                v___x_2261_ = l_Repr_addAppParen(v___x_2260_, v_prec_2233_);
                return v___x_2261_;
            }
            5 => {
                v___x_2282_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2283_ = lean_nat_dec_le(v___x_2282_, v_prec_2233_);
                if v___x_2283_ == 0 {
                    v___x_2284_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7,
                    );
                    v___y_2271_ = v___x_2284_;
                    state = 6;
                    continue;
                } else {
                    v___x_2285_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8,
                    );
                    v___y_2271_ = v___x_2285_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2272_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10;
                v___x_2273_ = l_Nat_reprFast(v_a_2266_);
                if v_isShared_2269_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2268_, 3);
                    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2268_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2273_);
                    v___x_2275_ = v_reuseFailAlloc_2281_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2276_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2276_, 0, v___x_2272_);
                leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                leanh::lean_inc(v___y_2271_);
                v___x_2277_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2277_, 0, v___y_2271_);
                leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = 0;
                v___x_2279_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                leanh::lean_ctor_set_uint8(
                    v___x_2279_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2278_,
                );
                v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2233_);
                return v___x_2280_;
            }
            8 => {
                v___x_2290_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13;
                v___x_2291_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2292_ =
                    l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_2287_, v___x_2291_);
                v___x_2293_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2293_, 0, v___x_2290_);
                leanh::lean_ctor_set(v___x_2293_, 1, v___x_2292_);
                leanh::lean_inc(v___y_2289_);
                v___x_2294_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2294_, 0, v___y_2289_);
                leanh::lean_ctor_set(v___x_2294_, 1, v___x_2293_);
                v___x_2295_ = 0;
                v___x_2296_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2296_, 0, v___x_2294_);
                leanh::lean_ctor_set_uint8(
                    v___x_2296_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2295_,
                );
                v___x_2297_ = l_Repr_addAppParen(v___x_2296_, v_prec_2233_);
                return v___x_2297_;
            }
            9 => {
                v___x_2306_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16;
                v___x_2307_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(
                    v_a_2302_,
                    v___x_2303_,
                );
                v___x_2308_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2308_, 0, v___x_2306_);
                leanh::lean_ctor_set(v___x_2308_, 1, v___x_2307_);
                leanh::lean_inc(v___y_2305_);
                v___x_2309_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2309_, 0, v___y_2305_);
                leanh::lean_ctor_set(v___x_2309_, 1, v___x_2308_);
                v___x_2310_ = 0;
                v___x_2311_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2311_, 0, v___x_2309_);
                leanh::lean_ctor_set_uint8(
                    v___x_2311_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2310_,
                );
                v___x_2312_ = l_Repr_addAppParen(v___x_2311_, v_prec_2233_);
                return v___x_2312_;
            }
            10 => {
                v___x_2331_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19;
                v___x_2332_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2333_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_2328_, v___x_2332_);
                v___x_2334_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2334_, 0, v___x_2331_);
                leanh::lean_ctor_set(v___x_2334_, 1, v___x_2333_);
                leanh::lean_inc(v___y_2330_);
                v___x_2335_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2335_, 0, v___y_2330_);
                leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                v___x_2336_ = 0;
                v___x_2337_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                leanh::lean_ctor_set_uint8(
                    v___x_2337_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2336_,
                );
                v___x_2338_ = l_Repr_addAppParen(v___x_2337_, v_prec_2233_);
                return v___x_2338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(
    mut v_x_2343_: *mut leanh::LeanObject,
    mut v_prec_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2345_ =
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_2343_, v_prec_2344_);
    leanh::lean_dec(v_prec_2344_);
    return v_res_2345_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr(
    mut v_dir_2346_: u8,
    mut v_x_2347_: *mut leanh::LeanObject,
    mut v_prec_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ =
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_2347_, v_prec_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(
    mut v_dir_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_prec_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_892__boxed_2353_: u8 = 0;
    let mut v_res_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_892__boxed_2353_ = (leanh::lean_unbox(v_dir_2350_) as u8);
    v_res_2354_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(
        v_dir_892__boxed_2353_,
        v_x_2351_,
        v_prec_2352_,
    );
    leanh::lean_dec(v_prec_2352_);
    return v_res_2354_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState(
    mut v_dir_2355_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2356_ = leanh::lean_box((v_dir_2355_) as usize);
    v___x_2357_ = leanh::lean_alloc_closure(
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_2357_, 0, v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState___boxed(
    mut v_dir_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_5__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_2359_ = (leanh::lean_unbox(v_dir_2358_) as u8);
    v_res_2360_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_2359_);
    return v_res_2360_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(
    mut v_x_2361_: *mut leanh::LeanObject,
    mut v_x_2362_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v_a_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: u8 = 0;
    let mut v_a_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: u8 = 0;
    let mut v_a_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut v_error_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2361_) {
                0 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 0 {
                        v___x_2363_ = 1;
                        return v___x_2363_;
                    } else {
                        v___x_2364_ = 0;
                        return v___x_2364_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 1 {
                        v_a_2365_ = leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2366_ = leanh::lean_ctor_get(v_x_2362_, 0);
                        v___x_2367_ = lean_nat_dec_eq(v_a_2365_, v_a_2366_);
                        return v___x_2367_;
                    } else {
                        v___x_2368_ = 0;
                        return v___x_2368_;
                    }
                }
                2 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 2 {
                        v_a_2369_ = leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2370_ = leanh::lean_ctor_get(v_x_2362_, 0);
                        v___x_2371_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(
                            v_a_2369_, v_a_2370_,
                        );
                        return v___x_2371_;
                    } else {
                        v___x_2372_ = 0;
                        return v___x_2372_;
                    }
                }
                3 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 3 {
                        v_a_2373_ = leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2374_ = leanh::lean_ctor_get(v_x_2362_, 0);
                        v_x_2361_ = v_a_2373_;
                        v_x_2362_ = v_a_2374_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2376_ = 0;
                        return v___x_2376_;
                    }
                }
                4 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 4 {
                        v___x_2377_ = 1;
                        return v___x_2377_;
                    } else {
                        v___x_2378_ = 0;
                        return v___x_2378_;
                    }
                }
                5 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 5 {
                        v___x_2379_ = 1;
                        return v___x_2379_;
                    } else {
                        v___x_2380_ = 0;
                        return v___x_2380_;
                    }
                }
                6 => {
                    if leanh::lean_obj_tag(v_x_2362_) == 6 {
                        v___x_2381_ = 1;
                        return v___x_2381_;
                    } else {
                        v___x_2382_ = 0;
                        return v___x_2382_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_x_2362_) == 7 {
                        v_error_2383_ = leanh::lean_ctor_get(v_x_2361_, 0);
                        v_error_2384_ = leanh::lean_ctor_get(v_x_2362_, 0);
                        v___x_2385_ =
                            l_Std_Http_Protocol_H1_instBEqError_beq(v_error_2383_, v_error_2384_);
                        return v___x_2385_;
                    } else {
                        v___x_2386_ = 0;
                        return v___x_2386_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(
    mut v_x_2387_: *mut leanh::LeanObject,
    mut v_x_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2389_: u8 = 0;
    let mut v_r_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_2387_, v_x_2388_);
    leanh::lean_dec(v_x_2388_);
    leanh::lean_dec(v_x_2387_);
    v_r_2390_ = leanh::lean_box((v_res_2389_) as usize);
    return v_r_2390_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq(
    mut v_dir_2391_: u8,
    mut v_x_2392_: *mut leanh::LeanObject,
    mut v_x_2393_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2394_: u8 = 0;
    v___x_2394_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_2392_, v_x_2393_);
    return v___x_2394_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(
    mut v_dir_2395_: *mut leanh::LeanObject,
    mut v_x_2396_: *mut leanh::LeanObject,
    mut v_x_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_218__boxed_2398_: u8 = 0;
    let mut v_res_2399_: u8 = 0;
    let mut v_r_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_218__boxed_2398_ = (leanh::lean_unbox(v_dir_2395_) as u8);
    v_res_2399_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(
        v_dir_218__boxed_2398_,
        v_x_2396_,
        v_x_2397_,
    );
    leanh::lean_dec(v_x_2397_);
    leanh::lean_dec(v_x_2396_);
    v_r_2400_ = leanh::lean_box((v_res_2399_) as usize);
    return v_r_2400_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState(
    mut v_dir_2401_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = leanh::lean_box((v_dir_2401_) as usize);
    v___x_2403_ = leanh::lean_alloc_closure(
        l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_2403_, 0, v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(
    mut v_dir_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_5__boxed_2405_: u8 = 0;
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_2405_ = (leanh::lean_unbox(v_dir_2404_) as u8);
    v_res_2406_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed___redArg(
    mut v_reader_2407_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2408_ = leanh::lean_ctor_get(v_reader_2407_, 0);
    if leanh::lean_obj_tag(v_state_2408_) == 6 {
        let mut v___x_2409_: u8 = 0;
        v___x_2409_ = 1;
        return v___x_2409_;
    } else {
        let mut v___x_2410_: u8 = 0;
        v___x_2410_ = 0;
        return v___x_2410_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(
    mut v_reader_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: u8 = 0;
    let mut v_r_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_2411_);
    leanh::lean_dec_ref(v_reader_2411_);
    v_r_2413_ = leanh::lean_box((v_res_2412_) as usize);
    return v_r_2413_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed(
    mut v_dir_2414_: u8,
    mut v_reader_2415_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2416_ = leanh::lean_ctor_get(v_reader_2415_, 0);
    if leanh::lean_obj_tag(v_state_2416_) == 6 {
        let mut v___x_2417_: u8 = 0;
        v___x_2417_ = 1;
        return v___x_2417_;
    } else {
        let mut v___x_2418_: u8 = 0;
        v___x_2418_ = 0;
        return v___x_2418_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed___boxed(
    mut v_dir_2419_: *mut leanh::LeanObject,
    mut v_reader_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2421_: u8 = 0;
    let mut v_res_2422_: u8 = 0;
    let mut v_r_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2421_ = (leanh::lean_unbox(v_dir_2419_) as u8);
    v_res_2422_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_2421_, v_reader_2420_);
    leanh::lean_dec_ref(v_reader_2420_);
    v_r_2423_ = leanh::lean_box((v_res_2422_) as usize);
    return v_r_2423_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete___redArg(
    mut v_reader_2424_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2425_ = leanh::lean_ctor_get(v_reader_2424_, 0);
    if leanh::lean_obj_tag(v_state_2425_) == 5 {
        let mut v___x_2426_: u8 = 0;
        v___x_2426_ = 1;
        return v___x_2426_;
    } else {
        let mut v___x_2427_: u8 = 0;
        v___x_2427_ = 0;
        return v___x_2427_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(
    mut v_reader_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2429_: u8 = 0;
    let mut v_r_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_2428_);
    leanh::lean_dec_ref(v_reader_2428_);
    v_r_2430_ = leanh::lean_box((v_res_2429_) as usize);
    return v_r_2430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete(
    mut v_dir_2431_: u8,
    mut v_reader_2432_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2433_ = leanh::lean_ctor_get(v_reader_2432_, 0);
    if leanh::lean_obj_tag(v_state_2433_) == 5 {
        let mut v___x_2434_: u8 = 0;
        v___x_2434_ = 1;
        return v___x_2434_;
    } else {
        let mut v___x_2435_: u8 = 0;
        v___x_2435_ = 0;
        return v___x_2435_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete___boxed(
    mut v_dir_2436_: *mut leanh::LeanObject,
    mut v_reader_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2438_: u8 = 0;
    let mut v_res_2439_: u8 = 0;
    let mut v_r_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2438_ = (leanh::lean_unbox(v_dir_2436_) as u8);
    v_res_2439_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_2438_, v_reader_2437_);
    leanh::lean_dec_ref(v_reader_2437_);
    v_r_2440_ = leanh::lean_box((v_res_2439_) as usize);
    return v_r_2440_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(
    mut v_reader_2441_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2442_ = leanh::lean_ctor_get(v_reader_2441_, 0);
    if leanh::lean_obj_tag(v_state_2442_) == 7 {
        let mut v___x_2443_: u8 = 0;
        v___x_2443_ = 1;
        return v___x_2443_;
    } else {
        let mut v___x_2444_: u8 = 0;
        v___x_2444_ = 0;
        return v___x_2444_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(
    mut v_reader_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2446_: u8 = 0;
    let mut v_r_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_2445_);
    leanh::lean_dec_ref(v_reader_2445_);
    v_r_2447_ = leanh::lean_box((v_res_2446_) as usize);
    return v_r_2447_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed(
    mut v_dir_2448_: u8,
    mut v_reader_2449_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2450_ = leanh::lean_ctor_get(v_reader_2449_, 0);
    if leanh::lean_obj_tag(v_state_2450_) == 7 {
        let mut v___x_2451_: u8 = 0;
        v___x_2451_ = 1;
        return v___x_2451_;
    } else {
        let mut v___x_2452_: u8 = 0;
        v___x_2452_ = 0;
        return v___x_2452_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(
    mut v_dir_2453_: *mut leanh::LeanObject,
    mut v_reader_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2455_: u8 = 0;
    let mut v_res_2456_: u8 = 0;
    let mut v_r_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2455_ = (leanh::lean_unbox(v_dir_2453_) as u8);
    v_res_2456_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_2455_, v_reader_2454_);
    leanh::lean_dec_ref(v_reader_2454_);
    v_r_2457_ = leanh::lean_box((v_res_2456_) as usize);
    return v_r_2457_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_feed___redArg(
    mut v_data_2458_: *mut leanh::LeanObject,
    mut v_reader_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2466_: u8 = 0;
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v_array_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2460_ = leanh::lean_ctor_get(v_reader_2459_, 1);
                v_state_2461_ = leanh::lean_ctor_get(v_reader_2459_, 0);
                v_messageHead_2462_ = leanh::lean_ctor_get(v_reader_2459_, 2);
                v_messageCount_2463_ = leanh::lean_ctor_get(v_reader_2459_, 3);
                v_bodyBytesRead_2464_ = leanh::lean_ctor_get(v_reader_2459_, 4);
                v_headerBytesRead_2465_ = leanh::lean_ctor_get(v_reader_2459_, 5);
                v_noMoreInput_2466_ = leanh::lean_ctor_get_uint8(
                    v_reader_2459_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2487_ = (!leanh::lean_is_exclusive(v_reader_2459_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v___x_2468_ = v_reader_2459_;
                    v_isShared_2469_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2465_);
                    leanh::lean_inc(v_bodyBytesRead_2464_);
                    leanh::lean_inc(v_messageCount_2463_);
                    leanh::lean_inc(v_messageHead_2462_);
                    leanh::lean_inc(v_input_2460_);
                    leanh::lean_inc(v_state_2461_);
                    leanh::lean_dec(v_reader_2459_);
                    v___x_2468_ = leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2470_ = leanh::lean_ctor_get(v_input_2460_, 0);
                leanh::lean_inc_ref(v_array_2470_);
                v_idx_2471_ = leanh::lean_ctor_get(v_input_2460_, 1);
                leanh::lean_inc(v_idx_2471_);
                leanh::lean_dec_ref(v_input_2460_);
                v___x_2472_ = lean_byte_array_size(v_array_2470_);
                v___x_2473_ = lean_nat_dec_le(v___x_2472_, v_idx_2471_);
                if v___x_2473_ == 0 {
                    v___x_2474_ = l_ByteArray_extract(v_array_2470_, v_idx_2471_, v___x_2472_);
                    leanh::lean_dec_ref(v_array_2470_);
                    v___x_2475_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2476_ = lean_byte_array_size(v___x_2474_);
                    v___x_2477_ = lean_byte_array_size(v_data_2458_);
                    v___x_2478_ = lean_byte_array_copy_slice(
                        v_data_2458_,
                        v___x_2475_,
                        v___x_2474_,
                        v___x_2476_,
                        v___x_2477_,
                        v___x_2473_,
                    );
                    leanh::lean_dec_ref(v_data_2458_);
                    v___x_2479_ = l_ByteArray_mkIterator(v___x_2478_);
                    if v_isShared_2469_ == 0 {
                        leanh::lean_ctor_set(v___x_2468_, 1, v___x_2479_);
                        v___x_2481_ = v___x_2468_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2482_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_state_2461_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2479_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_messageHead_2462_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            3,
                            v_messageCount_2463_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            4,
                            v_bodyBytesRead_2464_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            5,
                            v_headerBytesRead_2465_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2482_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2466_,
                        );
                        v___x_2481_ = v_reuseFailAlloc_2482_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_idx_2471_);
                    leanh::lean_dec_ref(v_array_2470_);
                    v___x_2483_ = l_ByteArray_mkIterator(v_data_2458_);
                    if v_isShared_2469_ == 0 {
                        leanh::lean_ctor_set(v___x_2468_, 1, v___x_2483_);
                        v___x_2485_ = v___x_2468_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2486_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_state_2461_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2483_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_messageHead_2462_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            3,
                            v_messageCount_2463_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            4,
                            v_bodyBytesRead_2464_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            5,
                            v_headerBytesRead_2465_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2486_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2466_,
                        );
                        v___x_2485_ = v_reuseFailAlloc_2486_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2481_;
            }
            3 => {
                return v___x_2485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_feed(
    mut v_dir_2488_: u8,
    mut v_data_2489_: *mut leanh::LeanObject,
    mut v_reader_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2497_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_array_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2491_ = leanh::lean_ctor_get(v_reader_2490_, 1);
                v_state_2492_ = leanh::lean_ctor_get(v_reader_2490_, 0);
                v_messageHead_2493_ = leanh::lean_ctor_get(v_reader_2490_, 2);
                v_messageCount_2494_ = leanh::lean_ctor_get(v_reader_2490_, 3);
                v_bodyBytesRead_2495_ = leanh::lean_ctor_get(v_reader_2490_, 4);
                v_headerBytesRead_2496_ = leanh::lean_ctor_get(v_reader_2490_, 5);
                v_noMoreInput_2497_ = leanh::lean_ctor_get_uint8(
                    v_reader_2490_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2518_ = (!leanh::lean_is_exclusive(v_reader_2490_)) as u8;
                if v_isSharedCheck_2518_ == 0 {
                    v___x_2499_ = v_reader_2490_;
                    v_isShared_2500_ = v_isSharedCheck_2518_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2496_);
                    leanh::lean_inc(v_bodyBytesRead_2495_);
                    leanh::lean_inc(v_messageCount_2494_);
                    leanh::lean_inc(v_messageHead_2493_);
                    leanh::lean_inc(v_input_2491_);
                    leanh::lean_inc(v_state_2492_);
                    leanh::lean_dec(v_reader_2490_);
                    v___x_2499_ = leanh::lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2501_ = leanh::lean_ctor_get(v_input_2491_, 0);
                leanh::lean_inc_ref(v_array_2501_);
                v_idx_2502_ = leanh::lean_ctor_get(v_input_2491_, 1);
                leanh::lean_inc(v_idx_2502_);
                leanh::lean_dec_ref(v_input_2491_);
                v___x_2503_ = lean_byte_array_size(v_array_2501_);
                v___x_2504_ = lean_nat_dec_le(v___x_2503_, v_idx_2502_);
                if v___x_2504_ == 0 {
                    v___x_2505_ = l_ByteArray_extract(v_array_2501_, v_idx_2502_, v___x_2503_);
                    leanh::lean_dec_ref(v_array_2501_);
                    v___x_2506_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2507_ = lean_byte_array_size(v___x_2505_);
                    v___x_2508_ = lean_byte_array_size(v_data_2489_);
                    v___x_2509_ = lean_byte_array_copy_slice(
                        v_data_2489_,
                        v___x_2506_,
                        v___x_2505_,
                        v___x_2507_,
                        v___x_2508_,
                        v___x_2504_,
                    );
                    leanh::lean_dec_ref(v_data_2489_);
                    v___x_2510_ = l_ByteArray_mkIterator(v___x_2509_);
                    if v_isShared_2500_ == 0 {
                        leanh::lean_ctor_set(v___x_2499_, 1, v___x_2510_);
                        v___x_2512_ = v___x_2499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2513_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_state_2492_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2510_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_messageHead_2493_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            3,
                            v_messageCount_2494_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            4,
                            v_bodyBytesRead_2495_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            5,
                            v_headerBytesRead_2496_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2513_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2497_,
                        );
                        v___x_2512_ = v_reuseFailAlloc_2513_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_idx_2502_);
                    leanh::lean_dec_ref(v_array_2501_);
                    v___x_2514_ = l_ByteArray_mkIterator(v_data_2489_);
                    if v_isShared_2500_ == 0 {
                        leanh::lean_ctor_set(v___x_2499_, 1, v___x_2514_);
                        v___x_2516_ = v___x_2499_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_state_2492_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2514_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_messageHead_2493_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            3,
                            v_messageCount_2494_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            4,
                            v_bodyBytesRead_2495_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            5,
                            v_headerBytesRead_2496_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2517_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2497_,
                        );
                        v___x_2516_ = v_reuseFailAlloc_2517_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2512_;
            }
            3 => {
                return v___x_2516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_feed___boxed(
    mut v_dir_2519_: *mut leanh::LeanObject,
    mut v_data_2520_: *mut leanh::LeanObject,
    mut v_reader_2521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2522_: u8 = 0;
    let mut v_res_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2522_ = (leanh::lean_unbox(v_dir_2519_) as u8);
    v_res_2523_ =
        l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_2522_, v_data_2520_, v_reader_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setInput___redArg(
    mut v_input_2524_: *mut leanh::LeanObject,
    mut v_reader_2525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2531_: u8 = 0;
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v_unused_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2526_ = leanh::lean_ctor_get(v_reader_2525_, 0);
                v_messageHead_2527_ = leanh::lean_ctor_get(v_reader_2525_, 2);
                v_messageCount_2528_ = leanh::lean_ctor_get(v_reader_2525_, 3);
                v_bodyBytesRead_2529_ = leanh::lean_ctor_get(v_reader_2525_, 4);
                v_headerBytesRead_2530_ = leanh::lean_ctor_get(v_reader_2525_, 5);
                v_noMoreInput_2531_ = leanh::lean_ctor_get_uint8(
                    v_reader_2525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2538_ = (!leanh::lean_is_exclusive(v_reader_2525_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v_unused_2539_ = leanh::lean_ctor_get(v_reader_2525_, 1);
                    leanh::lean_dec(v_unused_2539_);
                    v___x_2533_ = v_reader_2525_;
                    v_isShared_2534_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2530_);
                    leanh::lean_inc(v_bodyBytesRead_2529_);
                    leanh::lean_inc(v_messageCount_2528_);
                    leanh::lean_inc(v_messageHead_2527_);
                    leanh::lean_inc(v_state_2526_);
                    leanh::lean_dec(v_reader_2525_);
                    v___x_2533_ = leanh::lean_box(0);
                    v_isShared_2534_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2534_ == 0 {
                    leanh::lean_ctor_set(v___x_2533_, 1, v_input_2524_);
                    v___x_2536_ = v___x_2533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_state_2526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_input_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_messageHead_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_messageCount_2528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_bodyBytesRead_2529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_headerBytesRead_2530_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2537_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2531_,
                    );
                    v___x_2536_ = v_reuseFailAlloc_2537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setInput(
    mut v_dir_2540_: u8,
    mut v_input_2541_: *mut leanh::LeanObject,
    mut v_reader_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2548_: u8 = 0;
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_unused_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2543_ = leanh::lean_ctor_get(v_reader_2542_, 0);
                v_messageHead_2544_ = leanh::lean_ctor_get(v_reader_2542_, 2);
                v_messageCount_2545_ = leanh::lean_ctor_get(v_reader_2542_, 3);
                v_bodyBytesRead_2546_ = leanh::lean_ctor_get(v_reader_2542_, 4);
                v_headerBytesRead_2547_ = leanh::lean_ctor_get(v_reader_2542_, 5);
                v_noMoreInput_2548_ = leanh::lean_ctor_get_uint8(
                    v_reader_2542_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2555_ = (!leanh::lean_is_exclusive(v_reader_2542_)) as u8;
                if v_isSharedCheck_2555_ == 0 {
                    v_unused_2556_ = leanh::lean_ctor_get(v_reader_2542_, 1);
                    leanh::lean_dec(v_unused_2556_);
                    v___x_2550_ = v_reader_2542_;
                    v_isShared_2551_ = v_isSharedCheck_2555_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2547_);
                    leanh::lean_inc(v_bodyBytesRead_2546_);
                    leanh::lean_inc(v_messageCount_2545_);
                    leanh::lean_inc(v_messageHead_2544_);
                    leanh::lean_inc(v_state_2543_);
                    leanh::lean_dec(v_reader_2542_);
                    v___x_2550_ = leanh::lean_box(0);
                    v_isShared_2551_ = v_isSharedCheck_2555_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2551_ == 0 {
                    leanh::lean_ctor_set(v___x_2550_, 1, v_input_2541_);
                    v___x_2553_ = v___x_2550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_state_2543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_input_2541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_messageHead_2544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_messageCount_2545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_bodyBytesRead_2546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 5, v_headerBytesRead_2547_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2554_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2548_,
                    );
                    v___x_2553_ = v_reuseFailAlloc_2554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setInput___boxed(
    mut v_dir_2557_: *mut leanh::LeanObject,
    mut v_input_2558_: *mut leanh::LeanObject,
    mut v_reader_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2560_: u8 = 0;
    let mut v_res_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2560_ = (leanh::lean_unbox(v_dir_2557_) as u8);
    v_res_2561_ =
        l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_2560_, v_input_2558_, v_reader_2559_);
    return v_res_2561_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(
    mut v_messageHead_2562_: *mut leanh::LeanObject,
    mut v_reader_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2569_: u8 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_unused_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2564_ = leanh::lean_ctor_get(v_reader_2563_, 0);
                v_input_2565_ = leanh::lean_ctor_get(v_reader_2563_, 1);
                v_messageCount_2566_ = leanh::lean_ctor_get(v_reader_2563_, 3);
                v_bodyBytesRead_2567_ = leanh::lean_ctor_get(v_reader_2563_, 4);
                v_headerBytesRead_2568_ = leanh::lean_ctor_get(v_reader_2563_, 5);
                v_noMoreInput_2569_ = leanh::lean_ctor_get_uint8(
                    v_reader_2563_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2576_ = (!leanh::lean_is_exclusive(v_reader_2563_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v_unused_2577_ = leanh::lean_ctor_get(v_reader_2563_, 2);
                    leanh::lean_dec(v_unused_2577_);
                    v___x_2571_ = v_reader_2563_;
                    v_isShared_2572_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2568_);
                    leanh::lean_inc(v_bodyBytesRead_2567_);
                    leanh::lean_inc(v_messageCount_2566_);
                    leanh::lean_inc(v_input_2565_);
                    leanh::lean_inc(v_state_2564_);
                    leanh::lean_dec(v_reader_2563_);
                    v___x_2571_ = leanh::lean_box(0);
                    v_isShared_2572_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2572_ == 0 {
                    leanh::lean_ctor_set(v___x_2571_, 2, v_messageHead_2562_);
                    v___x_2574_ = v___x_2571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_state_2564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_input_2565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_messageHead_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_messageCount_2566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_bodyBytesRead_2567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 5, v_headerBytesRead_2568_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2575_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2569_,
                    );
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setMessageHead(
    mut v_dir_2578_: u8,
    mut v_messageHead_2579_: *mut leanh::LeanObject,
    mut v_reader_2580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2586_: u8 = 0;
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_unused_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2581_ = leanh::lean_ctor_get(v_reader_2580_, 0);
                v_input_2582_ = leanh::lean_ctor_get(v_reader_2580_, 1);
                v_messageCount_2583_ = leanh::lean_ctor_get(v_reader_2580_, 3);
                v_bodyBytesRead_2584_ = leanh::lean_ctor_get(v_reader_2580_, 4);
                v_headerBytesRead_2585_ = leanh::lean_ctor_get(v_reader_2580_, 5);
                v_noMoreInput_2586_ = leanh::lean_ctor_get_uint8(
                    v_reader_2580_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2593_ = (!leanh::lean_is_exclusive(v_reader_2580_)) as u8;
                if v_isSharedCheck_2593_ == 0 {
                    v_unused_2594_ = leanh::lean_ctor_get(v_reader_2580_, 2);
                    leanh::lean_dec(v_unused_2594_);
                    v___x_2588_ = v_reader_2580_;
                    v_isShared_2589_ = v_isSharedCheck_2593_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2585_);
                    leanh::lean_inc(v_bodyBytesRead_2584_);
                    leanh::lean_inc(v_messageCount_2583_);
                    leanh::lean_inc(v_input_2582_);
                    leanh::lean_inc(v_state_2581_);
                    leanh::lean_dec(v_reader_2580_);
                    v___x_2588_ = leanh::lean_box(0);
                    v_isShared_2589_ = v_isSharedCheck_2593_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2589_ == 0 {
                    leanh::lean_ctor_set(v___x_2588_, 2, v_messageHead_2579_);
                    v___x_2591_ = v___x_2588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_state_2581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_input_2582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_messageHead_2579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 3, v_messageCount_2583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 4, v_bodyBytesRead_2584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 5, v_headerBytesRead_2585_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2592_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2586_,
                    );
                    v___x_2591_ = v_reuseFailAlloc_2592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(
    mut v_dir_2595_: *mut leanh::LeanObject,
    mut v_messageHead_2596_: *mut leanh::LeanObject,
    mut v_reader_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2598_: u8 = 0;
    let mut v_res_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2598_ = (leanh::lean_unbox(v_dir_2595_) as u8);
    v_res_2599_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(
        v_dir_boxed_2598_,
        v_messageHead_2596_,
        v_reader_2597_,
    );
    return v_res_2599_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(
    mut v_i_2600_: *mut leanh::LeanObject,
    mut v_x_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2601_) == 0 {
                    v___x_2602_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2603_ = lean_mk_empty_array_with_capacity(v___x_2602_);
                    v___x_2604_ = lean_array_push(v___x_2603_, v_i_2600_);
                    v___x_2605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2605_, 0, v___x_2604_);
                    return v___x_2605_;
                } else {
                    v_val_2606_ = leanh::lean_ctor_get(v_x_2601_, 0);
                    v_isSharedCheck_2614_ = (!leanh::lean_is_exclusive(v_x_2601_)) as u8;
                    if v_isSharedCheck_2614_ == 0 {
                        v___x_2608_ = v_x_2601_;
                        v_isShared_2609_ = v_isSharedCheck_2614_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2606_);
                        leanh::lean_dec(v_x_2601_);
                        v___x_2608_ = leanh::lean_box(0);
                        v_isShared_2609_ = v_isSharedCheck_2614_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2610_ = lean_array_push(v_val_2606_, v_i_2600_);
                if v_isShared_2609_ == 0 {
                    leanh::lean_ctor_set(v___x_2608_, 0, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeader(
    mut v_dir_2617_: u8,
    mut v_name_2618_: *mut leanh::LeanObject,
    mut v_value_2619_: *mut leanh::LeanObject,
    mut v_reader_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_messageHead_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2627_: u8 = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v_method_2631_: u8 = 0;
    let mut v_version_2632_: u8 = 0;
    let mut v_uri_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2637_: u8 = 0;
    let mut v_entries_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2642_: u8 = 0;
    let mut v___f_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_unused_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_messageHead_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2670_: u8 = 0;
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v_status_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2675_: u8 = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_entries_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___f_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_unused_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_dir_2617_ == 0 {
                    v_messageHead_2621_ = leanh::lean_ctor_get(v_reader_2620_, 2);
                    v_state_2622_ = leanh::lean_ctor_get(v_reader_2620_, 0);
                    v_input_2623_ = leanh::lean_ctor_get(v_reader_2620_, 1);
                    v_messageCount_2624_ = leanh::lean_ctor_get(v_reader_2620_, 3);
                    v_bodyBytesRead_2625_ = leanh::lean_ctor_get(v_reader_2620_, 4);
                    v_headerBytesRead_2626_ = leanh::lean_ctor_get(v_reader_2620_, 5);
                    v_noMoreInput_2627_ = leanh::lean_ctor_get_uint8(
                        v_reader_2620_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    );
                    v_isSharedCheck_2663_ =
                        (!leanh::lean_is_exclusive(v_reader_2620_)) as u8;
                    if v_isSharedCheck_2663_ == 0 {
                        v___x_2629_ = v_reader_2620_;
                        v_isShared_2630_ = v_isSharedCheck_2663_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_headerBytesRead_2626_);
                        leanh::lean_inc(v_bodyBytesRead_2625_);
                        leanh::lean_inc(v_messageCount_2624_);
                        leanh::lean_inc(v_messageHead_2621_);
                        leanh::lean_inc(v_input_2623_);
                        leanh::lean_inc(v_state_2622_);
                        leanh::lean_dec(v_reader_2620_);
                        v___x_2629_ = leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_messageHead_2664_ = leanh::lean_ctor_get(v_reader_2620_, 2);
                    v_state_2665_ = leanh::lean_ctor_get(v_reader_2620_, 0);
                    v_input_2666_ = leanh::lean_ctor_get(v_reader_2620_, 1);
                    v_messageCount_2667_ = leanh::lean_ctor_get(v_reader_2620_, 3);
                    v_bodyBytesRead_2668_ = leanh::lean_ctor_get(v_reader_2620_, 4);
                    v_headerBytesRead_2669_ = leanh::lean_ctor_get(v_reader_2620_, 5);
                    v_noMoreInput_2670_ = leanh::lean_ctor_get_uint8(
                        v_reader_2620_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    );
                    v_isSharedCheck_2705_ =
                        (!leanh::lean_is_exclusive(v_reader_2620_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2672_ = v_reader_2620_;
                        v_isShared_2673_ = v_isSharedCheck_2705_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_headerBytesRead_2669_);
                        leanh::lean_inc(v_bodyBytesRead_2668_);
                        leanh::lean_inc(v_messageCount_2667_);
                        leanh::lean_inc(v_messageHead_2664_);
                        leanh::lean_inc(v_input_2666_);
                        leanh::lean_inc(v_state_2665_);
                        leanh::lean_dec(v_reader_2620_);
                        v___x_2672_ = leanh::lean_box(0);
                        v_isShared_2673_ = v_isSharedCheck_2705_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_method_2631_ = leanh::lean_ctor_get_uint8(
                    v_messageHead_2621_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_version_2632_ = leanh::lean_ctor_get_uint8(
                    v_messageHead_2621_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_2633_ = leanh::lean_ctor_get(v_messageHead_2621_, 0);
                leanh::lean_inc(v_uri_2633_);
                v___x_2634_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_2617_, v_messageHead_2621_);
                v_isSharedCheck_2660_ =
                    (!leanh::lean_is_exclusive(v_messageHead_2621_)) as u8;
                if v_isSharedCheck_2660_ == 0 {
                    v_unused_2661_ = leanh::lean_ctor_get(v_messageHead_2621_, 1);
                    leanh::lean_dec(v_unused_2661_);
                    v_unused_2662_ = leanh::lean_ctor_get(v_messageHead_2621_, 0);
                    leanh::lean_dec(v_unused_2662_);
                    v___x_2636_ = v_messageHead_2621_;
                    v_isShared_2637_ = v_isSharedCheck_2660_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_messageHead_2621_);
                    v___x_2636_ = leanh::lean_box(0);
                    v_isShared_2637_ = v_isSharedCheck_2660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_2638_ = leanh::lean_ctor_get(v___x_2634_, 0);
                v_indexes_2639_ = leanh::lean_ctor_get(v___x_2634_, 1);
                v_isSharedCheck_2659_ = (!leanh::lean_is_exclusive(v___x_2634_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v___x_2641_ = v___x_2634_;
                    v_isShared_2642_ = v_isSharedCheck_2659_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2639_);
                    leanh::lean_inc(v_entries_2638_);
                    leanh::lean_dec(v___x_2634_);
                    v___x_2641_ = leanh::lean_box(0);
                    v_isShared_2642_ = v_isSharedCheck_2659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_2643_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__0;
                v___f_2644_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__1;
                v_i_2645_ = lean_array_get_size(v_entries_2638_);
                v_f_2646_ = leanh::lean_alloc_closure(
                    l_Std_Http_Protocol_H1_Reader_addHeader___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2646_, 0, v_i_2645_);
                leanh::lean_inc_ref(v_name_2618_);
                v___x_2647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2647_, 0, v_name_2618_);
                leanh::lean_ctor_set(v___x_2647_, 1, v_value_2619_);
                v_entries_2648_ = lean_array_push(v_entries_2638_, v___x_2647_);
                v_indexes_2649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2643_,
                    v___f_2644_,
                    v_indexes_2639_,
                    v_name_2618_,
                    v_f_2646_,
                );
                if v_isShared_2642_ == 0 {
                    leanh::lean_ctor_set(v___x_2641_, 1, v_indexes_2649_);
                    leanh::lean_ctor_set(v___x_2641_, 0, v_entries_2648_);
                    v___x_2651_ = v___x_2641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_entries_2648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_indexes_2649_);
                    v___x_2651_ = v_reuseFailAlloc_2658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2637_ == 0 {
                    leanh::lean_ctor_set(v___x_2636_, 1, v___x_2651_);
                    v___x_2653_ = v___x_2636_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_uri_2633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2651_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2657_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_method_2631_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2657_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_2632_,
                    );
                    v___x_2653_ = v_reuseFailAlloc_2657_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2630_ == 0 {
                    leanh::lean_ctor_set(v___x_2629_, 2, v___x_2653_);
                    v___x_2655_ = v___x_2629_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_state_2622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_input_2623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 2, v___x_2653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_messageCount_2624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_bodyBytesRead_2625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_headerBytesRead_2626_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2656_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2627_,
                    );
                    v___x_2655_ = v_reuseFailAlloc_2656_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2655_;
            }
            7 => {
                v_status_2674_ = leanh::lean_ctor_get(v_messageHead_2664_, 0);
                leanh::lean_inc(v_status_2674_);
                v_version_2675_ = leanh::lean_ctor_get_uint8(
                    v_messageHead_2664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v___x_2676_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_2617_, v_messageHead_2664_);
                v_isSharedCheck_2702_ =
                    (!leanh::lean_is_exclusive(v_messageHead_2664_)) as u8;
                if v_isSharedCheck_2702_ == 0 {
                    v_unused_2703_ = leanh::lean_ctor_get(v_messageHead_2664_, 1);
                    leanh::lean_dec(v_unused_2703_);
                    v_unused_2704_ = leanh::lean_ctor_get(v_messageHead_2664_, 0);
                    leanh::lean_dec(v_unused_2704_);
                    v___x_2678_ = v_messageHead_2664_;
                    v_isShared_2679_ = v_isSharedCheck_2702_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec(v_messageHead_2664_);
                    v___x_2678_ = leanh::lean_box(0);
                    v_isShared_2679_ = v_isSharedCheck_2702_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_entries_2680_ = leanh::lean_ctor_get(v___x_2676_, 0);
                v_indexes_2681_ = leanh::lean_ctor_get(v___x_2676_, 1);
                v_isSharedCheck_2701_ = (!leanh::lean_is_exclusive(v___x_2676_)) as u8;
                if v_isSharedCheck_2701_ == 0 {
                    v___x_2683_ = v___x_2676_;
                    v_isShared_2684_ = v_isSharedCheck_2701_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2681_);
                    leanh::lean_inc(v_entries_2680_);
                    leanh::lean_dec(v___x_2676_);
                    v___x_2683_ = leanh::lean_box(0);
                    v_isShared_2684_ = v_isSharedCheck_2701_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___f_2685_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__0;
                v___f_2686_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__1;
                v_i_2687_ = lean_array_get_size(v_entries_2680_);
                v_f_2688_ = leanh::lean_alloc_closure(
                    l_Std_Http_Protocol_H1_Reader_addHeader___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2688_, 0, v_i_2687_);
                leanh::lean_inc_ref(v_name_2618_);
                v___x_2689_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2689_, 0, v_name_2618_);
                leanh::lean_ctor_set(v___x_2689_, 1, v_value_2619_);
                v_entries_2690_ = lean_array_push(v_entries_2680_, v___x_2689_);
                v_indexes_2691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2685_,
                    v___f_2686_,
                    v_indexes_2681_,
                    v_name_2618_,
                    v_f_2688_,
                );
                if v_isShared_2684_ == 0 {
                    leanh::lean_ctor_set(v___x_2683_, 1, v_indexes_2691_);
                    leanh::lean_ctor_set(v___x_2683_, 0, v_entries_2690_);
                    v___x_2693_ = v___x_2683_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_entries_2690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_indexes_2691_);
                    v___x_2693_ = v_reuseFailAlloc_2700_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2679_ == 0 {
                    leanh::lean_ctor_set(v___x_2678_, 1, v___x_2693_);
                    v___x_2695_ = v___x_2678_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_status_2674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2693_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2699_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_version_2675_,
                    );
                    v___x_2695_ = v_reuseFailAlloc_2699_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2673_ == 0 {
                    leanh::lean_ctor_set(v___x_2672_, 2, v___x_2695_);
                    v___x_2697_ = v___x_2672_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2698_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_state_2665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_input_2666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 2, v___x_2695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_messageCount_2667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_bodyBytesRead_2668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_headerBytesRead_2669_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2698_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2670_,
                    );
                    v___x_2697_ = v_reuseFailAlloc_2698_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeader___boxed(
    mut v_dir_2706_: *mut leanh::LeanObject,
    mut v_name_2707_: *mut leanh::LeanObject,
    mut v_value_2708_: *mut leanh::LeanObject,
    mut v_reader_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2710_: u8 = 0;
    let mut v_res_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2710_ = (leanh::lean_unbox(v_dir_2706_) as u8);
    v_res_2711_ = l_Std_Http_Protocol_H1_Reader_addHeader(
        v_dir_boxed_2710_,
        v_name_2707_,
        v_value_2708_,
        v_reader_2709_,
    );
    return v_res_2711_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_close___redArg(
    mut v_reader_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_unused_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2713_ = leanh::lean_ctor_get(v_reader_2712_, 1);
                v_messageHead_2714_ = leanh::lean_ctor_get(v_reader_2712_, 2);
                v_messageCount_2715_ = leanh::lean_ctor_get(v_reader_2712_, 3);
                v_bodyBytesRead_2716_ = leanh::lean_ctor_get(v_reader_2712_, 4);
                v_headerBytesRead_2717_ = leanh::lean_ctor_get(v_reader_2712_, 5);
                v_isSharedCheck_2726_ = (!leanh::lean_is_exclusive(v_reader_2712_)) as u8;
                if v_isSharedCheck_2726_ == 0 {
                    v_unused_2727_ = leanh::lean_ctor_get(v_reader_2712_, 0);
                    leanh::lean_dec(v_unused_2727_);
                    v___x_2719_ = v_reader_2712_;
                    v_isShared_2720_ = v_isSharedCheck_2726_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2717_);
                    leanh::lean_inc(v_bodyBytesRead_2716_);
                    leanh::lean_inc(v_messageCount_2715_);
                    leanh::lean_inc(v_messageHead_2714_);
                    leanh::lean_inc(v_input_2713_);
                    leanh::lean_dec(v_reader_2712_);
                    v___x_2719_ = leanh::lean_box(0);
                    v_isShared_2720_ = v_isSharedCheck_2726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2721_ = leanh::lean_box(6);
                v___x_2722_ = 1;
                if v_isShared_2720_ == 0 {
                    leanh::lean_ctor_set(v___x_2719_, 0, v___x_2721_);
                    v___x_2724_ = v___x_2719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_input_2713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_messageHead_2714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_messageCount_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_bodyBytesRead_2716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_headerBytesRead_2717_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2724_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_2722_,
                );
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_close(
    mut v_dir_2728_: u8,
    mut v_reader_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2737_: u8 = 0;
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v_unused_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2730_ = leanh::lean_ctor_get(v_reader_2729_, 1);
                v_messageHead_2731_ = leanh::lean_ctor_get(v_reader_2729_, 2);
                v_messageCount_2732_ = leanh::lean_ctor_get(v_reader_2729_, 3);
                v_bodyBytesRead_2733_ = leanh::lean_ctor_get(v_reader_2729_, 4);
                v_headerBytesRead_2734_ = leanh::lean_ctor_get(v_reader_2729_, 5);
                v_isSharedCheck_2743_ = (!leanh::lean_is_exclusive(v_reader_2729_)) as u8;
                if v_isSharedCheck_2743_ == 0 {
                    v_unused_2744_ = leanh::lean_ctor_get(v_reader_2729_, 0);
                    leanh::lean_dec(v_unused_2744_);
                    v___x_2736_ = v_reader_2729_;
                    v_isShared_2737_ = v_isSharedCheck_2743_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2734_);
                    leanh::lean_inc(v_bodyBytesRead_2733_);
                    leanh::lean_inc(v_messageCount_2732_);
                    leanh::lean_inc(v_messageHead_2731_);
                    leanh::lean_inc(v_input_2730_);
                    leanh::lean_dec(v_reader_2729_);
                    v___x_2736_ = leanh::lean_box(0);
                    v_isShared_2737_ = v_isSharedCheck_2743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2738_ = leanh::lean_box(6);
                v___x_2739_ = 1;
                if v_isShared_2737_ == 0 {
                    leanh::lean_ctor_set(v___x_2736_, 0, v___x_2738_);
                    v___x_2741_ = v___x_2736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_input_2730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_messageHead_2731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_messageCount_2732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_bodyBytesRead_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_headerBytesRead_2734_);
                    v___x_2741_ = v_reuseFailAlloc_2742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2741_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_2739_,
                );
                return v___x_2741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_close___boxed(
    mut v_dir_2745_: *mut leanh::LeanObject,
    mut v_reader_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2747_: u8 = 0;
    let mut v_res_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2747_ = (leanh::lean_unbox(v_dir_2745_) as u8);
    v_res_2748_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_2747_, v_reader_2746_);
    return v_res_2748_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markComplete___redArg(
    mut v_reader_2749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2755_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_unused_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2750_ = leanh::lean_ctor_get(v_reader_2749_, 1);
                v_messageHead_2751_ = leanh::lean_ctor_get(v_reader_2749_, 2);
                v_messageCount_2752_ = leanh::lean_ctor_get(v_reader_2749_, 3);
                v_bodyBytesRead_2753_ = leanh::lean_ctor_get(v_reader_2749_, 4);
                v_headerBytesRead_2754_ = leanh::lean_ctor_get(v_reader_2749_, 5);
                v_noMoreInput_2755_ = leanh::lean_ctor_get_uint8(
                    v_reader_2749_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2765_ = (!leanh::lean_is_exclusive(v_reader_2749_)) as u8;
                if v_isSharedCheck_2765_ == 0 {
                    v_unused_2766_ = leanh::lean_ctor_get(v_reader_2749_, 0);
                    leanh::lean_dec(v_unused_2766_);
                    v___x_2757_ = v_reader_2749_;
                    v_isShared_2758_ = v_isSharedCheck_2765_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2754_);
                    leanh::lean_inc(v_bodyBytesRead_2753_);
                    leanh::lean_inc(v_messageCount_2752_);
                    leanh::lean_inc(v_messageHead_2751_);
                    leanh::lean_inc(v_input_2750_);
                    leanh::lean_dec(v_reader_2749_);
                    v___x_2757_ = leanh::lean_box(0);
                    v_isShared_2758_ = v_isSharedCheck_2765_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2759_ = leanh::lean_box(5);
                v___x_2760_ = leanh::lean_unsigned_to_nat(1);
                v___x_2761_ = lean_nat_add(v_messageCount_2752_, v___x_2760_);
                leanh::lean_dec(v_messageCount_2752_);
                if v_isShared_2758_ == 0 {
                    leanh::lean_ctor_set(v___x_2757_, 3, v___x_2761_);
                    leanh::lean_ctor_set(v___x_2757_, 0, v___x_2759_);
                    v___x_2763_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_input_2750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_messageHead_2751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 3, v___x_2761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 4, v_bodyBytesRead_2753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 5, v_headerBytesRead_2754_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2764_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2755_,
                    );
                    v___x_2763_ = v_reuseFailAlloc_2764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2763_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markComplete(
    mut v_dir_2767_: u8,
    mut v_reader_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2774_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_unused_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2769_ = leanh::lean_ctor_get(v_reader_2768_, 1);
                v_messageHead_2770_ = leanh::lean_ctor_get(v_reader_2768_, 2);
                v_messageCount_2771_ = leanh::lean_ctor_get(v_reader_2768_, 3);
                v_bodyBytesRead_2772_ = leanh::lean_ctor_get(v_reader_2768_, 4);
                v_headerBytesRead_2773_ = leanh::lean_ctor_get(v_reader_2768_, 5);
                v_noMoreInput_2774_ = leanh::lean_ctor_get_uint8(
                    v_reader_2768_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2784_ = (!leanh::lean_is_exclusive(v_reader_2768_)) as u8;
                if v_isSharedCheck_2784_ == 0 {
                    v_unused_2785_ = leanh::lean_ctor_get(v_reader_2768_, 0);
                    leanh::lean_dec(v_unused_2785_);
                    v___x_2776_ = v_reader_2768_;
                    v_isShared_2777_ = v_isSharedCheck_2784_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2773_);
                    leanh::lean_inc(v_bodyBytesRead_2772_);
                    leanh::lean_inc(v_messageCount_2771_);
                    leanh::lean_inc(v_messageHead_2770_);
                    leanh::lean_inc(v_input_2769_);
                    leanh::lean_dec(v_reader_2768_);
                    v___x_2776_ = leanh::lean_box(0);
                    v_isShared_2777_ = v_isSharedCheck_2784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2778_ = leanh::lean_box(5);
                v___x_2779_ = leanh::lean_unsigned_to_nat(1);
                v___x_2780_ = lean_nat_add(v_messageCount_2771_, v___x_2779_);
                leanh::lean_dec(v_messageCount_2771_);
                if v_isShared_2777_ == 0 {
                    leanh::lean_ctor_set(v___x_2776_, 3, v___x_2780_);
                    leanh::lean_ctor_set(v___x_2776_, 0, v___x_2778_);
                    v___x_2782_ = v___x_2776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_input_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 2, v_messageHead_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 3, v___x_2780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 4, v_bodyBytesRead_2772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 5, v_headerBytesRead_2773_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2783_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2774_,
                    );
                    v___x_2782_ = v_reuseFailAlloc_2783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markComplete___boxed(
    mut v_dir_2786_: *mut leanh::LeanObject,
    mut v_reader_2787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2788_: u8 = 0;
    let mut v_res_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2788_ = (leanh::lean_unbox(v_dir_2786_) as u8);
    v_res_2789_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_2788_, v_reader_2787_);
    return v_res_2789_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_fail___redArg(
    mut v_error_2790_: *mut leanh::LeanObject,
    mut v_reader_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2797_: u8 = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_unused_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2792_ = leanh::lean_ctor_get(v_reader_2791_, 1);
                v_messageHead_2793_ = leanh::lean_ctor_get(v_reader_2791_, 2);
                v_messageCount_2794_ = leanh::lean_ctor_get(v_reader_2791_, 3);
                v_bodyBytesRead_2795_ = leanh::lean_ctor_get(v_reader_2791_, 4);
                v_headerBytesRead_2796_ = leanh::lean_ctor_get(v_reader_2791_, 5);
                v_noMoreInput_2797_ = leanh::lean_ctor_get_uint8(
                    v_reader_2791_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2805_ = (!leanh::lean_is_exclusive(v_reader_2791_)) as u8;
                if v_isSharedCheck_2805_ == 0 {
                    v_unused_2806_ = leanh::lean_ctor_get(v_reader_2791_, 0);
                    leanh::lean_dec(v_unused_2806_);
                    v___x_2799_ = v_reader_2791_;
                    v_isShared_2800_ = v_isSharedCheck_2805_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2796_);
                    leanh::lean_inc(v_bodyBytesRead_2795_);
                    leanh::lean_inc(v_messageCount_2794_);
                    leanh::lean_inc(v_messageHead_2793_);
                    leanh::lean_inc(v_input_2792_);
                    leanh::lean_dec(v_reader_2791_);
                    v___x_2799_ = leanh::lean_box(0);
                    v_isShared_2800_ = v_isSharedCheck_2805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2801_ = leanh::lean_alloc_ctor(7, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2801_, 0, v_error_2790_);
                if v_isShared_2800_ == 0 {
                    leanh::lean_ctor_set(v___x_2799_, 0, v___x_2801_);
                    v___x_2803_ = v___x_2799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_input_2792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 2, v_messageHead_2793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 3, v_messageCount_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 4, v_bodyBytesRead_2795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 5, v_headerBytesRead_2796_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2804_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2797_,
                    );
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_fail(
    mut v_dir_2807_: u8,
    mut v_error_2808_: *mut leanh::LeanObject,
    mut v_reader_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2815_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2810_ = leanh::lean_ctor_get(v_reader_2809_, 1);
                v_messageHead_2811_ = leanh::lean_ctor_get(v_reader_2809_, 2);
                v_messageCount_2812_ = leanh::lean_ctor_get(v_reader_2809_, 3);
                v_bodyBytesRead_2813_ = leanh::lean_ctor_get(v_reader_2809_, 4);
                v_headerBytesRead_2814_ = leanh::lean_ctor_get(v_reader_2809_, 5);
                v_noMoreInput_2815_ = leanh::lean_ctor_get_uint8(
                    v_reader_2809_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2823_ = (!leanh::lean_is_exclusive(v_reader_2809_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = leanh::lean_ctor_get(v_reader_2809_, 0);
                    leanh::lean_dec(v_unused_2824_);
                    v___x_2817_ = v_reader_2809_;
                    v_isShared_2818_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2814_);
                    leanh::lean_inc(v_bodyBytesRead_2813_);
                    leanh::lean_inc(v_messageCount_2812_);
                    leanh::lean_inc(v_messageHead_2811_);
                    leanh::lean_inc(v_input_2810_);
                    leanh::lean_dec(v_reader_2809_);
                    v___x_2817_ = leanh::lean_box(0);
                    v_isShared_2818_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2819_ = leanh::lean_alloc_ctor(7, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2819_, 0, v_error_2808_);
                if v_isShared_2818_ == 0 {
                    leanh::lean_ctor_set(v___x_2817_, 0, v___x_2819_);
                    v___x_2821_ = v___x_2817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_input_2810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_messageHead_2811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_messageCount_2812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_bodyBytesRead_2813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_headerBytesRead_2814_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2822_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2815_,
                    );
                    v___x_2821_ = v_reuseFailAlloc_2822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_fail___boxed(
    mut v_dir_2825_: *mut leanh::LeanObject,
    mut v_error_2826_: *mut leanh::LeanObject,
    mut v_reader_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2828_: u8 = 0;
    let mut v_res_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2828_ = (leanh::lean_unbox(v_dir_2825_) as u8);
    v_res_2829_ =
        l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_2828_, v_error_2826_, v_reader_2827_);
    return v_res_2829_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_reset(
    mut v_dir_2830_: u8,
    mut v_reader_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2834_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2832_ = leanh::lean_ctor_get(v_reader_2831_, 1);
                v_messageCount_2833_ = leanh::lean_ctor_get(v_reader_2831_, 3);
                v_noMoreInput_2834_ = leanh::lean_ctor_get_uint8(
                    v_reader_2831_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2844_ = (!leanh::lean_is_exclusive(v_reader_2831_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v_unused_2845_ = leanh::lean_ctor_get(v_reader_2831_, 5);
                    leanh::lean_dec(v_unused_2845_);
                    v_unused_2846_ = leanh::lean_ctor_get(v_reader_2831_, 4);
                    leanh::lean_dec(v_unused_2846_);
                    v_unused_2847_ = leanh::lean_ctor_get(v_reader_2831_, 2);
                    leanh::lean_dec(v_unused_2847_);
                    v_unused_2848_ = leanh::lean_ctor_get(v_reader_2831_, 0);
                    leanh::lean_dec(v_unused_2848_);
                    v___x_2836_ = v_reader_2831_;
                    v_isShared_2837_ = v_isSharedCheck_2844_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_messageCount_2833_);
                    leanh::lean_inc(v_input_2832_);
                    leanh::lean_dec(v_reader_2831_);
                    v___x_2836_ = leanh::lean_box(0);
                    v_isShared_2837_ = v_isSharedCheck_2844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2838_ = leanh::lean_box(0);
                v___x_2839_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_2830_);
                v___x_2840_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_2837_ == 0 {
                    leanh::lean_ctor_set(v___x_2836_, 5, v___x_2840_);
                    leanh::lean_ctor_set(v___x_2836_, 4, v___x_2840_);
                    leanh::lean_ctor_set(v___x_2836_, 2, v___x_2839_);
                    leanh::lean_ctor_set(v___x_2836_, 0, v___x_2838_);
                    v___x_2842_ = v___x_2836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_input_2832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v___x_2839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_messageCount_2833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v___x_2840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 5, v___x_2840_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2843_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2834_,
                    );
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_reset___boxed(
    mut v_dir_2849_: *mut leanh::LeanObject,
    mut v_reader_2850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2851_: u8 = 0;
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2851_ = (leanh::lean_unbox(v_dir_2849_) as u8);
    v_res_2852_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_2851_, v_reader_2850_);
    return v_res_2852_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(
    mut v_reader_2853_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2856_: u8 = 0;
    let mut v___y_2858_: u8 = 0;
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: u8 = 0;
    let mut v_array_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2854_ = leanh::lean_ctor_get(v_reader_2853_, 0);
                v_input_2855_ = leanh::lean_ctor_get(v_reader_2853_, 1);
                v_noMoreInput_2856_ = leanh::lean_ctor_get_uint8(
                    v_reader_2853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_array_2863_ = leanh::lean_ctor_get(v_input_2855_, 0);
                v_idx_2864_ = leanh::lean_ctor_get(v_input_2855_, 1);
                v___x_2865_ = lean_byte_array_size(v_array_2863_);
                v___x_2866_ = lean_nat_dec_le(v___x_2865_, v_idx_2864_);
                if v___x_2866_ == 0 {
                    v___y_2858_ = v___x_2866_;
                    state = 1;
                    continue;
                } else {
                    if v_noMoreInput_2856_ == 0 {
                        v___y_2858_ = v___x_2866_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2867_ = 0;
                        return v___x_2867_;
                    }
                }
            }
            1 => {
                if v___y_2858_ == 0 {
                    return v___y_2858_;
                } else {
                    match leanh::lean_obj_tag(v_state_2854_) {
                        5 => {
                            v___x_2859_ = 0;
                            return v___x_2859_;
                        }
                        6 => {
                            v___x_2860_ = 0;
                            return v___x_2860_;
                        }
                        7 => {
                            v___x_2861_ = 0;
                            return v___x_2861_;
                        }
                        3 => {
                            v___x_2862_ = 0;
                            return v___x_2862_;
                        }
                        _ => {
                            return v___y_2858_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(
    mut v_reader_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2869_: u8 = 0;
    let mut v_r_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_2868_);
    leanh::lean_dec_ref(v_reader_2868_);
    v_r_2870_ = leanh::lean_box((v_res_2869_) as usize);
    return v_r_2870_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput(
    mut v_dir_2871_: u8,
    mut v_reader_2872_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_state_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2875_: u8 = 0;
    let mut v___y_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: u8 = 0;
    let mut v_array_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2873_ = leanh::lean_ctor_get(v_reader_2872_, 0);
                v_input_2874_ = leanh::lean_ctor_get(v_reader_2872_, 1);
                v_noMoreInput_2875_ = leanh::lean_ctor_get_uint8(
                    v_reader_2872_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_array_2882_ = leanh::lean_ctor_get(v_input_2874_, 0);
                v_idx_2883_ = leanh::lean_ctor_get(v_input_2874_, 1);
                v___x_2884_ = lean_byte_array_size(v_array_2882_);
                v___x_2885_ = lean_nat_dec_le(v___x_2884_, v_idx_2883_);
                if v___x_2885_ == 0 {
                    v___y_2877_ = v___x_2885_;
                    state = 1;
                    continue;
                } else {
                    if v_noMoreInput_2875_ == 0 {
                        v___y_2877_ = v___x_2885_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2886_ = 0;
                        return v___x_2886_;
                    }
                }
            }
            1 => {
                if v___y_2877_ == 0 {
                    return v___y_2877_;
                } else {
                    match leanh::lean_obj_tag(v_state_2873_) {
                        5 => {
                            v___x_2878_ = 0;
                            return v___x_2878_;
                        }
                        6 => {
                            v___x_2879_ = 0;
                            return v___x_2879_;
                        }
                        7 => {
                            v___x_2880_ = 0;
                            return v___x_2880_;
                        }
                        3 => {
                            v___x_2881_ = 0;
                            return v___x_2881_;
                        }
                        _ => {
                            return v___y_2877_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(
    mut v_dir_2887_: *mut leanh::LeanObject,
    mut v_reader_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2889_: u8 = 0;
    let mut v_res_2890_: u8 = 0;
    let mut v_r_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2889_ = (leanh::lean_unbox(v_dir_2887_) as u8);
    v_res_2890_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_2889_, v_reader_2888_);
    leanh::lean_dec_ref(v_reader_2888_);
    v_r_2891_ = leanh::lean_box((v_res_2890_) as usize);
    return v_r_2891_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_getError___redArg(
    mut v_reader_2892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2893_ = leanh::lean_ctor_get(v_reader_2892_, 0);
                leanh::lean_inc(v_state_2893_);
                leanh::lean_dec_ref(v_reader_2892_);
                if leanh::lean_obj_tag(v_state_2893_) == 7 {
                    v_error_2894_ = leanh::lean_ctor_get(v_state_2893_, 0);
                    v_isSharedCheck_2901_ = (!leanh::lean_is_exclusive(v_state_2893_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v_state_2893_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_error_2894_);
                        leanh::lean_dec(v_state_2893_);
                        v___x_2896_ = leanh::lean_box(0);
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_state_2893_);
                    v___x_2902_ = leanh::lean_box(0);
                    return v___x_2902_;
                }
            }
            1 => {
                if v_isShared_2897_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2896_, 1);
                    v___x_2899_ = v___x_2896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_error_2894_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_getError(
    mut v_dir_2903_: u8,
    mut v_reader_2904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2905_ = leanh::lean_ctor_get(v_reader_2904_, 0);
                leanh::lean_inc(v_state_2905_);
                leanh::lean_dec_ref(v_reader_2904_);
                if leanh::lean_obj_tag(v_state_2905_) == 7 {
                    v_error_2906_ = leanh::lean_ctor_get(v_state_2905_, 0);
                    v_isSharedCheck_2913_ = (!leanh::lean_is_exclusive(v_state_2905_)) as u8;
                    if v_isSharedCheck_2913_ == 0 {
                        v___x_2908_ = v_state_2905_;
                        v_isShared_2909_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_error_2906_);
                        leanh::lean_dec(v_state_2905_);
                        v___x_2908_ = leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_state_2905_);
                    v___x_2914_ = leanh::lean_box(0);
                    return v___x_2914_;
                }
            }
            1 => {
                if v_isShared_2909_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2908_, 1);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_error_2906_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_getError___boxed(
    mut v_dir_2915_: *mut leanh::LeanObject,
    mut v_reader_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2917_: u8 = 0;
    let mut v_res_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2917_ = (leanh::lean_unbox(v_dir_2915_) as u8);
    v_res_2918_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_2917_, v_reader_2916_);
    return v_res_2918_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(
    mut v_reader_2919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_input_2920_ = leanh::lean_ctor_get(v_reader_2919_, 1);
    v_array_2921_ = leanh::lean_ctor_get(v_input_2920_, 0);
    v_idx_2922_ = leanh::lean_ctor_get(v_input_2920_, 1);
    v___x_2923_ = lean_byte_array_size(v_array_2921_);
    v___x_2924_ = lean_nat_sub(v___x_2923_, v_idx_2922_);
    return v___x_2924_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(
    mut v_reader_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_2925_);
    leanh::lean_dec_ref(v_reader_2925_);
    return v_res_2926_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes(
    mut v_dir_2927_: u8,
    mut v_reader_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_input_2929_ = leanh::lean_ctor_get(v_reader_2928_, 1);
    v_array_2930_ = leanh::lean_ctor_get(v_input_2929_, 0);
    v_idx_2931_ = leanh::lean_ctor_get(v_input_2929_, 1);
    v___x_2932_ = lean_byte_array_size(v_array_2930_);
    v___x_2933_ = lean_nat_sub(v___x_2932_, v_idx_2931_);
    return v___x_2933_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(
    mut v_dir_2934_: *mut leanh::LeanObject,
    mut v_reader_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2936_: u8 = 0;
    let mut v_res_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2936_ = (leanh::lean_unbox(v_dir_2934_) as u8);
    v_res_2937_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_2936_, v_reader_2935_);
    leanh::lean_dec_ref(v_reader_2935_);
    return v_res_2937_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance___redArg(
    mut v_n_2938_: *mut leanh::LeanObject,
    mut v_reader_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2946_: u8 = 0;
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v_array_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2940_ = leanh::lean_ctor_get(v_reader_2939_, 1);
                v_state_2941_ = leanh::lean_ctor_get(v_reader_2939_, 0);
                v_messageHead_2942_ = leanh::lean_ctor_get(v_reader_2939_, 2);
                v_messageCount_2943_ = leanh::lean_ctor_get(v_reader_2939_, 3);
                v_bodyBytesRead_2944_ = leanh::lean_ctor_get(v_reader_2939_, 4);
                v_headerBytesRead_2945_ = leanh::lean_ctor_get(v_reader_2939_, 5);
                v_noMoreInput_2946_ = leanh::lean_ctor_get_uint8(
                    v_reader_2939_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2963_ = (!leanh::lean_is_exclusive(v_reader_2939_)) as u8;
                if v_isSharedCheck_2963_ == 0 {
                    v___x_2948_ = v_reader_2939_;
                    v_isShared_2949_ = v_isSharedCheck_2963_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2945_);
                    leanh::lean_inc(v_bodyBytesRead_2944_);
                    leanh::lean_inc(v_messageCount_2943_);
                    leanh::lean_inc(v_messageHead_2942_);
                    leanh::lean_inc(v_input_2940_);
                    leanh::lean_inc(v_state_2941_);
                    leanh::lean_dec(v_reader_2939_);
                    v___x_2948_ = leanh::lean_box(0);
                    v_isShared_2949_ = v_isSharedCheck_2963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2950_ = leanh::lean_ctor_get(v_input_2940_, 0);
                v_idx_2951_ = leanh::lean_ctor_get(v_input_2940_, 1);
                v_isSharedCheck_2962_ = (!leanh::lean_is_exclusive(v_input_2940_)) as u8;
                if v_isSharedCheck_2962_ == 0 {
                    v___x_2953_ = v_input_2940_;
                    v_isShared_2954_ = v_isSharedCheck_2962_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_2951_);
                    leanh::lean_inc(v_array_2950_);
                    leanh::lean_dec(v_input_2940_);
                    v___x_2953_ = leanh::lean_box(0);
                    v_isShared_2954_ = v_isSharedCheck_2962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2955_ = lean_nat_add(v_idx_2951_, v_n_2938_);
                leanh::lean_dec(v_idx_2951_);
                if v_isShared_2954_ == 0 {
                    leanh::lean_ctor_set(v___x_2953_, 1, v___x_2955_);
                    v___x_2957_ = v___x_2953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2961_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_array_2950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2955_);
                    v___x_2957_ = v_reuseFailAlloc_2961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2949_ == 0 {
                    leanh::lean_ctor_set(v___x_2948_, 1, v___x_2957_);
                    v___x_2959_ = v___x_2948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_state_2941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_messageHead_2942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_messageCount_2943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_bodyBytesRead_2944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_headerBytesRead_2945_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2960_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2946_,
                    );
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(
    mut v_n_2964_: *mut leanh::LeanObject,
    mut v_reader_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_2964_, v_reader_2965_);
    leanh::lean_dec(v_n_2964_);
    return v_res_2966_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance(
    mut v_dir_2967_: u8,
    mut v_n_2968_: *mut leanh::LeanObject,
    mut v_reader_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2976_: u8 = 0;
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_array_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v_isSharedCheck_2993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2970_ = leanh::lean_ctor_get(v_reader_2969_, 1);
                v_state_2971_ = leanh::lean_ctor_get(v_reader_2969_, 0);
                v_messageHead_2972_ = leanh::lean_ctor_get(v_reader_2969_, 2);
                v_messageCount_2973_ = leanh::lean_ctor_get(v_reader_2969_, 3);
                v_bodyBytesRead_2974_ = leanh::lean_ctor_get(v_reader_2969_, 4);
                v_headerBytesRead_2975_ = leanh::lean_ctor_get(v_reader_2969_, 5);
                v_noMoreInput_2976_ = leanh::lean_ctor_get_uint8(
                    v_reader_2969_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2993_ = (!leanh::lean_is_exclusive(v_reader_2969_)) as u8;
                if v_isSharedCheck_2993_ == 0 {
                    v___x_2978_ = v_reader_2969_;
                    v_isShared_2979_ = v_isSharedCheck_2993_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_2975_);
                    leanh::lean_inc(v_bodyBytesRead_2974_);
                    leanh::lean_inc(v_messageCount_2973_);
                    leanh::lean_inc(v_messageHead_2972_);
                    leanh::lean_inc(v_input_2970_);
                    leanh::lean_inc(v_state_2971_);
                    leanh::lean_dec(v_reader_2969_);
                    v___x_2978_ = leanh::lean_box(0);
                    v_isShared_2979_ = v_isSharedCheck_2993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2980_ = leanh::lean_ctor_get(v_input_2970_, 0);
                v_idx_2981_ = leanh::lean_ctor_get(v_input_2970_, 1);
                v_isSharedCheck_2992_ = (!leanh::lean_is_exclusive(v_input_2970_)) as u8;
                if v_isSharedCheck_2992_ == 0 {
                    v___x_2983_ = v_input_2970_;
                    v_isShared_2984_ = v_isSharedCheck_2992_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_2981_);
                    leanh::lean_inc(v_array_2980_);
                    leanh::lean_dec(v_input_2970_);
                    v___x_2983_ = leanh::lean_box(0);
                    v_isShared_2984_ = v_isSharedCheck_2992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2985_ = lean_nat_add(v_idx_2981_, v_n_2968_);
                leanh::lean_dec(v_idx_2981_);
                if v_isShared_2984_ == 0 {
                    leanh::lean_ctor_set(v___x_2983_, 1, v___x_2985_);
                    v___x_2987_ = v___x_2983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_array_2980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2985_);
                    v___x_2987_ = v_reuseFailAlloc_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2979_ == 0 {
                    leanh::lean_ctor_set(v___x_2978_, 1, v___x_2987_);
                    v___x_2989_ = v___x_2978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_state_2971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_messageHead_2972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_messageCount_2973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_bodyBytesRead_2974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_headerBytesRead_2975_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2990_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_2976_,
                    );
                    v___x_2989_ = v_reuseFailAlloc_2990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance___boxed(
    mut v_dir_2994_: *mut leanh::LeanObject,
    mut v_n_2995_: *mut leanh::LeanObject,
    mut v_reader_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_2997_: u8 = 0;
    let mut v_res_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2997_ = (leanh::lean_unbox(v_dir_2994_) as u8);
    v_res_2998_ =
        l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_2997_, v_n_2995_, v_reader_2996_);
    leanh::lean_dec(v_n_2995_);
    return v_res_2998_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(
    mut v_reader_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3005_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3002_ = leanh::lean_ctor_get(v_reader_3001_, 1);
                v_messageHead_3003_ = leanh::lean_ctor_get(v_reader_3001_, 2);
                v_messageCount_3004_ = leanh::lean_ctor_get(v_reader_3001_, 3);
                v_noMoreInput_3005_ = leanh::lean_ctor_get_uint8(
                    v_reader_3001_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3014_ = (!leanh::lean_is_exclusive(v_reader_3001_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v_unused_3015_ = leanh::lean_ctor_get(v_reader_3001_, 5);
                    leanh::lean_dec(v_unused_3015_);
                    v_unused_3016_ = leanh::lean_ctor_get(v_reader_3001_, 4);
                    leanh::lean_dec(v_unused_3016_);
                    v_unused_3017_ = leanh::lean_ctor_get(v_reader_3001_, 0);
                    leanh::lean_dec(v_unused_3017_);
                    v___x_3007_ = v_reader_3001_;
                    v_isShared_3008_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_messageCount_3004_);
                    leanh::lean_inc(v_messageHead_3003_);
                    leanh::lean_inc(v_input_3002_);
                    leanh::lean_dec(v_reader_3001_);
                    v___x_3007_ = leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3009_ = leanh::lean_unsigned_to_nat(0);
                v___x_3010_ = l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0;
                if v_isShared_3008_ == 0 {
                    leanh::lean_ctor_set(v___x_3007_, 5, v___x_3009_);
                    leanh::lean_ctor_set(v___x_3007_, 4, v___x_3009_);
                    leanh::lean_ctor_set(v___x_3007_, 0, v___x_3010_);
                    v___x_3012_ = v___x_3007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_input_3002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_messageHead_3003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_messageCount_3004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 4, v___x_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 5, v___x_3009_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3013_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3005_,
                    );
                    v___x_3012_ = v_reuseFailAlloc_3013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startHeaders(
    mut v_dir_3018_: u8,
    mut v_reader_3019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3023_: u8 = 0;
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_unused_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3020_ = leanh::lean_ctor_get(v_reader_3019_, 1);
                v_messageHead_3021_ = leanh::lean_ctor_get(v_reader_3019_, 2);
                v_messageCount_3022_ = leanh::lean_ctor_get(v_reader_3019_, 3);
                v_noMoreInput_3023_ = leanh::lean_ctor_get_uint8(
                    v_reader_3019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3032_ = (!leanh::lean_is_exclusive(v_reader_3019_)) as u8;
                if v_isSharedCheck_3032_ == 0 {
                    v_unused_3033_ = leanh::lean_ctor_get(v_reader_3019_, 5);
                    leanh::lean_dec(v_unused_3033_);
                    v_unused_3034_ = leanh::lean_ctor_get(v_reader_3019_, 4);
                    leanh::lean_dec(v_unused_3034_);
                    v_unused_3035_ = leanh::lean_ctor_get(v_reader_3019_, 0);
                    leanh::lean_dec(v_unused_3035_);
                    v___x_3025_ = v_reader_3019_;
                    v_isShared_3026_ = v_isSharedCheck_3032_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_messageCount_3022_);
                    leanh::lean_inc(v_messageHead_3021_);
                    leanh::lean_inc(v_input_3020_);
                    leanh::lean_dec(v_reader_3019_);
                    v___x_3025_ = leanh::lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3027_ = leanh::lean_unsigned_to_nat(0);
                v___x_3028_ = l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0;
                if v_isShared_3026_ == 0 {
                    leanh::lean_ctor_set(v___x_3025_, 5, v___x_3027_);
                    leanh::lean_ctor_set(v___x_3025_, 4, v___x_3027_);
                    leanh::lean_ctor_set(v___x_3025_, 0, v___x_3028_);
                    v___x_3030_ = v___x_3025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_input_3020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_messageHead_3021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_messageCount_3022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 4, v___x_3027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 5, v___x_3027_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3031_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3023_,
                    );
                    v___x_3030_ = v_reuseFailAlloc_3031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(
    mut v_dir_3036_: *mut leanh::LeanObject,
    mut v_reader_3037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3038_: u8 = 0;
    let mut v_res_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3038_ = (leanh::lean_unbox(v_dir_3036_) as u8);
    v_res_3039_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_3038_, v_reader_3037_);
    return v_res_3039_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(
    mut v_n_3040_: *mut leanh::LeanObject,
    mut v_reader_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3048_: u8 = 0;
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3042_ = leanh::lean_ctor_get(v_reader_3041_, 0);
                v_input_3043_ = leanh::lean_ctor_get(v_reader_3041_, 1);
                v_messageHead_3044_ = leanh::lean_ctor_get(v_reader_3041_, 2);
                v_messageCount_3045_ = leanh::lean_ctor_get(v_reader_3041_, 3);
                v_bodyBytesRead_3046_ = leanh::lean_ctor_get(v_reader_3041_, 4);
                v_headerBytesRead_3047_ = leanh::lean_ctor_get(v_reader_3041_, 5);
                v_noMoreInput_3048_ = leanh::lean_ctor_get_uint8(
                    v_reader_3041_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3056_ = (!leanh::lean_is_exclusive(v_reader_3041_)) as u8;
                if v_isSharedCheck_3056_ == 0 {
                    v___x_3050_ = v_reader_3041_;
                    v_isShared_3051_ = v_isSharedCheck_3056_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3047_);
                    leanh::lean_inc(v_bodyBytesRead_3046_);
                    leanh::lean_inc(v_messageCount_3045_);
                    leanh::lean_inc(v_messageHead_3044_);
                    leanh::lean_inc(v_input_3043_);
                    leanh::lean_inc(v_state_3042_);
                    leanh::lean_dec(v_reader_3041_);
                    v___x_3050_ = leanh::lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3052_ = lean_nat_add(v_bodyBytesRead_3046_, v_n_3040_);
                leanh::lean_dec(v_bodyBytesRead_3046_);
                if v_isShared_3051_ == 0 {
                    leanh::lean_ctor_set(v___x_3050_, 4, v___x_3052_);
                    v___x_3054_ = v___x_3050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_state_3042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_input_3043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_messageHead_3044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_messageCount_3045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 4, v___x_3052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 5, v_headerBytesRead_3047_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3048_,
                    );
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(
    mut v_n_3057_: *mut leanh::LeanObject,
    mut v_reader_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_3057_, v_reader_3058_);
    leanh::lean_dec(v_n_3057_);
    return v_res_3059_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes(
    mut v_dir_3060_: u8,
    mut v_n_3061_: *mut leanh::LeanObject,
    mut v_reader_3062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3069_: u8 = 0;
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3063_ = leanh::lean_ctor_get(v_reader_3062_, 0);
                v_input_3064_ = leanh::lean_ctor_get(v_reader_3062_, 1);
                v_messageHead_3065_ = leanh::lean_ctor_get(v_reader_3062_, 2);
                v_messageCount_3066_ = leanh::lean_ctor_get(v_reader_3062_, 3);
                v_bodyBytesRead_3067_ = leanh::lean_ctor_get(v_reader_3062_, 4);
                v_headerBytesRead_3068_ = leanh::lean_ctor_get(v_reader_3062_, 5);
                v_noMoreInput_3069_ = leanh::lean_ctor_get_uint8(
                    v_reader_3062_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3077_ = (!leanh::lean_is_exclusive(v_reader_3062_)) as u8;
                if v_isSharedCheck_3077_ == 0 {
                    v___x_3071_ = v_reader_3062_;
                    v_isShared_3072_ = v_isSharedCheck_3077_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3068_);
                    leanh::lean_inc(v_bodyBytesRead_3067_);
                    leanh::lean_inc(v_messageCount_3066_);
                    leanh::lean_inc(v_messageHead_3065_);
                    leanh::lean_inc(v_input_3064_);
                    leanh::lean_inc(v_state_3063_);
                    leanh::lean_dec(v_reader_3062_);
                    v___x_3071_ = leanh::lean_box(0);
                    v_isShared_3072_ = v_isSharedCheck_3077_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3073_ = lean_nat_add(v_bodyBytesRead_3067_, v_n_3061_);
                leanh::lean_dec(v_bodyBytesRead_3067_);
                if v_isShared_3072_ == 0 {
                    leanh::lean_ctor_set(v___x_3071_, 4, v___x_3073_);
                    v___x_3075_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_state_3063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_input_3064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_messageHead_3065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_messageCount_3066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 5, v_headerBytesRead_3068_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3076_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3069_,
                    );
                    v___x_3075_ = v_reuseFailAlloc_3076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(
    mut v_dir_3078_: *mut leanh::LeanObject,
    mut v_n_3079_: *mut leanh::LeanObject,
    mut v_reader_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3081_ = (leanh::lean_unbox(v_dir_3078_) as u8);
    v_res_3082_ =
        l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_3081_, v_n_3079_, v_reader_3080_);
    leanh::lean_dec(v_n_3079_);
    return v_res_3082_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(
    mut v_n_3083_: *mut leanh::LeanObject,
    mut v_reader_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3091_: u8 = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3085_ = leanh::lean_ctor_get(v_reader_3084_, 0);
                v_input_3086_ = leanh::lean_ctor_get(v_reader_3084_, 1);
                v_messageHead_3087_ = leanh::lean_ctor_get(v_reader_3084_, 2);
                v_messageCount_3088_ = leanh::lean_ctor_get(v_reader_3084_, 3);
                v_bodyBytesRead_3089_ = leanh::lean_ctor_get(v_reader_3084_, 4);
                v_headerBytesRead_3090_ = leanh::lean_ctor_get(v_reader_3084_, 5);
                v_noMoreInput_3091_ = leanh::lean_ctor_get_uint8(
                    v_reader_3084_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3099_ = (!leanh::lean_is_exclusive(v_reader_3084_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3093_ = v_reader_3084_;
                    v_isShared_3094_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3090_);
                    leanh::lean_inc(v_bodyBytesRead_3089_);
                    leanh::lean_inc(v_messageCount_3088_);
                    leanh::lean_inc(v_messageHead_3087_);
                    leanh::lean_inc(v_input_3086_);
                    leanh::lean_inc(v_state_3085_);
                    leanh::lean_dec(v_reader_3084_);
                    v___x_3093_ = leanh::lean_box(0);
                    v_isShared_3094_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3095_ = lean_nat_add(v_headerBytesRead_3090_, v_n_3083_);
                leanh::lean_dec(v_headerBytesRead_3090_);
                if v_isShared_3094_ == 0 {
                    leanh::lean_ctor_set(v___x_3093_, 5, v___x_3095_);
                    v___x_3097_ = v___x_3093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_state_3085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_input_3086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_messageHead_3087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_messageCount_3088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_bodyBytesRead_3089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 5, v___x_3095_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3098_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3091_,
                    );
                    v___x_3097_ = v_reuseFailAlloc_3098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(
    mut v_n_3100_: *mut leanh::LeanObject,
    mut v_reader_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3102_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_3100_, v_reader_3101_);
    leanh::lean_dec(v_n_3100_);
    return v_res_3102_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes(
    mut v_dir_3103_: u8,
    mut v_n_3104_: *mut leanh::LeanObject,
    mut v_reader_3105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3112_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3106_ = leanh::lean_ctor_get(v_reader_3105_, 0);
                v_input_3107_ = leanh::lean_ctor_get(v_reader_3105_, 1);
                v_messageHead_3108_ = leanh::lean_ctor_get(v_reader_3105_, 2);
                v_messageCount_3109_ = leanh::lean_ctor_get(v_reader_3105_, 3);
                v_bodyBytesRead_3110_ = leanh::lean_ctor_get(v_reader_3105_, 4);
                v_headerBytesRead_3111_ = leanh::lean_ctor_get(v_reader_3105_, 5);
                v_noMoreInput_3112_ = leanh::lean_ctor_get_uint8(
                    v_reader_3105_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3120_ = (!leanh::lean_is_exclusive(v_reader_3105_)) as u8;
                if v_isSharedCheck_3120_ == 0 {
                    v___x_3114_ = v_reader_3105_;
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3111_);
                    leanh::lean_inc(v_bodyBytesRead_3110_);
                    leanh::lean_inc(v_messageCount_3109_);
                    leanh::lean_inc(v_messageHead_3108_);
                    leanh::lean_inc(v_input_3107_);
                    leanh::lean_inc(v_state_3106_);
                    leanh::lean_dec(v_reader_3105_);
                    v___x_3114_ = leanh::lean_box(0);
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3116_ = lean_nat_add(v_headerBytesRead_3111_, v_n_3104_);
                leanh::lean_dec(v_headerBytesRead_3111_);
                if v_isShared_3115_ == 0 {
                    leanh::lean_ctor_set(v___x_3114_, 5, v___x_3116_);
                    v___x_3118_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_state_3106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_input_3107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_messageHead_3108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_messageCount_3109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_bodyBytesRead_3110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 5, v___x_3116_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3119_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3112_,
                    );
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(
    mut v_dir_3121_: *mut leanh::LeanObject,
    mut v_n_3122_: *mut leanh::LeanObject,
    mut v_reader_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3124_: u8 = 0;
    let mut v_res_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3124_ = (leanh::lean_unbox(v_dir_3121_) as u8);
    v_res_3125_ =
        l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_3124_, v_n_3122_, v_reader_3123_);
    leanh::lean_dec(v_n_3122_);
    return v_res_3125_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(
    mut v_size_3126_: *mut leanh::LeanObject,
    mut v_reader_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3133_: u8 = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_unused_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3128_ = leanh::lean_ctor_get(v_reader_3127_, 1);
                v_messageHead_3129_ = leanh::lean_ctor_get(v_reader_3127_, 2);
                v_messageCount_3130_ = leanh::lean_ctor_get(v_reader_3127_, 3);
                v_bodyBytesRead_3131_ = leanh::lean_ctor_get(v_reader_3127_, 4);
                v_headerBytesRead_3132_ = leanh::lean_ctor_get(v_reader_3127_, 5);
                v_noMoreInput_3133_ = leanh::lean_ctor_get_uint8(
                    v_reader_3127_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3142_ = (!leanh::lean_is_exclusive(v_reader_3127_)) as u8;
                if v_isSharedCheck_3142_ == 0 {
                    v_unused_3143_ = leanh::lean_ctor_get(v_reader_3127_, 0);
                    leanh::lean_dec(v_unused_3143_);
                    v___x_3135_ = v_reader_3127_;
                    v_isShared_3136_ = v_isSharedCheck_3142_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3132_);
                    leanh::lean_inc(v_bodyBytesRead_3131_);
                    leanh::lean_inc(v_messageCount_3130_);
                    leanh::lean_inc(v_messageHead_3129_);
                    leanh::lean_inc(v_input_3128_);
                    leanh::lean_dec(v_reader_3127_);
                    v___x_3135_ = leanh::lean_box(0);
                    v_isShared_3136_ = v_isSharedCheck_3142_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3137_, 0, v_size_3126_);
                v___x_3138_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                if v_isShared_3136_ == 0 {
                    leanh::lean_ctor_set(v___x_3135_, 0, v___x_3138_);
                    v___x_3140_ = v___x_3135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_input_3128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_messageHead_3129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 3, v_messageCount_3130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 4, v_bodyBytesRead_3131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 5, v_headerBytesRead_3132_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3141_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3133_,
                    );
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startFixedBody(
    mut v_dir_3144_: u8,
    mut v_size_3145_: *mut leanh::LeanObject,
    mut v_reader_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3152_: u8 = 0;
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_unused_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3147_ = leanh::lean_ctor_get(v_reader_3146_, 1);
                v_messageHead_3148_ = leanh::lean_ctor_get(v_reader_3146_, 2);
                v_messageCount_3149_ = leanh::lean_ctor_get(v_reader_3146_, 3);
                v_bodyBytesRead_3150_ = leanh::lean_ctor_get(v_reader_3146_, 4);
                v_headerBytesRead_3151_ = leanh::lean_ctor_get(v_reader_3146_, 5);
                v_noMoreInput_3152_ = leanh::lean_ctor_get_uint8(
                    v_reader_3146_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3161_ = (!leanh::lean_is_exclusive(v_reader_3146_)) as u8;
                if v_isSharedCheck_3161_ == 0 {
                    v_unused_3162_ = leanh::lean_ctor_get(v_reader_3146_, 0);
                    leanh::lean_dec(v_unused_3162_);
                    v___x_3154_ = v_reader_3146_;
                    v_isShared_3155_ = v_isSharedCheck_3161_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3151_);
                    leanh::lean_inc(v_bodyBytesRead_3150_);
                    leanh::lean_inc(v_messageCount_3149_);
                    leanh::lean_inc(v_messageHead_3148_);
                    leanh::lean_inc(v_input_3147_);
                    leanh::lean_dec(v_reader_3146_);
                    v___x_3154_ = leanh::lean_box(0);
                    v_isShared_3155_ = v_isSharedCheck_3161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3156_, 0, v_size_3145_);
                v___x_3157_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                if v_isShared_3155_ == 0 {
                    leanh::lean_ctor_set(v___x_3154_, 0, v___x_3157_);
                    v___x_3159_ = v___x_3154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_input_3147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_messageHead_3148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_messageCount_3149_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_bodyBytesRead_3150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 5, v_headerBytesRead_3151_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3160_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3152_,
                    );
                    v___x_3159_ = v_reuseFailAlloc_3160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(
    mut v_dir_3163_: *mut leanh::LeanObject,
    mut v_size_3164_: *mut leanh::LeanObject,
    mut v_reader_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3166_: u8 = 0;
    let mut v_res_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3166_ = (leanh::lean_unbox(v_dir_3163_) as u8);
    v_res_3167_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(
        v_dir_boxed_3166_,
        v_size_3164_,
        v_reader_3165_,
    );
    return v_res_3167_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(
    mut v_reader_3170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3176_: u8 = 0;
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3179_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_unused_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3171_ = leanh::lean_ctor_get(v_reader_3170_, 1);
                v_messageHead_3172_ = leanh::lean_ctor_get(v_reader_3170_, 2);
                v_messageCount_3173_ = leanh::lean_ctor_get(v_reader_3170_, 3);
                v_bodyBytesRead_3174_ = leanh::lean_ctor_get(v_reader_3170_, 4);
                v_headerBytesRead_3175_ = leanh::lean_ctor_get(v_reader_3170_, 5);
                v_noMoreInput_3176_ = leanh::lean_ctor_get_uint8(
                    v_reader_3170_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3184_ = (!leanh::lean_is_exclusive(v_reader_3170_)) as u8;
                if v_isSharedCheck_3184_ == 0 {
                    v_unused_3185_ = leanh::lean_ctor_get(v_reader_3170_, 0);
                    leanh::lean_dec(v_unused_3185_);
                    v___x_3178_ = v_reader_3170_;
                    v_isShared_3179_ = v_isSharedCheck_3184_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3175_);
                    leanh::lean_inc(v_bodyBytesRead_3174_);
                    leanh::lean_inc(v_messageCount_3173_);
                    leanh::lean_inc(v_messageHead_3172_);
                    leanh::lean_inc(v_input_3171_);
                    leanh::lean_dec(v_reader_3170_);
                    v___x_3178_ = leanh::lean_box(0);
                    v_isShared_3179_ = v_isSharedCheck_3184_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3180_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0;
                if v_isShared_3179_ == 0 {
                    leanh::lean_ctor_set(v___x_3178_, 0, v___x_3180_);
                    v___x_3182_ = v___x_3178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_input_3171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_messageHead_3172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_messageCount_3173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_bodyBytesRead_3174_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_headerBytesRead_3175_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3183_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3176_,
                    );
                    v___x_3182_ = v_reuseFailAlloc_3183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startChunkedBody(
    mut v_dir_3186_: u8,
    mut v_reader_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_input_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3193_: u8 = 0;
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3201_: u8 = 0;
    let mut v_unused_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3188_ = leanh::lean_ctor_get(v_reader_3187_, 1);
                v_messageHead_3189_ = leanh::lean_ctor_get(v_reader_3187_, 2);
                v_messageCount_3190_ = leanh::lean_ctor_get(v_reader_3187_, 3);
                v_bodyBytesRead_3191_ = leanh::lean_ctor_get(v_reader_3187_, 4);
                v_headerBytesRead_3192_ = leanh::lean_ctor_get(v_reader_3187_, 5);
                v_noMoreInput_3193_ = leanh::lean_ctor_get_uint8(
                    v_reader_3187_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3201_ = (!leanh::lean_is_exclusive(v_reader_3187_)) as u8;
                if v_isSharedCheck_3201_ == 0 {
                    v_unused_3202_ = leanh::lean_ctor_get(v_reader_3187_, 0);
                    leanh::lean_dec(v_unused_3202_);
                    v___x_3195_ = v_reader_3187_;
                    v_isShared_3196_ = v_isSharedCheck_3201_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3192_);
                    leanh::lean_inc(v_bodyBytesRead_3191_);
                    leanh::lean_inc(v_messageCount_3190_);
                    leanh::lean_inc(v_messageHead_3189_);
                    leanh::lean_inc(v_input_3188_);
                    leanh::lean_dec(v_reader_3187_);
                    v___x_3195_ = leanh::lean_box(0);
                    v_isShared_3196_ = v_isSharedCheck_3201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3197_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0;
                if v_isShared_3196_ == 0 {
                    leanh::lean_ctor_set(v___x_3195_, 0, v___x_3197_);
                    v___x_3199_ = v___x_3195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_input_3188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_messageHead_3189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_messageCount_3190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 4, v_bodyBytesRead_3191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 5, v_headerBytesRead_3192_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3200_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_noMoreInput_3193_,
                    );
                    v___x_3199_ = v_reuseFailAlloc_3200_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(
    mut v_dir_3203_: *mut leanh::LeanObject,
    mut v_reader_3204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3205_: u8 = 0;
    let mut v_res_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3205_ = (leanh::lean_unbox(v_dir_3203_) as u8);
    v_res_3206_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_3205_, v_reader_3204_);
    return v_res_3206_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(
    mut v_reader_3207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3208_ = leanh::lean_ctor_get(v_reader_3207_, 0);
                v_input_3209_ = leanh::lean_ctor_get(v_reader_3207_, 1);
                v_messageHead_3210_ = leanh::lean_ctor_get(v_reader_3207_, 2);
                v_messageCount_3211_ = leanh::lean_ctor_get(v_reader_3207_, 3);
                v_bodyBytesRead_3212_ = leanh::lean_ctor_get(v_reader_3207_, 4);
                v_headerBytesRead_3213_ = leanh::lean_ctor_get(v_reader_3207_, 5);
                v_isSharedCheck_3221_ = (!leanh::lean_is_exclusive(v_reader_3207_)) as u8;
                if v_isSharedCheck_3221_ == 0 {
                    v___x_3215_ = v_reader_3207_;
                    v_isShared_3216_ = v_isSharedCheck_3221_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3213_);
                    leanh::lean_inc(v_bodyBytesRead_3212_);
                    leanh::lean_inc(v_messageCount_3211_);
                    leanh::lean_inc(v_messageHead_3210_);
                    leanh::lean_inc(v_input_3209_);
                    leanh::lean_inc(v_state_3208_);
                    leanh::lean_dec(v_reader_3207_);
                    v___x_3215_ = leanh::lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3217_ = 1;
                if v_isShared_3216_ == 0 {
                    v___x_3219_ = v___x_3215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3220_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_state_3208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_input_3209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_messageHead_3210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_messageCount_3211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_bodyBytesRead_3212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 5, v_headerBytesRead_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3219_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_3217_,
                );
                return v___x_3219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markNoMoreInput(
    mut v_dir_3222_: u8,
    mut v_reader_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3224_ = leanh::lean_ctor_get(v_reader_3223_, 0);
                v_input_3225_ = leanh::lean_ctor_get(v_reader_3223_, 1);
                v_messageHead_3226_ = leanh::lean_ctor_get(v_reader_3223_, 2);
                v_messageCount_3227_ = leanh::lean_ctor_get(v_reader_3223_, 3);
                v_bodyBytesRead_3228_ = leanh::lean_ctor_get(v_reader_3223_, 4);
                v_headerBytesRead_3229_ = leanh::lean_ctor_get(v_reader_3223_, 5);
                v_isSharedCheck_3237_ = (!leanh::lean_is_exclusive(v_reader_3223_)) as u8;
                if v_isSharedCheck_3237_ == 0 {
                    v___x_3231_ = v_reader_3223_;
                    v_isShared_3232_ = v_isSharedCheck_3237_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_headerBytesRead_3229_);
                    leanh::lean_inc(v_bodyBytesRead_3228_);
                    leanh::lean_inc(v_messageCount_3227_);
                    leanh::lean_inc(v_messageHead_3226_);
                    leanh::lean_inc(v_input_3225_);
                    leanh::lean_inc(v_state_3224_);
                    leanh::lean_dec(v_reader_3223_);
                    v___x_3231_ = leanh::lean_box(0);
                    v_isShared_3232_ = v_isSharedCheck_3237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3233_ = 1;
                if v_isShared_3232_ == 0 {
                    v___x_3235_ = v___x_3231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_state_3224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_input_3225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_messageHead_3226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_messageCount_3227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_bodyBytesRead_3228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 5, v_headerBytesRead_3229_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_3233_,
                );
                return v___x_3235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(
    mut v_dir_3238_: *mut leanh::LeanObject,
    mut v_reader_3239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3240_: u8 = 0;
    let mut v_res_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3240_ = (leanh::lean_unbox(v_dir_3238_) as u8);
    v_res_3241_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_3240_, v_reader_3239_);
    return v_res_3241_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(
    mut v_dir_3242_: u8,
    mut v_reader_3243_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_messageHead_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    v_messageHead_3244_ = leanh::lean_ctor_get(v_reader_3243_, 2);
    v___x_3245_ =
        l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_3242_, v_messageHead_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(
    mut v_dir_3246_: *mut leanh::LeanObject,
    mut v_reader_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_3248_: u8 = 0;
    let mut v_res_3249_: u8 = 0;
    let mut v_r_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3248_ = (leanh::lean_unbox(v_dir_3246_) as u8);
    v_res_3249_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_3248_, v_reader_3247_);
    leanh::lean_dec_ref(v_reader_3247_);
    v_r_3250_ = leanh::lean_box((v_res_3249_) as usize);
    return v_r_3250_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Reader(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Reader(
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
pub unsafe fn initialize_Std_Http_Protocol_H1_Reader(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Error(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Reader(builtin);
}