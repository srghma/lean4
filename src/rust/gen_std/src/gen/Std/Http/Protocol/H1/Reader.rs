// Lean compiler output
// Module: Std.Http.Protocol.H1.Reader
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message Std.Http.Protocol.H1.Error
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
use crate::ffi::lean_byte_array_copy_slice;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_sub,
};
pub static l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value
)
    as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instReprBodyState: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_Reader_instBEqBodyState: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value:
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
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value:
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
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value:
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
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value:
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
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value:
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
            l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value:
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
static mut l_Std_Http_Protocol_H1_Reader_addHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value:
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
static mut l_Std_Http_Protocol_H1_Reader_addHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value:
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
static mut l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(
    mut v_x_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1626_) {
        0 => {
            let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1627_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1627_;
        }
        1 => {
            let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1628_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1628_;
        }
        2 => {
            let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1629_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1629_;
        }
        _ => {
            let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1630_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1630_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___boxed(
    mut v_x_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(v_x_1631_);
    crate::leanh::lean_dec(v_x_1631_);
    return v_res_1632_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
    mut v_t_1633_: *mut crate::leanh::LeanObject,
    mut v_k_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1633_) {
        0 => {
            let mut v_remaining_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_remaining_1635_ = crate::leanh::lean_ctor_get(v_t_1633_, 0);
            crate::leanh::lean_inc(v_remaining_1635_);
            crate::leanh::lean_dec_ref_known(v_t_1633_, 1);
            v___x_1636_ = crate::leanh::lean_apply_1(v_k_1634_, v_remaining_1635_);
            return v___x_1636_;
        }
        2 => {
            let mut v_ext_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_remaining_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ext_1637_ = crate::leanh::lean_ctor_get(v_t_1633_, 0);
            crate::leanh::lean_inc_ref(v_ext_1637_);
            v_remaining_1638_ = crate::leanh::lean_ctor_get(v_t_1633_, 1);
            crate::leanh::lean_inc(v_remaining_1638_);
            crate::leanh::lean_dec_ref_known(v_t_1633_, 2);
            v___x_1639_ = crate::leanh::lean_apply_2(v_k_1634_, v_ext_1637_, v_remaining_1638_);
            return v___x_1639_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_1633_);
            return v_k_1634_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(
    mut v_motive_1640_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1641_: *mut crate::leanh::LeanObject,
    mut v_t_1642_: *mut crate::leanh::LeanObject,
    mut v_h_1643_: *mut crate::leanh::LeanObject,
    mut v_k_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1642_, v_k_1644_);
    return v___x_1645_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(
    mut v_motive_1646_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1647_: *mut crate::leanh::LeanObject,
    mut v_t_1648_: *mut crate::leanh::LeanObject,
    mut v_h_1649_: *mut crate::leanh::LeanObject,
    mut v_k_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(
        v_motive_1646_,
        v_ctorIdx_1647_,
        v_t_1648_,
        v_h_1649_,
        v_k_1650_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1647_);
    return v_res_1651_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(
    mut v_t_1652_: *mut crate::leanh::LeanObject,
    mut v_fixed_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1652_, v_fixed_1653_);
    return v___x_1654_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(
    mut v_motive_1655_: *mut crate::leanh::LeanObject,
    mut v_t_1656_: *mut crate::leanh::LeanObject,
    mut v_h_1657_: *mut crate::leanh::LeanObject,
    mut v_fixed_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1656_, v_fixed_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(
    mut v_t_1660_: *mut crate::leanh::LeanObject,
    mut v_chunkedSize_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1660_, v_chunkedSize_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(
    mut v_motive_1663_: *mut crate::leanh::LeanObject,
    mut v_t_1664_: *mut crate::leanh::LeanObject,
    mut v_h_1665_: *mut crate::leanh::LeanObject,
    mut v_chunkedSize_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1664_, v_chunkedSize_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(
    mut v_t_1668_: *mut crate::leanh::LeanObject,
    mut v_chunkedBody_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1668_, v_chunkedBody_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(
    mut v_motive_1671_: *mut crate::leanh::LeanObject,
    mut v_t_1672_: *mut crate::leanh::LeanObject,
    mut v_h_1673_: *mut crate::leanh::LeanObject,
    mut v_chunkedBody_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ =
        l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_1672_, v_chunkedBody_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(
    mut v_t_1676_: *mut crate::leanh::LeanObject,
    mut v_closeDelimited_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
        v_t_1676_,
        v_closeDelimited_1677_,
    );
    return v___x_1678_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(
    mut v_motive_1679_: *mut crate::leanh::LeanObject,
    mut v_t_1680_: *mut crate::leanh::LeanObject,
    mut v_h_1681_: *mut crate::leanh::LeanObject,
    mut v_closeDelimited_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(
        v_t_1680_,
        v_closeDelimited_1682_,
    );
    return v___x_1683_;
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(
    mut v_x_1694_: *mut crate::leanh::LeanObject,
    mut v_x_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1694_) == 0 {
        let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1696_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1;
        return v___x_1696_;
    } else {
        let mut v_val_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1697_ = crate::leanh::lean_ctor_get(v_x_1694_, 0);
        crate::leanh::lean_inc(v_val_1697_);
        crate::leanh::lean_dec_ref_known(v_x_1694_, 1);
        v___x_1698_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3;
        v___x_1699_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_val_1697_);
        v___x_1700_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1700_, 0, v___x_1698_);
        crate::leanh::lean_ctor_set(v___x_1700_, 1, v___x_1699_);
        v___x_1701_ = l_Repr_addAppParen(v___x_1700_, v_x_1695_);
        return v___x_1701_;
    }
}
pub unsafe fn l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(
    mut v_x_1702_: *mut crate::leanh::LeanObject,
    mut v_x_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_x_1702_, v_x_1703_);
    crate::leanh::lean_dec(v_x_1703_);
    return v_res_1704_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_x_1705_: *mut crate::leanh::LeanObject,
    mut v_x_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1707_) == 0 {
                    crate::leanh::lean_dec(v_x_1705_);
                    return v_x_1706_;
                } else {
                    v_head_1708_ = crate::leanh::lean_ctor_get(v_x_1707_, 0);
                    v_tail_1709_ = crate::leanh::lean_ctor_get(v_x_1707_, 1);
                    v_isSharedCheck_1718_ = (!crate::leanh::lean_is_exclusive(v_x_1707_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1711_ = v_x_1707_;
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1709_);
                        crate::leanh::lean_inc(v_head_1708_);
                        crate::leanh::lean_dec(v_x_1707_);
                        v___x_1711_ = crate::leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1705_);
                if v_isShared_1712_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1711_, 5);
                    crate::leanh::lean_ctor_set(v___x_1711_, 1, v_x_1705_);
                    crate::leanh::lean_ctor_set(v___x_1711_, 0, v_x_1706_);
                    v___x_1714_ = v___x_1711_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_x_1706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_x_1705_);
                    v___x_1714_ = v_reuseFailAlloc_1717_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1715_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                crate::leanh::lean_ctor_set(v___x_1715_, 1, v_head_1708_);
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
    mut v_x_1719_: *mut crate::leanh::LeanObject,
    mut v_x_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1719_) == 0 {
        let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1720_);
        v___x_1721_ = crate::leanh::lean_box(0);
        return v___x_1721_;
    } else {
        let mut v_tail_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1722_ = crate::leanh::lean_ctor_get(v_x_1719_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1722_) == 0 {
            let mut v_head_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1720_);
            v_head_1723_ = crate::leanh::lean_ctor_get(v_x_1719_, 0);
            crate::leanh::lean_inc(v_head_1723_);
            crate::leanh::lean_dec_ref_known(v_x_1719_, 2);
            return v_head_1723_;
        } else {
            let mut v_head_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1722_);
            v_head_1724_ = crate::leanh::lean_ctor_get(v_x_1719_, 0);
            crate::leanh::lean_inc(v_head_1724_);
            crate::leanh::lean_dec_ref_known(v_x_1719_, 2);
            v___x_1725_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(v_x_1720_, v_head_1724_, v_tail_1722_);
            return v___x_1725_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0;
    v___x_1735_ = lean_string_length(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5);
    v___x_1737_ = lean_nat_to_int(v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(
    mut v_x_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1743_ = crate::leanh::lean_ctor_get(v_x_1742_, 0);
                v_snd_1744_ = crate::leanh::lean_ctor_get(v_x_1742_, 1);
                v_isSharedCheck_1767_ = (!crate::leanh::lean_is_exclusive(v_x_1742_)) as u8;
                if v_isSharedCheck_1767_ == 0 {
                    v___x_1746_ = v_x_1742_;
                    v_isShared_1747_ = v_isSharedCheck_1767_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1744_);
                    crate::leanh::lean_inc(v_fst_1743_);
                    crate::leanh::lean_dec(v_x_1742_);
                    v___x_1746_ = crate::leanh::lean_box(0);
                    v_isShared_1747_ = v_isSharedCheck_1767_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1748_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1749_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_fst_1743_);
                v___x_1750_ = crate::leanh::lean_box(0);
                if v_isShared_1747_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1746_, 1);
                    crate::leanh::lean_ctor_set(v___x_1746_, 1, v___x_1750_);
                    crate::leanh::lean_ctor_set(v___x_1746_, 0, v___x_1749_);
                    v___x_1752_ = v___x_1746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1753_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_snd_1744_, v___x_1748_);
                v___x_1754_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1754_, 1, v___x_1752_);
                v___x_1755_ = l_List_reverse___redArg(v___x_1754_);
                v___x_1756_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3;
                v___x_1757_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(v___x_1755_, v___x_1756_);
                v___x_1758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once), _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6);
                v___x_1759_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7;
                v___x_1760_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1759_);
                crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1757_);
                v___x_1761_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8;
                v___x_1762_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1760_);
                crate::leanh::lean_ctor_set(v___x_1762_, 1, v___x_1761_);
                v___x_1763_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1758_);
                crate::leanh::lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                v___x_1764_ = 0;
                v___x_1765_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1765_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1764_,
                );
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(
    mut v_x_1768_: *mut crate::leanh::LeanObject,
    mut v_x_1769_: *mut crate::leanh::LeanObject,
    mut v_x_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1770_) == 0 {
                    crate::leanh::lean_dec(v_x_1768_);
                    return v_x_1769_;
                } else {
                    v_head_1771_ = crate::leanh::lean_ctor_get(v_x_1770_, 0);
                    v_tail_1772_ = crate::leanh::lean_ctor_get(v_x_1770_, 1);
                    v_isSharedCheck_1782_ = (!crate::leanh::lean_is_exclusive(v_x_1770_)) as u8;
                    if v_isSharedCheck_1782_ == 0 {
                        v___x_1774_ = v_x_1770_;
                        v_isShared_1775_ = v_isSharedCheck_1782_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1772_);
                        crate::leanh::lean_inc(v_head_1771_);
                        crate::leanh::lean_dec(v_x_1770_);
                        v___x_1774_ = crate::leanh::lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1782_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1768_);
                if v_isShared_1775_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1774_, 5);
                    crate::leanh::lean_ctor_set(v___x_1774_, 1, v_x_1768_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 0, v_x_1769_);
                    v___x_1777_ = v___x_1774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_x_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_x_1768_);
                    v___x_1777_ = v_reuseFailAlloc_1781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1778_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1771_);
                v___x_1779_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1777_);
                crate::leanh::lean_ctor_set(v___x_1779_, 1, v___x_1778_);
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
    mut v_x_1783_: *mut crate::leanh::LeanObject,
    mut v_x_1784_: *mut crate::leanh::LeanObject,
    mut v_x_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1785_) == 0 {
                    crate::leanh::lean_dec(v_x_1783_);
                    return v_x_1784_;
                } else {
                    v_head_1786_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    v_tail_1787_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    v_isSharedCheck_1797_ = (!crate::leanh::lean_is_exclusive(v_x_1785_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1789_ = v_x_1785_;
                        v_isShared_1790_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1787_);
                        crate::leanh::lean_inc(v_head_1786_);
                        crate::leanh::lean_dec(v_x_1785_);
                        v___x_1789_ = crate::leanh::lean_box(0);
                        v_isShared_1790_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1783_);
                if v_isShared_1790_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1789_, 5);
                    crate::leanh::lean_ctor_set(v___x_1789_, 1, v_x_1783_);
                    crate::leanh::lean_ctor_set(v___x_1789_, 0, v_x_1784_);
                    v___x_1792_ = v___x_1789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_x_1784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_x_1783_);
                    v___x_1792_ = v_reuseFailAlloc_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1793_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1786_);
                v___x_1794_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1792_);
                crate::leanh::lean_ctor_set(v___x_1794_, 1, v___x_1793_);
                v___x_1795_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(v_x_1783_, v___x_1794_, v_tail_1787_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(
    mut v_x_1798_: *mut crate::leanh::LeanObject,
    mut v_x_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1798_) == 0 {
        let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1799_);
        v___x_1800_ = crate::leanh::lean_box(0);
        return v___x_1800_;
    } else {
        let mut v_tail_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1801_ = crate::leanh::lean_ctor_get(v_x_1798_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1801_) == 0 {
            let mut v_head_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1799_);
            v_head_1802_ = crate::leanh::lean_ctor_get(v_x_1798_, 0);
            crate::leanh::lean_inc(v_head_1802_);
            crate::leanh::lean_dec_ref_known(v_x_1798_, 2);
            v___x_1803_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1802_);
            return v___x_1803_;
        } else {
            let mut v_head_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1801_);
            v_head_1804_ = crate::leanh::lean_ctor_get(v_x_1798_, 0);
            crate::leanh::lean_inc(v_head_1804_);
            crate::leanh::lean_dec_ref_known(v_x_1798_, 2);
            v___x_1805_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_1804_);
            v___x_1806_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(v_x_1799_, v___x_1805_, v_tail_1801_);
            return v___x_1806_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0;
    v___x_1810_ = lean_string_length(v___x_1809_);
    return v___x_1810_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2);
    v___x_1812_ = lean_nat_to_int(v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(
    mut v_xs_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    v___x_1821_ = lean_array_get_size(v_xs_1820_);
    v___x_1822_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1823_ = lean_nat_dec_eq(v___x_1821_, v___x_1822_);
    if v___x_1823_ == 0 {
        let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1824_ = lean_array_to_list(v_xs_1820_);
        v___x_1825_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3;
        v___x_1826_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(v___x_1824_, v___x_1825_);
        v___x_1827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once), _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3);
        v___x_1828_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4;
        v___x_1829_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1828_);
        crate::leanh::lean_ctor_set(v___x_1829_, 1, v___x_1826_);
        v___x_1830_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5;
        v___x_1831_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1831_, 0, v___x_1829_);
        crate::leanh::lean_ctor_set(v___x_1831_, 1, v___x_1830_);
        v___x_1832_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1832_, 0, v___x_1827_);
        crate::leanh::lean_ctor_set(v___x_1832_, 1, v___x_1831_);
        v___x_1833_ = l_Std_Format_fill(v___x_1832_);
        return v___x_1833_;
    } else {
        let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1820_);
        v___x_1834_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7;
        return v___x_1834_;
    }
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1848_ = lean_nat_to_int(v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1850_ = lean_nat_to_int(v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_prec_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1857_) {
                0 => {
                    v_remaining_1873_ = crate::leanh::lean_ctor_get(v_x_1857_, 0);
                    v_isSharedCheck_1893_ = (!crate::leanh::lean_is_exclusive(v_x_1857_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1875_ = v_x_1857_;
                        v_isShared_1876_ = v_isSharedCheck_1893_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_remaining_1873_);
                        crate::leanh::lean_dec(v_x_1857_);
                        v___x_1875_ = crate::leanh::lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1893_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v___x_1894_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1895_ = lean_nat_dec_le(v___x_1894_, v_prec_1858_);
                    if v___x_1895_ == 0 {
                        v___x_1896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_1860_ = v___x_1896_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_1860_ = v___x_1897_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ext_1898_ = crate::leanh::lean_ctor_get(v_x_1857_, 0);
                    v_remaining_1899_ = crate::leanh::lean_ctor_get(v_x_1857_, 1);
                    v_isSharedCheck_1923_ = (!crate::leanh::lean_is_exclusive(v_x_1857_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1901_ = v_x_1857_;
                        v_isShared_1902_ = v_isSharedCheck_1923_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_remaining_1899_);
                        crate::leanh::lean_inc(v_ext_1898_);
                        crate::leanh::lean_dec(v_x_1857_);
                        v___x_1901_ = crate::leanh::lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1923_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v___x_1924_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1925_ = lean_nat_dec_le(v___x_1924_, v_prec_1858_);
                    if v___x_1925_ == 0 {
                        v___x_1926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_1867_ = v___x_1926_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_1867_ = v___x_1927_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1861_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1;
                crate::leanh::lean_inc(v___y_1860_);
                v___x_1862_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1862_, 0, v___y_1860_);
                crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
                v___x_1863_ = 0;
                v___x_1864_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1862_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1864_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1863_,
                );
                v___x_1865_ = l_Repr_addAppParen(v___x_1864_, v_prec_1858_);
                return v___x_1865_;
            }
            2 => {
                v___x_1868_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3;
                crate::leanh::lean_inc(v___y_1867_);
                v___x_1869_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1869_, 0, v___y_1867_);
                crate::leanh::lean_ctor_set(v___x_1869_, 1, v___x_1868_);
                v___x_1870_ = 0;
                v___x_1871_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1869_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1870_,
                );
                v___x_1872_ = l_Repr_addAppParen(v___x_1871_, v_prec_1858_);
                return v___x_1872_;
            }
            3 => {
                v___x_1889_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1890_ = lean_nat_dec_le(v___x_1889_, v_prec_1858_);
                if v___x_1890_ == 0 {
                    v___x_1891_ = crate::leanh::lean_obj_once(
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
                    v___x_1892_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_1875_, 3);
                    crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1880_);
                    v___x_1882_ = v___x_1875_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1888_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1880_);
                    v___x_1882_ = v_reuseFailAlloc_1888_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1883_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1883_, 0, v___x_1879_);
                crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                crate::leanh::lean_inc(v___y_1878_);
                v___x_1884_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1884_, 0, v___y_1878_);
                crate::leanh::lean_ctor_set(v___x_1884_, 1, v___x_1883_);
                v___x_1885_ = 0;
                v___x_1886_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1884_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1886_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1885_,
                );
                v___x_1887_ = l_Repr_addAppParen(v___x_1886_, v_prec_1858_);
                return v___x_1887_;
            }
            6 => {
                v___x_1919_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1920_ = lean_nat_dec_le(v___x_1919_, v_prec_1858_);
                if v___x_1920_ == 0 {
                    v___x_1921_ = crate::leanh::lean_obj_once(
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
                    v___x_1922_ = crate::leanh::lean_obj_once(
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
                v___x_1905_ = crate::leanh::lean_box(1);
                v___x_1906_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11;
                v___x_1907_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_1898_);
                if v_isShared_1902_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1901_, 5);
                    crate::leanh::lean_ctor_set(v___x_1901_, 1, v___x_1907_);
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1906_);
                    v___x_1909_ = v___x_1901_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1907_);
                    v___x_1909_ = v_reuseFailAlloc_1918_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1910_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
                crate::leanh::lean_ctor_set(v___x_1910_, 1, v___x_1905_);
                v___x_1911_ = l_Nat_reprFast(v_remaining_1899_);
                v___x_1912_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1912_, 0, v___x_1911_);
                v___x_1913_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1910_);
                crate::leanh::lean_ctor_set(v___x_1913_, 1, v___x_1912_);
                crate::leanh::lean_inc(v___y_1904_);
                v___x_1914_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1914_, 0, v___y_1904_);
                crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                v___x_1915_ = 0;
                v___x_1916_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1914_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1916_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1928_: *mut crate::leanh::LeanObject,
    mut v_prec_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_x_1928_, v_prec_1929_);
    crate::leanh::lean_dec(v_prec_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(
    mut v_a_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_nat_to_int(v_a_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
    mut v_x_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_x_1933_);
    return v___x_1935_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(
    mut v_x_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(v_x_1936_, v_x_1937_);
    crate::leanh::lean_dec(v_x_1937_);
    return v_res_1938_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(
    mut v_x_1941_: *mut crate::leanh::LeanObject,
    mut v_x_1942_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1941_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1942_) == 0 {
            let mut v___x_1943_: u8 = 0;
            v___x_1943_ = 1;
            return v___x_1943_;
        } else {
            let mut v___x_1944_: u8 = 0;
            v___x_1944_ = 0;
            return v___x_1944_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1942_) == 0 {
            let mut v___x_1945_: u8 = 0;
            v___x_1945_ = 0;
            return v___x_1945_;
        } else {
            let mut v_val_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1948_: u8 = 0;
            v_val_1946_ = crate::leanh::lean_ctor_get(v_x_1941_, 0);
            v_val_1947_ = crate::leanh::lean_ctor_get(v_x_1942_, 0);
            v___x_1948_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_val_1946_, v_val_1947_);
            return v___x_1948_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1951_: u8 = 0;
    let mut v_r_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ =
        l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(
            v_x_1949_, v_x_1950_,
        );
    crate::leanh::lean_dec(v_x_1950_);
    crate::leanh::lean_dec(v_x_1949_);
    v_r_1952_ = crate::leanh::lean_box((v_res_1951_) as usize);
    return v_r_1952_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
    mut v_xs_1953_: *mut crate::leanh::LeanObject,
    mut v_ys_1954_: *mut crate::leanh::LeanObject,
    mut v_x_1955_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1957_: u8 = 0;
    let mut v_one_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1956_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1957_ = lean_nat_dec_eq(v_x_1955_, v_zero_1956_);
                if v_isZero_1957_ == 1 {
                    crate::leanh::lean_dec(v_x_1955_);
                    return v_isZero_1957_;
                } else {
                    v_one_1958_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1959_ = lean_nat_sub(v_x_1955_, v_one_1958_);
                    crate::leanh::lean_dec(v_x_1955_);
                    v___x_1963_ = lean_array_fget_borrowed(v_xs_1953_, v_n_1959_);
                    v_fst_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                    v_snd_1965_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                    v___x_1966_ = lean_array_fget_borrowed(v_ys_1954_, v_n_1959_);
                    v_fst_1967_ = crate::leanh::lean_ctor_get(v___x_1966_, 0);
                    v_snd_1968_ = crate::leanh::lean_ctor_get(v___x_1966_, 1);
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
                    crate::leanh::lean_dec(v_n_1959_);
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
    mut v_xs_1971_: *mut crate::leanh::LeanObject,
    mut v_ys_1972_: *mut crate::leanh::LeanObject,
    mut v_x_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1974_: u8 = 0;
    let mut v_r_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1974_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
            v_xs_1971_, v_ys_1972_, v_x_1973_,
        );
    crate::leanh::lean_dec_ref(v_ys_1972_);
    crate::leanh::lean_dec_ref(v_xs_1971_);
    v_r_1975_ = crate::leanh::lean_box((v_res_1974_) as usize);
    return v_r_1975_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(
    mut v_x_1976_: *mut crate::leanh::LeanObject,
    mut v_x_1977_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1976_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_1977_) == 0 {
                let mut v_remaining_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1980_: u8 = 0;
                v_remaining_1978_ = crate::leanh::lean_ctor_get(v_x_1976_, 0);
                v_remaining_1979_ = crate::leanh::lean_ctor_get(v_x_1977_, 0);
                v___x_1980_ = lean_nat_dec_eq(v_remaining_1978_, v_remaining_1979_);
                return v___x_1980_;
            } else {
                let mut v___x_1981_: u8 = 0;
                v___x_1981_ = 0;
                return v___x_1981_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_1977_) == 1 {
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
            if crate::leanh::lean_obj_tag(v_x_1977_) == 2 {
                let mut v_ext_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ext_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_remaining_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1990_: u8 = 0;
                v_ext_1984_ = crate::leanh::lean_ctor_get(v_x_1976_, 0);
                v_remaining_1985_ = crate::leanh::lean_ctor_get(v_x_1976_, 1);
                v_ext_1986_ = crate::leanh::lean_ctor_get(v_x_1977_, 0);
                v_remaining_1987_ = crate::leanh::lean_ctor_get(v_x_1977_, 1);
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
            if crate::leanh::lean_obj_tag(v_x_1977_) == 3 {
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
    mut v_x_1996_: *mut crate::leanh::LeanObject,
    mut v_x_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1998_: u8 = 0;
    let mut v_r_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_1996_, v_x_1997_);
    crate::leanh::lean_dec(v_x_1997_);
    crate::leanh::lean_dec(v_x_1996_);
    v_r_1999_ = crate::leanh::lean_box((v_res_1998_) as usize);
    return v_r_1999_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(
    mut v_xs_2000_: *mut crate::leanh::LeanObject,
    mut v_ys_2001_: *mut crate::leanh::LeanObject,
    mut v_hsz_2002_: *mut crate::leanh::LeanObject,
    mut v_x_2003_: *mut crate::leanh::LeanObject,
    mut v_x_2004_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2005_: u8 = 0;
    v___x_2005_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(
            v_xs_2000_, v_ys_2001_, v_x_2003_,
        );
    return v___x_2005_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(
    mut v_xs_2006_: *mut crate::leanh::LeanObject,
    mut v_ys_2007_: *mut crate::leanh::LeanObject,
    mut v_hsz_2008_: *mut crate::leanh::LeanObject,
    mut v_x_2009_: *mut crate::leanh::LeanObject,
    mut v_x_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2011_: u8 = 0;
    let mut v_r_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ =
        l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(
            v_xs_2006_,
            v_ys_2007_,
            v_hsz_2008_,
            v_x_2009_,
            v_x_2010_,
        );
    crate::leanh::lean_dec_ref(v_ys_2007_);
    crate::leanh::lean_dec_ref(v_xs_2006_);
    v_r_2012_ = crate::leanh::lean_box((v_res_2011_) as usize);
    return v_r_2012_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(
    mut v_x_2015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2015_) {
        0 => {
            let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2016_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2016_;
        }
        1 => {
            let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2017_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2017_;
        }
        2 => {
            let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2018_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2018_;
        }
        3 => {
            let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2019_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2019_;
        }
        4 => {
            let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2020_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2020_;
        }
        5 => {
            let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2021_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2021_;
        }
        6 => {
            let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2022_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_2022_;
        }
        _ => {
            let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2023_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_2023_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg___boxed(
    mut v_x_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_2024_);
    crate::leanh::lean_dec(v_x_2024_);
    return v_res_2025_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx(
    mut v_dir_2026_: u8,
    mut v_x_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_2027_);
    return v___x_2028_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorIdx___boxed(
    mut v_dir_2029_: *mut crate::leanh::LeanObject,
    mut v_x_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2031_: u8 = 0;
    let mut v_res_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2031_ = (crate::leanh::lean_unbox(v_dir_2029_) as u8);
    v_res_2032_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx(v_dir_boxed_2031_, v_x_2030_);
    crate::leanh::lean_dec(v_x_2030_);
    return v_res_2032_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(
    mut v_t_2033_: *mut crate::leanh::LeanObject,
    mut v_k_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2033_) {
        1 => {
            let mut v_a_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2035_ = crate::leanh::lean_ctor_get(v_t_2033_, 0);
            crate::leanh::lean_inc(v_a_2035_);
            crate::leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2036_ = crate::leanh::lean_apply_1(v_k_2034_, v_a_2035_);
            return v___x_2036_;
        }
        2 => {
            let mut v_a_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2037_ = crate::leanh::lean_ctor_get(v_t_2033_, 0);
            crate::leanh::lean_inc(v_a_2037_);
            crate::leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2038_ = crate::leanh::lean_apply_1(v_k_2034_, v_a_2037_);
            return v___x_2038_;
        }
        3 => {
            let mut v_a_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2039_ = crate::leanh::lean_ctor_get(v_t_2033_, 0);
            crate::leanh::lean_inc(v_a_2039_);
            crate::leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2040_ = crate::leanh::lean_apply_1(v_k_2034_, v_a_2039_);
            return v___x_2040_;
        }
        7 => {
            let mut v_error_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_error_2041_ = crate::leanh::lean_ctor_get(v_t_2033_, 0);
            crate::leanh::lean_inc(v_error_2041_);
            crate::leanh::lean_dec_ref_known(v_t_2033_, 1);
            v___x_2042_ = crate::leanh::lean_apply_1(v_k_2034_, v_error_2041_);
            return v___x_2042_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_2033_);
            return v_k_2034_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim(
    mut v_dir_2043_: u8,
    mut v_motive_2044_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2045_: *mut crate::leanh::LeanObject,
    mut v_t_2046_: *mut crate::leanh::LeanObject,
    mut v_h_2047_: *mut crate::leanh::LeanObject,
    mut v_k_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2046_, v_k_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(
    mut v_dir_2050_: *mut crate::leanh::LeanObject,
    mut v_motive_2051_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2052_: *mut crate::leanh::LeanObject,
    mut v_t_2053_: *mut crate::leanh::LeanObject,
    mut v_h_2054_: *mut crate::leanh::LeanObject,
    mut v_k_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2056_: u8 = 0;
    let mut v_res_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2056_ = (crate::leanh::lean_unbox(v_dir_2050_) as u8);
    v_res_2057_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(
        v_dir_boxed_2056_,
        v_motive_2051_,
        v_ctorIdx_2052_,
        v_t_2053_,
        v_h_2054_,
        v_k_2055_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2052_);
    return v_res_2057_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(
    mut v_t_2058_: *mut crate::leanh::LeanObject,
    mut v_needStartLine_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2058_, v_needStartLine_2059_);
    return v___x_2060_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(
    mut v_dir_2061_: u8,
    mut v_motive_2062_: *mut crate::leanh::LeanObject,
    mut v_t_2063_: *mut crate::leanh::LeanObject,
    mut v_h_2064_: *mut crate::leanh::LeanObject,
    mut v_needStartLine_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2063_, v_needStartLine_2065_);
    return v___x_2066_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(
    mut v_dir_2067_: *mut crate::leanh::LeanObject,
    mut v_motive_2068_: *mut crate::leanh::LeanObject,
    mut v_t_2069_: *mut crate::leanh::LeanObject,
    mut v_h_2070_: *mut crate::leanh::LeanObject,
    mut v_needStartLine_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2072_: u8 = 0;
    let mut v_res_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2072_ = (crate::leanh::lean_unbox(v_dir_2067_) as u8);
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
    mut v_t_2074_: *mut crate::leanh::LeanObject,
    mut v_needHeader_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2074_, v_needHeader_2075_);
    return v___x_2076_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(
    mut v_dir_2077_: u8,
    mut v_motive_2078_: *mut crate::leanh::LeanObject,
    mut v_t_2079_: *mut crate::leanh::LeanObject,
    mut v_h_2080_: *mut crate::leanh::LeanObject,
    mut v_needHeader_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2079_, v_needHeader_2081_);
    return v___x_2082_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(
    mut v_dir_2083_: *mut crate::leanh::LeanObject,
    mut v_motive_2084_: *mut crate::leanh::LeanObject,
    mut v_t_2085_: *mut crate::leanh::LeanObject,
    mut v_h_2086_: *mut crate::leanh::LeanObject,
    mut v_needHeader_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2088_: u8 = 0;
    let mut v_res_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2088_ = (crate::leanh::lean_unbox(v_dir_2083_) as u8);
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
    mut v_t_2090_: *mut crate::leanh::LeanObject,
    mut v_readBody_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2090_, v_readBody_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_readBody_elim(
    mut v_dir_2093_: u8,
    mut v_motive_2094_: *mut crate::leanh::LeanObject,
    mut v_t_2095_: *mut crate::leanh::LeanObject,
    mut v_h_2096_: *mut crate::leanh::LeanObject,
    mut v_readBody_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2095_, v_readBody_2097_);
    return v___x_2098_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(
    mut v_dir_2099_: *mut crate::leanh::LeanObject,
    mut v_motive_2100_: *mut crate::leanh::LeanObject,
    mut v_t_2101_: *mut crate::leanh::LeanObject,
    mut v_h_2102_: *mut crate::leanh::LeanObject,
    mut v_readBody_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2104_: u8 = 0;
    let mut v_res_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2104_ = (crate::leanh::lean_unbox(v_dir_2099_) as u8);
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
    mut v_t_2106_: *mut crate::leanh::LeanObject,
    mut v_continue_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2106_, v_continue_2107_);
    return v___x_2108_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_continue_elim(
    mut v_dir_2109_: u8,
    mut v_motive_2110_: *mut crate::leanh::LeanObject,
    mut v_t_2111_: *mut crate::leanh::LeanObject,
    mut v_h_2112_: *mut crate::leanh::LeanObject,
    mut v_continue_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2111_, v_continue_2113_);
    return v___x_2114_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(
    mut v_dir_2115_: *mut crate::leanh::LeanObject,
    mut v_motive_2116_: *mut crate::leanh::LeanObject,
    mut v_t_2117_: *mut crate::leanh::LeanObject,
    mut v_h_2118_: *mut crate::leanh::LeanObject,
    mut v_continue_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2120_: u8 = 0;
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2120_ = (crate::leanh::lean_unbox(v_dir_2115_) as u8);
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
    mut v_t_2122_: *mut crate::leanh::LeanObject,
    mut v_pending_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2122_, v_pending_2123_);
    return v___x_2124_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_pending_elim(
    mut v_dir_2125_: u8,
    mut v_motive_2126_: *mut crate::leanh::LeanObject,
    mut v_t_2127_: *mut crate::leanh::LeanObject,
    mut v_h_2128_: *mut crate::leanh::LeanObject,
    mut v_pending_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2127_, v_pending_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(
    mut v_dir_2131_: *mut crate::leanh::LeanObject,
    mut v_motive_2132_: *mut crate::leanh::LeanObject,
    mut v_t_2133_: *mut crate::leanh::LeanObject,
    mut v_h_2134_: *mut crate::leanh::LeanObject,
    mut v_pending_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2136_: u8 = 0;
    let mut v_res_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2136_ = (crate::leanh::lean_unbox(v_dir_2131_) as u8);
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
    mut v_t_2138_: *mut crate::leanh::LeanObject,
    mut v_complete_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2138_, v_complete_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_complete_elim(
    mut v_dir_2141_: u8,
    mut v_motive_2142_: *mut crate::leanh::LeanObject,
    mut v_t_2143_: *mut crate::leanh::LeanObject,
    mut v_h_2144_: *mut crate::leanh::LeanObject,
    mut v_complete_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ =
        l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2143_, v_complete_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(
    mut v_dir_2147_: *mut crate::leanh::LeanObject,
    mut v_motive_2148_: *mut crate::leanh::LeanObject,
    mut v_t_2149_: *mut crate::leanh::LeanObject,
    mut v_h_2150_: *mut crate::leanh::LeanObject,
    mut v_complete_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2152_: u8 = 0;
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2152_ = (crate::leanh::lean_unbox(v_dir_2147_) as u8);
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
    mut v_t_2154_: *mut crate::leanh::LeanObject,
    mut v_closed_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2154_, v_closed_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_closed_elim(
    mut v_dir_2157_: u8,
    mut v_motive_2158_: *mut crate::leanh::LeanObject,
    mut v_t_2159_: *mut crate::leanh::LeanObject,
    mut v_h_2160_: *mut crate::leanh::LeanObject,
    mut v_closed_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2159_, v_closed_2161_);
    return v___x_2162_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(
    mut v_dir_2163_: *mut crate::leanh::LeanObject,
    mut v_motive_2164_: *mut crate::leanh::LeanObject,
    mut v_t_2165_: *mut crate::leanh::LeanObject,
    mut v_h_2166_: *mut crate::leanh::LeanObject,
    mut v_closed_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2168_: u8 = 0;
    let mut v_res_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2168_ = (crate::leanh::lean_unbox(v_dir_2163_) as u8);
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
    mut v_t_2170_: *mut crate::leanh::LeanObject,
    mut v_failed_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2170_, v_failed_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_failed_elim(
    mut v_dir_2173_: u8,
    mut v_motive_2174_: *mut crate::leanh::LeanObject,
    mut v_t_2175_: *mut crate::leanh::LeanObject,
    mut v_h_2176_: *mut crate::leanh::LeanObject,
    mut v_failed_2177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_2175_, v_failed_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(
    mut v_dir_2179_: *mut crate::leanh::LeanObject,
    mut v_motive_2180_: *mut crate::leanh::LeanObject,
    mut v_t_2181_: *mut crate::leanh::LeanObject,
    mut v_h_2182_: *mut crate::leanh::LeanObject,
    mut v_failed_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2184_: u8 = 0;
    let mut v_res_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2184_ = (crate::leanh::lean_unbox(v_dir_2179_) as u8);
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = crate::leanh::lean_box(0);
    return v___x_2187_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(
    mut v_dir_2188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2189_: u8 = 0;
    let mut v_res_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2189_ = (crate::leanh::lean_unbox(v_dir_2188_) as u8);
    v_res_2190_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_2189_);
    return v_res_2190_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState(
    mut v_a_2191_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = crate::leanh::lean_box(0);
    return v___x_2192_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(
    mut v_a_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6__boxed_2194_: u8 = 0;
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_6__boxed_2194_ = (crate::leanh::lean_unbox(v_a_2193_) as u8);
    v_res_2195_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_6__boxed_2194_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(
    mut v_x_2232_: *mut crate::leanh::LeanObject,
    mut v_prec_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___y_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_a_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2232_) {
                0 => {
                    v___x_2262_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2263_ = lean_nat_dec_le(v___x_2262_, v_prec_2233_);
                    if v___x_2263_ == 0 {
                        v___x_2264_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2256_ = v___x_2264_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2265_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2256_ = v___x_2265_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v_a_2266_ = crate::leanh::lean_ctor_get(v_x_2232_, 0);
                    v_isSharedCheck_2286_ = (!crate::leanh::lean_is_exclusive(v_x_2232_)) as u8;
                    if v_isSharedCheck_2286_ == 0 {
                        v___x_2268_ = v_x_2232_;
                        v_isShared_2269_ = v_isSharedCheck_2286_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2266_);
                        crate::leanh::lean_dec(v_x_2232_);
                        v___x_2268_ = crate::leanh::lean_box(0);
                        v_isShared_2269_ = v_isSharedCheck_2286_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_a_2287_ = crate::leanh::lean_ctor_get(v_x_2232_, 0);
                    crate::leanh::lean_inc(v_a_2287_);
                    crate::leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2298_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2299_ = lean_nat_dec_le(v___x_2298_, v_prec_2233_);
                    if v___x_2299_ == 0 {
                        v___x_2300_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2289_ = v___x_2300_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2289_ = v___x_2301_;
                        state = 8;
                        continue;
                    }
                }
                3 => {
                    v_a_2302_ = crate::leanh::lean_ctor_get(v_x_2232_, 0);
                    crate::leanh::lean_inc(v_a_2302_);
                    crate::leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2303_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2313_ = lean_nat_dec_le(v___x_2303_, v_prec_2233_);
                    if v___x_2313_ == 0 {
                        v___x_2314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2305_ = v___x_2314_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2305_ = v___x_2315_;
                        state = 9;
                        continue;
                    }
                }
                4 => {
                    v___x_2316_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2317_ = lean_nat_dec_le(v___x_2316_, v_prec_2233_);
                    if v___x_2317_ == 0 {
                        v___x_2318_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2249_ = v___x_2318_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2249_ = v___x_2319_;
                        state = 3;
                        continue;
                    }
                }
                5 => {
                    v___x_2320_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2321_ = lean_nat_dec_le(v___x_2320_, v_prec_2233_);
                    if v___x_2321_ == 0 {
                        v___x_2322_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2242_ = v___x_2322_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2323_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2242_ = v___x_2323_;
                        state = 2;
                        continue;
                    }
                }
                6 => {
                    v___x_2324_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2325_ = lean_nat_dec_le(v___x_2324_, v_prec_2233_);
                    if v___x_2325_ == 0 {
                        v___x_2326_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2235_ = v___x_2326_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2327_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2235_ = v___x_2327_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_error_2328_ = crate::leanh::lean_ctor_get(v_x_2232_, 0);
                    crate::leanh::lean_inc(v_error_2328_);
                    crate::leanh::lean_dec_ref_known(v_x_2232_, 1);
                    v___x_2339_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2340_ = lean_nat_dec_le(v___x_2339_, v_prec_2233_);
                    if v___x_2340_ == 0 {
                        v___x_2341_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
                        v___y_2330_ = v___x_2341_;
                        state = 10;
                        continue;
                    } else {
                        v___x_2342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once), _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
                        v___y_2330_ = v___x_2342_;
                        state = 10;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2236_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1;
                crate::leanh::lean_inc(v___y_2235_);
                v___x_2237_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2237_, 0, v___y_2235_);
                crate::leanh::lean_ctor_set(v___x_2237_, 1, v___x_2236_);
                v___x_2238_ = 0;
                v___x_2239_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2237_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2239_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2238_,
                );
                v___x_2240_ = l_Repr_addAppParen(v___x_2239_, v_prec_2233_);
                return v___x_2240_;
            }
            2 => {
                v___x_2243_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3;
                crate::leanh::lean_inc(v___y_2242_);
                v___x_2244_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2244_, 0, v___y_2242_);
                crate::leanh::lean_ctor_set(v___x_2244_, 1, v___x_2243_);
                v___x_2245_ = 0;
                v___x_2246_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2246_, 0, v___x_2244_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2246_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2245_,
                );
                v___x_2247_ = l_Repr_addAppParen(v___x_2246_, v_prec_2233_);
                return v___x_2247_;
            }
            3 => {
                v___x_2250_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5;
                crate::leanh::lean_inc(v___y_2249_);
                v___x_2251_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2251_, 0, v___y_2249_);
                crate::leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
                v___x_2252_ = 0;
                v___x_2253_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2251_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2253_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2252_,
                );
                v___x_2254_ = l_Repr_addAppParen(v___x_2253_, v_prec_2233_);
                return v___x_2254_;
            }
            4 => {
                v___x_2257_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7;
                crate::leanh::lean_inc(v___y_2256_);
                v___x_2258_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2258_, 0, v___y_2256_);
                crate::leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                v___x_2259_ = 0;
                v___x_2260_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2260_, 0, v___x_2258_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2260_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2259_,
                );
                v___x_2261_ = l_Repr_addAppParen(v___x_2260_, v_prec_2233_);
                return v___x_2261_;
            }
            5 => {
                v___x_2282_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2283_ = lean_nat_dec_le(v___x_2282_, v_prec_2233_);
                if v___x_2283_ == 0 {
                    v___x_2284_ = crate::leanh::lean_obj_once(
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
                    v___x_2285_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_2268_, 3);
                    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2268_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2273_);
                    v___x_2275_ = v_reuseFailAlloc_2281_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2276_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2272_);
                crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                crate::leanh::lean_inc(v___y_2271_);
                v___x_2277_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2277_, 0, v___y_2271_);
                crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = 0;
                v___x_2279_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2279_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2278_,
                );
                v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2233_);
                return v___x_2280_;
            }
            8 => {
                v___x_2290_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13;
                v___x_2291_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2292_ =
                    l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_2287_, v___x_2291_);
                v___x_2293_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2290_);
                crate::leanh::lean_ctor_set(v___x_2293_, 1, v___x_2292_);
                crate::leanh::lean_inc(v___y_2289_);
                v___x_2294_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2294_, 0, v___y_2289_);
                crate::leanh::lean_ctor_set(v___x_2294_, 1, v___x_2293_);
                v___x_2295_ = 0;
                v___x_2296_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2296_, 0, v___x_2294_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2296_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_2308_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2306_);
                crate::leanh::lean_ctor_set(v___x_2308_, 1, v___x_2307_);
                crate::leanh::lean_inc(v___y_2305_);
                v___x_2309_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2309_, 0, v___y_2305_);
                crate::leanh::lean_ctor_set(v___x_2309_, 1, v___x_2308_);
                v___x_2310_ = 0;
                v___x_2311_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2311_, 0, v___x_2309_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2311_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2310_,
                );
                v___x_2312_ = l_Repr_addAppParen(v___x_2311_, v_prec_2233_);
                return v___x_2312_;
            }
            10 => {
                v___x_2331_ =
                    l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19;
                v___x_2332_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2333_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_2328_, v___x_2332_);
                v___x_2334_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2334_, 0, v___x_2331_);
                crate::leanh::lean_ctor_set(v___x_2334_, 1, v___x_2333_);
                crate::leanh::lean_inc(v___y_2330_);
                v___x_2335_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2335_, 0, v___y_2330_);
                crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                v___x_2336_ = 0;
                v___x_2337_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_2343_: *mut crate::leanh::LeanObject,
    mut v_prec_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2345_ =
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_2343_, v_prec_2344_);
    crate::leanh::lean_dec(v_prec_2344_);
    return v_res_2345_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr(
    mut v_dir_2346_: u8,
    mut v_x_2347_: *mut crate::leanh::LeanObject,
    mut v_prec_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ =
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_2347_, v_prec_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(
    mut v_dir_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_prec_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_892__boxed_2353_: u8 = 0;
    let mut v_res_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_892__boxed_2353_ = (crate::leanh::lean_unbox(v_dir_2350_) as u8);
    v_res_2354_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(
        v_dir_892__boxed_2353_,
        v_x_2351_,
        v_prec_2352_,
    );
    crate::leanh::lean_dec(v_prec_2352_);
    return v_res_2354_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState(
    mut v_dir_2355_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2356_ = crate::leanh::lean_box((v_dir_2355_) as usize);
    v___x_2357_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2357_, 0, v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instReprState___boxed(
    mut v_dir_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_5__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_2359_ = (crate::leanh::lean_unbox(v_dir_2358_) as u8);
    v_res_2360_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_2359_);
    return v_res_2360_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(
    mut v_x_2361_: *mut crate::leanh::LeanObject,
    mut v_x_2362_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v_a_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: u8 = 0;
    let mut v_a_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: u8 = 0;
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut v_error_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2361_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 0 {
                        v___x_2363_ = 1;
                        return v___x_2363_;
                    } else {
                        v___x_2364_ = 0;
                        return v___x_2364_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 1 {
                        v_a_2365_ = crate::leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2366_ = crate::leanh::lean_ctor_get(v_x_2362_, 0);
                        v___x_2367_ = lean_nat_dec_eq(v_a_2365_, v_a_2366_);
                        return v___x_2367_;
                    } else {
                        v___x_2368_ = 0;
                        return v___x_2368_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 2 {
                        v_a_2369_ = crate::leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2370_ = crate::leanh::lean_ctor_get(v_x_2362_, 0);
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
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 3 {
                        v_a_2373_ = crate::leanh::lean_ctor_get(v_x_2361_, 0);
                        v_a_2374_ = crate::leanh::lean_ctor_get(v_x_2362_, 0);
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
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 4 {
                        v___x_2377_ = 1;
                        return v___x_2377_;
                    } else {
                        v___x_2378_ = 0;
                        return v___x_2378_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 5 {
                        v___x_2379_ = 1;
                        return v___x_2379_;
                    } else {
                        v___x_2380_ = 0;
                        return v___x_2380_;
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 6 {
                        v___x_2381_ = 1;
                        return v___x_2381_;
                    } else {
                        v___x_2382_ = 0;
                        return v___x_2382_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_2362_) == 7 {
                        v_error_2383_ = crate::leanh::lean_ctor_get(v_x_2361_, 0);
                        v_error_2384_ = crate::leanh::lean_ctor_get(v_x_2362_, 0);
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
    mut v_x_2387_: *mut crate::leanh::LeanObject,
    mut v_x_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: u8 = 0;
    let mut v_r_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_2387_, v_x_2388_);
    crate::leanh::lean_dec(v_x_2388_);
    crate::leanh::lean_dec(v_x_2387_);
    v_r_2390_ = crate::leanh::lean_box((v_res_2389_) as usize);
    return v_r_2390_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq(
    mut v_dir_2391_: u8,
    mut v_x_2392_: *mut crate::leanh::LeanObject,
    mut v_x_2393_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2394_: u8 = 0;
    v___x_2394_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_2392_, v_x_2393_);
    return v___x_2394_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(
    mut v_dir_2395_: *mut crate::leanh::LeanObject,
    mut v_x_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_218__boxed_2398_: u8 = 0;
    let mut v_res_2399_: u8 = 0;
    let mut v_r_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_218__boxed_2398_ = (crate::leanh::lean_unbox(v_dir_2395_) as u8);
    v_res_2399_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(
        v_dir_218__boxed_2398_,
        v_x_2396_,
        v_x_2397_,
    );
    crate::leanh::lean_dec(v_x_2397_);
    crate::leanh::lean_dec(v_x_2396_);
    v_r_2400_ = crate::leanh::lean_box((v_res_2399_) as usize);
    return v_r_2400_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState(
    mut v_dir_2401_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = crate::leanh::lean_box((v_dir_2401_) as usize);
    v___x_2403_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2403_, 0, v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(
    mut v_dir_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_5__boxed_2405_: u8 = 0;
    let mut v_res_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_2405_ = (crate::leanh::lean_unbox(v_dir_2404_) as u8);
    v_res_2406_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed___redArg(
    mut v_reader_2407_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2408_ = crate::leanh::lean_ctor_get(v_reader_2407_, 0);
    if crate::leanh::lean_obj_tag(v_state_2408_) == 6 {
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
    mut v_reader_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: u8 = 0;
    let mut v_r_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_2411_);
    crate::leanh::lean_dec_ref(v_reader_2411_);
    v_r_2413_ = crate::leanh::lean_box((v_res_2412_) as usize);
    return v_r_2413_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isClosed(
    mut v_dir_2414_: u8,
    mut v_reader_2415_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2416_ = crate::leanh::lean_ctor_get(v_reader_2415_, 0);
    if crate::leanh::lean_obj_tag(v_state_2416_) == 6 {
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
    mut v_dir_2419_: *mut crate::leanh::LeanObject,
    mut v_reader_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2421_: u8 = 0;
    let mut v_res_2422_: u8 = 0;
    let mut v_r_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2421_ = (crate::leanh::lean_unbox(v_dir_2419_) as u8);
    v_res_2422_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_2421_, v_reader_2420_);
    crate::leanh::lean_dec_ref(v_reader_2420_);
    v_r_2423_ = crate::leanh::lean_box((v_res_2422_) as usize);
    return v_r_2423_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete___redArg(
    mut v_reader_2424_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2425_ = crate::leanh::lean_ctor_get(v_reader_2424_, 0);
    if crate::leanh::lean_obj_tag(v_state_2425_) == 5 {
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
    mut v_reader_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: u8 = 0;
    let mut v_r_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_2428_);
    crate::leanh::lean_dec_ref(v_reader_2428_);
    v_r_2430_ = crate::leanh::lean_box((v_res_2429_) as usize);
    return v_r_2430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_isComplete(
    mut v_dir_2431_: u8,
    mut v_reader_2432_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2433_ = crate::leanh::lean_ctor_get(v_reader_2432_, 0);
    if crate::leanh::lean_obj_tag(v_state_2433_) == 5 {
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
    mut v_dir_2436_: *mut crate::leanh::LeanObject,
    mut v_reader_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2438_: u8 = 0;
    let mut v_res_2439_: u8 = 0;
    let mut v_r_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2438_ = (crate::leanh::lean_unbox(v_dir_2436_) as u8);
    v_res_2439_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_2438_, v_reader_2437_);
    crate::leanh::lean_dec_ref(v_reader_2437_);
    v_r_2440_ = crate::leanh::lean_box((v_res_2439_) as usize);
    return v_r_2440_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(
    mut v_reader_2441_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2442_ = crate::leanh::lean_ctor_get(v_reader_2441_, 0);
    if crate::leanh::lean_obj_tag(v_state_2442_) == 7 {
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
    mut v_reader_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2446_: u8 = 0;
    let mut v_r_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_2445_);
    crate::leanh::lean_dec_ref(v_reader_2445_);
    v_r_2447_ = crate::leanh::lean_box((v_res_2446_) as usize);
    return v_r_2447_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_hasFailed(
    mut v_dir_2448_: u8,
    mut v_reader_2449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2450_ = crate::leanh::lean_ctor_get(v_reader_2449_, 0);
    if crate::leanh::lean_obj_tag(v_state_2450_) == 7 {
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
    mut v_dir_2453_: *mut crate::leanh::LeanObject,
    mut v_reader_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2455_: u8 = 0;
    let mut v_res_2456_: u8 = 0;
    let mut v_r_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2455_ = (crate::leanh::lean_unbox(v_dir_2453_) as u8);
    v_res_2456_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_2455_, v_reader_2454_);
    crate::leanh::lean_dec_ref(v_reader_2454_);
    v_r_2457_ = crate::leanh::lean_box((v_res_2456_) as usize);
    return v_r_2457_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_feed___redArg(
    mut v_data_2458_: *mut crate::leanh::LeanObject,
    mut v_reader_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2466_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v_array_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2460_ = crate::leanh::lean_ctor_get(v_reader_2459_, 1);
                v_state_2461_ = crate::leanh::lean_ctor_get(v_reader_2459_, 0);
                v_messageHead_2462_ = crate::leanh::lean_ctor_get(v_reader_2459_, 2);
                v_messageCount_2463_ = crate::leanh::lean_ctor_get(v_reader_2459_, 3);
                v_bodyBytesRead_2464_ = crate::leanh::lean_ctor_get(v_reader_2459_, 4);
                v_headerBytesRead_2465_ = crate::leanh::lean_ctor_get(v_reader_2459_, 5);
                v_noMoreInput_2466_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2459_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2487_ = (!crate::leanh::lean_is_exclusive(v_reader_2459_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v___x_2468_ = v_reader_2459_;
                    v_isShared_2469_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2465_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2464_);
                    crate::leanh::lean_inc(v_messageCount_2463_);
                    crate::leanh::lean_inc(v_messageHead_2462_);
                    crate::leanh::lean_inc(v_input_2460_);
                    crate::leanh::lean_inc(v_state_2461_);
                    crate::leanh::lean_dec(v_reader_2459_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2470_ = crate::leanh::lean_ctor_get(v_input_2460_, 0);
                crate::leanh::lean_inc_ref(v_array_2470_);
                v_idx_2471_ = crate::leanh::lean_ctor_get(v_input_2460_, 1);
                crate::leanh::lean_inc(v_idx_2471_);
                crate::leanh::lean_dec_ref(v_input_2460_);
                v___x_2472_ = lean_byte_array_size(v_array_2470_);
                v___x_2473_ = lean_nat_dec_le(v___x_2472_, v_idx_2471_);
                if v___x_2473_ == 0 {
                    v___x_2474_ = l_ByteArray_extract(v_array_2470_, v_idx_2471_, v___x_2472_);
                    crate::leanh::lean_dec_ref(v_array_2470_);
                    v___x_2475_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    crate::leanh::lean_dec_ref(v_data_2458_);
                    v___x_2479_ = l_ByteArray_mkIterator(v___x_2478_);
                    if v_isShared_2469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2468_, 1, v___x_2479_);
                        v___x_2481_ = v___x_2468_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2482_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_state_2461_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2479_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_messageHead_2462_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            3,
                            v_messageCount_2463_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            4,
                            v_bodyBytesRead_2464_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2482_,
                            5,
                            v_headerBytesRead_2465_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2482_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2466_,
                        );
                        v___x_2481_ = v_reuseFailAlloc_2482_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_idx_2471_);
                    crate::leanh::lean_dec_ref(v_array_2470_);
                    v___x_2483_ = l_ByteArray_mkIterator(v_data_2458_);
                    if v_isShared_2469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2468_, 1, v___x_2483_);
                        v___x_2485_ = v___x_2468_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2486_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_state_2461_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2483_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_messageHead_2462_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            3,
                            v_messageCount_2463_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            4,
                            v_bodyBytesRead_2464_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2486_,
                            5,
                            v_headerBytesRead_2465_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2486_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_data_2489_: *mut crate::leanh::LeanObject,
    mut v_reader_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2497_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_array_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2491_ = crate::leanh::lean_ctor_get(v_reader_2490_, 1);
                v_state_2492_ = crate::leanh::lean_ctor_get(v_reader_2490_, 0);
                v_messageHead_2493_ = crate::leanh::lean_ctor_get(v_reader_2490_, 2);
                v_messageCount_2494_ = crate::leanh::lean_ctor_get(v_reader_2490_, 3);
                v_bodyBytesRead_2495_ = crate::leanh::lean_ctor_get(v_reader_2490_, 4);
                v_headerBytesRead_2496_ = crate::leanh::lean_ctor_get(v_reader_2490_, 5);
                v_noMoreInput_2497_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2518_ = (!crate::leanh::lean_is_exclusive(v_reader_2490_)) as u8;
                if v_isSharedCheck_2518_ == 0 {
                    v___x_2499_ = v_reader_2490_;
                    v_isShared_2500_ = v_isSharedCheck_2518_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2496_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2495_);
                    crate::leanh::lean_inc(v_messageCount_2494_);
                    crate::leanh::lean_inc(v_messageHead_2493_);
                    crate::leanh::lean_inc(v_input_2491_);
                    crate::leanh::lean_inc(v_state_2492_);
                    crate::leanh::lean_dec(v_reader_2490_);
                    v___x_2499_ = crate::leanh::lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2501_ = crate::leanh::lean_ctor_get(v_input_2491_, 0);
                crate::leanh::lean_inc_ref(v_array_2501_);
                v_idx_2502_ = crate::leanh::lean_ctor_get(v_input_2491_, 1);
                crate::leanh::lean_inc(v_idx_2502_);
                crate::leanh::lean_dec_ref(v_input_2491_);
                v___x_2503_ = lean_byte_array_size(v_array_2501_);
                v___x_2504_ = lean_nat_dec_le(v___x_2503_, v_idx_2502_);
                if v___x_2504_ == 0 {
                    v___x_2505_ = l_ByteArray_extract(v_array_2501_, v_idx_2502_, v___x_2503_);
                    crate::leanh::lean_dec_ref(v_array_2501_);
                    v___x_2506_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    crate::leanh::lean_dec_ref(v_data_2489_);
                    v___x_2510_ = l_ByteArray_mkIterator(v___x_2509_);
                    if v_isShared_2500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2499_, 1, v___x_2510_);
                        v___x_2512_ = v___x_2499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2513_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_state_2492_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2510_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_messageHead_2493_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            3,
                            v_messageCount_2494_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            4,
                            v_bodyBytesRead_2495_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2513_,
                            5,
                            v_headerBytesRead_2496_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2513_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                            v_noMoreInput_2497_,
                        );
                        v___x_2512_ = v_reuseFailAlloc_2513_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_idx_2502_);
                    crate::leanh::lean_dec_ref(v_array_2501_);
                    v___x_2514_ = l_ByteArray_mkIterator(v_data_2489_);
                    if v_isShared_2500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2499_, 1, v___x_2514_);
                        v___x_2516_ = v___x_2499_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2517_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_state_2492_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_messageHead_2493_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            3,
                            v_messageCount_2494_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            4,
                            v_bodyBytesRead_2495_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2517_,
                            5,
                            v_headerBytesRead_2496_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2517_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2519_: *mut crate::leanh::LeanObject,
    mut v_data_2520_: *mut crate::leanh::LeanObject,
    mut v_reader_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2522_: u8 = 0;
    let mut v_res_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2522_ = (crate::leanh::lean_unbox(v_dir_2519_) as u8);
    v_res_2523_ =
        l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_2522_, v_data_2520_, v_reader_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setInput___redArg(
    mut v_input_2524_: *mut crate::leanh::LeanObject,
    mut v_reader_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2531_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v_unused_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2526_ = crate::leanh::lean_ctor_get(v_reader_2525_, 0);
                v_messageHead_2527_ = crate::leanh::lean_ctor_get(v_reader_2525_, 2);
                v_messageCount_2528_ = crate::leanh::lean_ctor_get(v_reader_2525_, 3);
                v_bodyBytesRead_2529_ = crate::leanh::lean_ctor_get(v_reader_2525_, 4);
                v_headerBytesRead_2530_ = crate::leanh::lean_ctor_get(v_reader_2525_, 5);
                v_noMoreInput_2531_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2525_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2538_ = (!crate::leanh::lean_is_exclusive(v_reader_2525_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v_unused_2539_ = crate::leanh::lean_ctor_get(v_reader_2525_, 1);
                    crate::leanh::lean_dec(v_unused_2539_);
                    v___x_2533_ = v_reader_2525_;
                    v_isShared_2534_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2530_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2529_);
                    crate::leanh::lean_inc(v_messageCount_2528_);
                    crate::leanh::lean_inc(v_messageHead_2527_);
                    crate::leanh::lean_inc(v_state_2526_);
                    crate::leanh::lean_dec(v_reader_2525_);
                    v___x_2533_ = crate::leanh::lean_box(0);
                    v_isShared_2534_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2534_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2533_, 1, v_input_2524_);
                    v___x_2536_ = v___x_2533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_state_2526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_input_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_messageHead_2527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_messageCount_2528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_bodyBytesRead_2529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_headerBytesRead_2530_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2537_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_input_2541_: *mut crate::leanh::LeanObject,
    mut v_reader_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2548_: u8 = 0;
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_unused_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2543_ = crate::leanh::lean_ctor_get(v_reader_2542_, 0);
                v_messageHead_2544_ = crate::leanh::lean_ctor_get(v_reader_2542_, 2);
                v_messageCount_2545_ = crate::leanh::lean_ctor_get(v_reader_2542_, 3);
                v_bodyBytesRead_2546_ = crate::leanh::lean_ctor_get(v_reader_2542_, 4);
                v_headerBytesRead_2547_ = crate::leanh::lean_ctor_get(v_reader_2542_, 5);
                v_noMoreInput_2548_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2555_ = (!crate::leanh::lean_is_exclusive(v_reader_2542_)) as u8;
                if v_isSharedCheck_2555_ == 0 {
                    v_unused_2556_ = crate::leanh::lean_ctor_get(v_reader_2542_, 1);
                    crate::leanh::lean_dec(v_unused_2556_);
                    v___x_2550_ = v_reader_2542_;
                    v_isShared_2551_ = v_isSharedCheck_2555_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2547_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2546_);
                    crate::leanh::lean_inc(v_messageCount_2545_);
                    crate::leanh::lean_inc(v_messageHead_2544_);
                    crate::leanh::lean_inc(v_state_2543_);
                    crate::leanh::lean_dec(v_reader_2542_);
                    v___x_2550_ = crate::leanh::lean_box(0);
                    v_isShared_2551_ = v_isSharedCheck_2555_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2550_, 1, v_input_2541_);
                    v___x_2553_ = v___x_2550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_state_2543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_input_2541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_messageHead_2544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_messageCount_2545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_bodyBytesRead_2546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 5, v_headerBytesRead_2547_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2554_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2557_: *mut crate::leanh::LeanObject,
    mut v_input_2558_: *mut crate::leanh::LeanObject,
    mut v_reader_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2560_: u8 = 0;
    let mut v_res_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2560_ = (crate::leanh::lean_unbox(v_dir_2557_) as u8);
    v_res_2561_ =
        l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_2560_, v_input_2558_, v_reader_2559_);
    return v_res_2561_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(
    mut v_messageHead_2562_: *mut crate::leanh::LeanObject,
    mut v_reader_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2569_: u8 = 0;
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_unused_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2564_ = crate::leanh::lean_ctor_get(v_reader_2563_, 0);
                v_input_2565_ = crate::leanh::lean_ctor_get(v_reader_2563_, 1);
                v_messageCount_2566_ = crate::leanh::lean_ctor_get(v_reader_2563_, 3);
                v_bodyBytesRead_2567_ = crate::leanh::lean_ctor_get(v_reader_2563_, 4);
                v_headerBytesRead_2568_ = crate::leanh::lean_ctor_get(v_reader_2563_, 5);
                v_noMoreInput_2569_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v_reader_2563_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v_unused_2577_ = crate::leanh::lean_ctor_get(v_reader_2563_, 2);
                    crate::leanh::lean_dec(v_unused_2577_);
                    v___x_2571_ = v_reader_2563_;
                    v_isShared_2572_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2568_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2567_);
                    crate::leanh::lean_inc(v_messageCount_2566_);
                    crate::leanh::lean_inc(v_input_2565_);
                    crate::leanh::lean_inc(v_state_2564_);
                    crate::leanh::lean_dec(v_reader_2563_);
                    v___x_2571_ = crate::leanh::lean_box(0);
                    v_isShared_2572_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2571_, 2, v_messageHead_2562_);
                    v___x_2574_ = v___x_2571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_state_2564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_input_2565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_messageHead_2562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_messageCount_2566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_bodyBytesRead_2567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 5, v_headerBytesRead_2568_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2575_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_messageHead_2579_: *mut crate::leanh::LeanObject,
    mut v_reader_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2586_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_unused_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2581_ = crate::leanh::lean_ctor_get(v_reader_2580_, 0);
                v_input_2582_ = crate::leanh::lean_ctor_get(v_reader_2580_, 1);
                v_messageCount_2583_ = crate::leanh::lean_ctor_get(v_reader_2580_, 3);
                v_bodyBytesRead_2584_ = crate::leanh::lean_ctor_get(v_reader_2580_, 4);
                v_headerBytesRead_2585_ = crate::leanh::lean_ctor_get(v_reader_2580_, 5);
                v_noMoreInput_2586_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2593_ = (!crate::leanh::lean_is_exclusive(v_reader_2580_)) as u8;
                if v_isSharedCheck_2593_ == 0 {
                    v_unused_2594_ = crate::leanh::lean_ctor_get(v_reader_2580_, 2);
                    crate::leanh::lean_dec(v_unused_2594_);
                    v___x_2588_ = v_reader_2580_;
                    v_isShared_2589_ = v_isSharedCheck_2593_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2585_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2584_);
                    crate::leanh::lean_inc(v_messageCount_2583_);
                    crate::leanh::lean_inc(v_input_2582_);
                    crate::leanh::lean_inc(v_state_2581_);
                    crate::leanh::lean_dec(v_reader_2580_);
                    v___x_2588_ = crate::leanh::lean_box(0);
                    v_isShared_2589_ = v_isSharedCheck_2593_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2588_, 2, v_messageHead_2579_);
                    v___x_2591_ = v___x_2588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_state_2581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_input_2582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_messageHead_2579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 3, v_messageCount_2583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 4, v_bodyBytesRead_2584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 5, v_headerBytesRead_2585_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2592_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2595_: *mut crate::leanh::LeanObject,
    mut v_messageHead_2596_: *mut crate::leanh::LeanObject,
    mut v_reader_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2598_: u8 = 0;
    let mut v_res_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2598_ = (crate::leanh::lean_unbox(v_dir_2595_) as u8);
    v_res_2599_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(
        v_dir_boxed_2598_,
        v_messageHead_2596_,
        v_reader_2597_,
    );
    return v_res_2599_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(
    mut v_i_2600_: *mut crate::leanh::LeanObject,
    mut v_x_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2601_) == 0 {
                    v___x_2602_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2603_ = lean_mk_empty_array_with_capacity(v___x_2602_);
                    v___x_2604_ = lean_array_push(v___x_2603_, v_i_2600_);
                    v___x_2605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2605_, 0, v___x_2604_);
                    return v___x_2605_;
                } else {
                    v_val_2606_ = crate::leanh::lean_ctor_get(v_x_2601_, 0);
                    v_isSharedCheck_2614_ = (!crate::leanh::lean_is_exclusive(v_x_2601_)) as u8;
                    if v_isSharedCheck_2614_ == 0 {
                        v___x_2608_ = v_x_2601_;
                        v_isShared_2609_ = v_isSharedCheck_2614_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2606_);
                        crate::leanh::lean_dec(v_x_2601_);
                        v___x_2608_ = crate::leanh::lean_box(0);
                        v_isShared_2609_ = v_isSharedCheck_2614_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2610_ = lean_array_push(v_val_2606_, v_i_2600_);
                if v_isShared_2609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
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
    mut v_name_2618_: *mut crate::leanh::LeanObject,
    mut v_value_2619_: *mut crate::leanh::LeanObject,
    mut v_reader_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_messageHead_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2627_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v_method_2631_: u8 = 0;
    let mut v_version_2632_: u8 = 0;
    let mut v_uri_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2637_: u8 = 0;
    let mut v_entries_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2642_: u8 = 0;
    let mut v___f_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_unused_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_messageHead_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2670_: u8 = 0;
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v_status_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2675_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_entries_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___f_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_unused_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_dir_2617_ == 0 {
                    v_messageHead_2621_ = crate::leanh::lean_ctor_get(v_reader_2620_, 2);
                    v_state_2622_ = crate::leanh::lean_ctor_get(v_reader_2620_, 0);
                    v_input_2623_ = crate::leanh::lean_ctor_get(v_reader_2620_, 1);
                    v_messageCount_2624_ = crate::leanh::lean_ctor_get(v_reader_2620_, 3);
                    v_bodyBytesRead_2625_ = crate::leanh::lean_ctor_get(v_reader_2620_, 4);
                    v_headerBytesRead_2626_ = crate::leanh::lean_ctor_get(v_reader_2620_, 5);
                    v_noMoreInput_2627_ = crate::leanh::lean_ctor_get_uint8(
                        v_reader_2620_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    );
                    v_isSharedCheck_2663_ =
                        (!crate::leanh::lean_is_exclusive(v_reader_2620_)) as u8;
                    if v_isSharedCheck_2663_ == 0 {
                        v___x_2629_ = v_reader_2620_;
                        v_isShared_2630_ = v_isSharedCheck_2663_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_headerBytesRead_2626_);
                        crate::leanh::lean_inc(v_bodyBytesRead_2625_);
                        crate::leanh::lean_inc(v_messageCount_2624_);
                        crate::leanh::lean_inc(v_messageHead_2621_);
                        crate::leanh::lean_inc(v_input_2623_);
                        crate::leanh::lean_inc(v_state_2622_);
                        crate::leanh::lean_dec(v_reader_2620_);
                        v___x_2629_ = crate::leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_messageHead_2664_ = crate::leanh::lean_ctor_get(v_reader_2620_, 2);
                    v_state_2665_ = crate::leanh::lean_ctor_get(v_reader_2620_, 0);
                    v_input_2666_ = crate::leanh::lean_ctor_get(v_reader_2620_, 1);
                    v_messageCount_2667_ = crate::leanh::lean_ctor_get(v_reader_2620_, 3);
                    v_bodyBytesRead_2668_ = crate::leanh::lean_ctor_get(v_reader_2620_, 4);
                    v_headerBytesRead_2669_ = crate::leanh::lean_ctor_get(v_reader_2620_, 5);
                    v_noMoreInput_2670_ = crate::leanh::lean_ctor_get_uint8(
                        v_reader_2620_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    );
                    v_isSharedCheck_2705_ =
                        (!crate::leanh::lean_is_exclusive(v_reader_2620_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2672_ = v_reader_2620_;
                        v_isShared_2673_ = v_isSharedCheck_2705_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_headerBytesRead_2669_);
                        crate::leanh::lean_inc(v_bodyBytesRead_2668_);
                        crate::leanh::lean_inc(v_messageCount_2667_);
                        crate::leanh::lean_inc(v_messageHead_2664_);
                        crate::leanh::lean_inc(v_input_2666_);
                        crate::leanh::lean_inc(v_state_2665_);
                        crate::leanh::lean_dec(v_reader_2620_);
                        v___x_2672_ = crate::leanh::lean_box(0);
                        v_isShared_2673_ = v_isSharedCheck_2705_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_method_2631_ = crate::leanh::lean_ctor_get_uint8(
                    v_messageHead_2621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_version_2632_ = crate::leanh::lean_ctor_get_uint8(
                    v_messageHead_2621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_uri_2633_ = crate::leanh::lean_ctor_get(v_messageHead_2621_, 0);
                crate::leanh::lean_inc(v_uri_2633_);
                v___x_2634_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_2617_, v_messageHead_2621_);
                v_isSharedCheck_2660_ =
                    (!crate::leanh::lean_is_exclusive(v_messageHead_2621_)) as u8;
                if v_isSharedCheck_2660_ == 0 {
                    v_unused_2661_ = crate::leanh::lean_ctor_get(v_messageHead_2621_, 1);
                    crate::leanh::lean_dec(v_unused_2661_);
                    v_unused_2662_ = crate::leanh::lean_ctor_get(v_messageHead_2621_, 0);
                    crate::leanh::lean_dec(v_unused_2662_);
                    v___x_2636_ = v_messageHead_2621_;
                    v_isShared_2637_ = v_isSharedCheck_2660_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_messageHead_2621_);
                    v___x_2636_ = crate::leanh::lean_box(0);
                    v_isShared_2637_ = v_isSharedCheck_2660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_2638_ = crate::leanh::lean_ctor_get(v___x_2634_, 0);
                v_indexes_2639_ = crate::leanh::lean_ctor_get(v___x_2634_, 1);
                v_isSharedCheck_2659_ = (!crate::leanh::lean_is_exclusive(v___x_2634_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v___x_2641_ = v___x_2634_;
                    v_isShared_2642_ = v_isSharedCheck_2659_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2639_);
                    crate::leanh::lean_inc(v_entries_2638_);
                    crate::leanh::lean_dec(v___x_2634_);
                    v___x_2641_ = crate::leanh::lean_box(0);
                    v_isShared_2642_ = v_isSharedCheck_2659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_2643_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__0;
                v___f_2644_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__1;
                v_i_2645_ = lean_array_get_size(v_entries_2638_);
                v_f_2646_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Protocol_H1_Reader_addHeader___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2646_, 0, v_i_2645_);
                crate::leanh::lean_inc_ref(v_name_2618_);
                v___x_2647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2647_, 0, v_name_2618_);
                crate::leanh::lean_ctor_set(v___x_2647_, 1, v_value_2619_);
                v_entries_2648_ = lean_array_push(v_entries_2638_, v___x_2647_);
                v_indexes_2649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2643_,
                    v___f_2644_,
                    v_indexes_2639_,
                    v_name_2618_,
                    v_f_2646_,
                );
                if v_isShared_2642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2641_, 1, v_indexes_2649_);
                    crate::leanh::lean_ctor_set(v___x_2641_, 0, v_entries_2648_);
                    v___x_2651_ = v___x_2641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_entries_2648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_indexes_2649_);
                    v___x_2651_ = v_reuseFailAlloc_2658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2636_, 1, v___x_2651_);
                    v___x_2653_ = v___x_2636_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(0, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_uri_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2651_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2657_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_method_2631_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2657_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_version_2632_,
                    );
                    v___x_2653_ = v_reuseFailAlloc_2657_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 2, v___x_2653_);
                    v___x_2655_ = v___x_2629_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_state_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_input_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 2, v___x_2653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_messageCount_2624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_bodyBytesRead_2625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_headerBytesRead_2626_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2656_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
                v_status_2674_ = crate::leanh::lean_ctor_get(v_messageHead_2664_, 0);
                crate::leanh::lean_inc(v_status_2674_);
                v_version_2675_ = crate::leanh::lean_ctor_get_uint8(
                    v_messageHead_2664_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v___x_2676_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_2617_, v_messageHead_2664_);
                v_isSharedCheck_2702_ =
                    (!crate::leanh::lean_is_exclusive(v_messageHead_2664_)) as u8;
                if v_isSharedCheck_2702_ == 0 {
                    v_unused_2703_ = crate::leanh::lean_ctor_get(v_messageHead_2664_, 1);
                    crate::leanh::lean_dec(v_unused_2703_);
                    v_unused_2704_ = crate::leanh::lean_ctor_get(v_messageHead_2664_, 0);
                    crate::leanh::lean_dec(v_unused_2704_);
                    v___x_2678_ = v_messageHead_2664_;
                    v_isShared_2679_ = v_isSharedCheck_2702_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_messageHead_2664_);
                    v___x_2678_ = crate::leanh::lean_box(0);
                    v_isShared_2679_ = v_isSharedCheck_2702_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_entries_2680_ = crate::leanh::lean_ctor_get(v___x_2676_, 0);
                v_indexes_2681_ = crate::leanh::lean_ctor_get(v___x_2676_, 1);
                v_isSharedCheck_2701_ = (!crate::leanh::lean_is_exclusive(v___x_2676_)) as u8;
                if v_isSharedCheck_2701_ == 0 {
                    v___x_2683_ = v___x_2676_;
                    v_isShared_2684_ = v_isSharedCheck_2701_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2681_);
                    crate::leanh::lean_inc(v_entries_2680_);
                    crate::leanh::lean_dec(v___x_2676_);
                    v___x_2683_ = crate::leanh::lean_box(0);
                    v_isShared_2684_ = v_isSharedCheck_2701_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___f_2685_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__0;
                v___f_2686_ = l_Std_Http_Protocol_H1_Reader_addHeader___closed__1;
                v_i_2687_ = lean_array_get_size(v_entries_2680_);
                v_f_2688_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Protocol_H1_Reader_addHeader___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2688_, 0, v_i_2687_);
                crate::leanh::lean_inc_ref(v_name_2618_);
                v___x_2689_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2689_, 0, v_name_2618_);
                crate::leanh::lean_ctor_set(v___x_2689_, 1, v_value_2619_);
                v_entries_2690_ = lean_array_push(v_entries_2680_, v___x_2689_);
                v_indexes_2691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2685_,
                    v___f_2686_,
                    v_indexes_2681_,
                    v_name_2618_,
                    v_f_2688_,
                );
                if v_isShared_2684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2683_, 1, v_indexes_2691_);
                    crate::leanh::lean_ctor_set(v___x_2683_, 0, v_entries_2690_);
                    v___x_2693_ = v___x_2683_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_entries_2690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_indexes_2691_);
                    v___x_2693_ = v_reuseFailAlloc_2700_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2678_, 1, v___x_2693_);
                    v___x_2695_ = v___x_2678_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_status_2674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2693_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2699_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_version_2675_,
                    );
                    v___x_2695_ = v_reuseFailAlloc_2699_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2672_, 2, v___x_2695_);
                    v___x_2697_ = v___x_2672_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2698_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_state_2665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_input_2666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 2, v___x_2695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_messageCount_2667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_bodyBytesRead_2668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_headerBytesRead_2669_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2698_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2706_: *mut crate::leanh::LeanObject,
    mut v_name_2707_: *mut crate::leanh::LeanObject,
    mut v_value_2708_: *mut crate::leanh::LeanObject,
    mut v_reader_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2710_: u8 = 0;
    let mut v_res_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2710_ = (crate::leanh::lean_unbox(v_dir_2706_) as u8);
    v_res_2711_ = l_Std_Http_Protocol_H1_Reader_addHeader(
        v_dir_boxed_2710_,
        v_name_2707_,
        v_value_2708_,
        v_reader_2709_,
    );
    return v_res_2711_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_close___redArg(
    mut v_reader_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_unused_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2713_ = crate::leanh::lean_ctor_get(v_reader_2712_, 1);
                v_messageHead_2714_ = crate::leanh::lean_ctor_get(v_reader_2712_, 2);
                v_messageCount_2715_ = crate::leanh::lean_ctor_get(v_reader_2712_, 3);
                v_bodyBytesRead_2716_ = crate::leanh::lean_ctor_get(v_reader_2712_, 4);
                v_headerBytesRead_2717_ = crate::leanh::lean_ctor_get(v_reader_2712_, 5);
                v_isSharedCheck_2726_ = (!crate::leanh::lean_is_exclusive(v_reader_2712_)) as u8;
                if v_isSharedCheck_2726_ == 0 {
                    v_unused_2727_ = crate::leanh::lean_ctor_get(v_reader_2712_, 0);
                    crate::leanh::lean_dec(v_unused_2727_);
                    v___x_2719_ = v_reader_2712_;
                    v_isShared_2720_ = v_isSharedCheck_2726_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2717_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2716_);
                    crate::leanh::lean_inc(v_messageCount_2715_);
                    crate::leanh::lean_inc(v_messageHead_2714_);
                    crate::leanh::lean_inc(v_input_2713_);
                    crate::leanh::lean_dec(v_reader_2712_);
                    v___x_2719_ = crate::leanh::lean_box(0);
                    v_isShared_2720_ = v_isSharedCheck_2726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2721_ = crate::leanh::lean_box(6);
                v___x_2722_ = 1;
                if v_isShared_2720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2719_, 0, v___x_2721_);
                    v___x_2724_ = v___x_2719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_input_2713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_messageHead_2714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_messageCount_2715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_bodyBytesRead_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_headerBytesRead_2717_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2724_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_reader_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2737_: u8 = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v_unused_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2730_ = crate::leanh::lean_ctor_get(v_reader_2729_, 1);
                v_messageHead_2731_ = crate::leanh::lean_ctor_get(v_reader_2729_, 2);
                v_messageCount_2732_ = crate::leanh::lean_ctor_get(v_reader_2729_, 3);
                v_bodyBytesRead_2733_ = crate::leanh::lean_ctor_get(v_reader_2729_, 4);
                v_headerBytesRead_2734_ = crate::leanh::lean_ctor_get(v_reader_2729_, 5);
                v_isSharedCheck_2743_ = (!crate::leanh::lean_is_exclusive(v_reader_2729_)) as u8;
                if v_isSharedCheck_2743_ == 0 {
                    v_unused_2744_ = crate::leanh::lean_ctor_get(v_reader_2729_, 0);
                    crate::leanh::lean_dec(v_unused_2744_);
                    v___x_2736_ = v_reader_2729_;
                    v_isShared_2737_ = v_isSharedCheck_2743_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2734_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2733_);
                    crate::leanh::lean_inc(v_messageCount_2732_);
                    crate::leanh::lean_inc(v_messageHead_2731_);
                    crate::leanh::lean_inc(v_input_2730_);
                    crate::leanh::lean_dec(v_reader_2729_);
                    v___x_2736_ = crate::leanh::lean_box(0);
                    v_isShared_2737_ = v_isSharedCheck_2743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2738_ = crate::leanh::lean_box(6);
                v___x_2739_ = 1;
                if v_isShared_2737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2736_, 0, v___x_2738_);
                    v___x_2741_ = v___x_2736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_input_2730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_messageHead_2731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_messageCount_2732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_bodyBytesRead_2733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_headerBytesRead_2734_);
                    v___x_2741_ = v_reuseFailAlloc_2742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v___x_2739_,
                );
                return v___x_2741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_close___boxed(
    mut v_dir_2745_: *mut crate::leanh::LeanObject,
    mut v_reader_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2747_: u8 = 0;
    let mut v_res_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2747_ = (crate::leanh::lean_unbox(v_dir_2745_) as u8);
    v_res_2748_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_2747_, v_reader_2746_);
    return v_res_2748_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markComplete___redArg(
    mut v_reader_2749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2755_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_unused_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2750_ = crate::leanh::lean_ctor_get(v_reader_2749_, 1);
                v_messageHead_2751_ = crate::leanh::lean_ctor_get(v_reader_2749_, 2);
                v_messageCount_2752_ = crate::leanh::lean_ctor_get(v_reader_2749_, 3);
                v_bodyBytesRead_2753_ = crate::leanh::lean_ctor_get(v_reader_2749_, 4);
                v_headerBytesRead_2754_ = crate::leanh::lean_ctor_get(v_reader_2749_, 5);
                v_noMoreInput_2755_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2749_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2765_ = (!crate::leanh::lean_is_exclusive(v_reader_2749_)) as u8;
                if v_isSharedCheck_2765_ == 0 {
                    v_unused_2766_ = crate::leanh::lean_ctor_get(v_reader_2749_, 0);
                    crate::leanh::lean_dec(v_unused_2766_);
                    v___x_2757_ = v_reader_2749_;
                    v_isShared_2758_ = v_isSharedCheck_2765_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2754_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2753_);
                    crate::leanh::lean_inc(v_messageCount_2752_);
                    crate::leanh::lean_inc(v_messageHead_2751_);
                    crate::leanh::lean_inc(v_input_2750_);
                    crate::leanh::lean_dec(v_reader_2749_);
                    v___x_2757_ = crate::leanh::lean_box(0);
                    v_isShared_2758_ = v_isSharedCheck_2765_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2759_ = crate::leanh::lean_box(5);
                v___x_2760_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2761_ = lean_nat_add(v_messageCount_2752_, v___x_2760_);
                crate::leanh::lean_dec(v_messageCount_2752_);
                if v_isShared_2758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2757_, 3, v___x_2761_);
                    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2759_);
                    v___x_2763_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_input_2750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_messageHead_2751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 3, v___x_2761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 4, v_bodyBytesRead_2753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 5, v_headerBytesRead_2754_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2764_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_reader_2768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2774_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_unused_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2769_ = crate::leanh::lean_ctor_get(v_reader_2768_, 1);
                v_messageHead_2770_ = crate::leanh::lean_ctor_get(v_reader_2768_, 2);
                v_messageCount_2771_ = crate::leanh::lean_ctor_get(v_reader_2768_, 3);
                v_bodyBytesRead_2772_ = crate::leanh::lean_ctor_get(v_reader_2768_, 4);
                v_headerBytesRead_2773_ = crate::leanh::lean_ctor_get(v_reader_2768_, 5);
                v_noMoreInput_2774_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2768_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2784_ = (!crate::leanh::lean_is_exclusive(v_reader_2768_)) as u8;
                if v_isSharedCheck_2784_ == 0 {
                    v_unused_2785_ = crate::leanh::lean_ctor_get(v_reader_2768_, 0);
                    crate::leanh::lean_dec(v_unused_2785_);
                    v___x_2776_ = v_reader_2768_;
                    v_isShared_2777_ = v_isSharedCheck_2784_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2773_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2772_);
                    crate::leanh::lean_inc(v_messageCount_2771_);
                    crate::leanh::lean_inc(v_messageHead_2770_);
                    crate::leanh::lean_inc(v_input_2769_);
                    crate::leanh::lean_dec(v_reader_2768_);
                    v___x_2776_ = crate::leanh::lean_box(0);
                    v_isShared_2777_ = v_isSharedCheck_2784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2778_ = crate::leanh::lean_box(5);
                v___x_2779_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2780_ = lean_nat_add(v_messageCount_2771_, v___x_2779_);
                crate::leanh::lean_dec(v_messageCount_2771_);
                if v_isShared_2777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2776_, 3, v___x_2780_);
                    crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2778_);
                    v___x_2782_ = v___x_2776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_input_2769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 2, v_messageHead_2770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 3, v___x_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 4, v_bodyBytesRead_2772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 5, v_headerBytesRead_2773_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2783_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2786_: *mut crate::leanh::LeanObject,
    mut v_reader_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2788_: u8 = 0;
    let mut v_res_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2788_ = (crate::leanh::lean_unbox(v_dir_2786_) as u8);
    v_res_2789_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_2788_, v_reader_2787_);
    return v_res_2789_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_fail___redArg(
    mut v_error_2790_: *mut crate::leanh::LeanObject,
    mut v_reader_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2797_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_unused_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2792_ = crate::leanh::lean_ctor_get(v_reader_2791_, 1);
                v_messageHead_2793_ = crate::leanh::lean_ctor_get(v_reader_2791_, 2);
                v_messageCount_2794_ = crate::leanh::lean_ctor_get(v_reader_2791_, 3);
                v_bodyBytesRead_2795_ = crate::leanh::lean_ctor_get(v_reader_2791_, 4);
                v_headerBytesRead_2796_ = crate::leanh::lean_ctor_get(v_reader_2791_, 5);
                v_noMoreInput_2797_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2791_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2805_ = (!crate::leanh::lean_is_exclusive(v_reader_2791_)) as u8;
                if v_isSharedCheck_2805_ == 0 {
                    v_unused_2806_ = crate::leanh::lean_ctor_get(v_reader_2791_, 0);
                    crate::leanh::lean_dec(v_unused_2806_);
                    v___x_2799_ = v_reader_2791_;
                    v_isShared_2800_ = v_isSharedCheck_2805_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2796_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2795_);
                    crate::leanh::lean_inc(v_messageCount_2794_);
                    crate::leanh::lean_inc(v_messageHead_2793_);
                    crate::leanh::lean_inc(v_input_2792_);
                    crate::leanh::lean_dec(v_reader_2791_);
                    v___x_2799_ = crate::leanh::lean_box(0);
                    v_isShared_2800_ = v_isSharedCheck_2805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2801_ = crate::leanh::lean_alloc_ctor(7, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2801_, 0, v_error_2790_);
                if v_isShared_2800_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2801_);
                    v___x_2803_ = v___x_2799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_input_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 2, v_messageHead_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 3, v_messageCount_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 4, v_bodyBytesRead_2795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 5, v_headerBytesRead_2796_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2804_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_error_2808_: *mut crate::leanh::LeanObject,
    mut v_reader_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2815_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2810_ = crate::leanh::lean_ctor_get(v_reader_2809_, 1);
                v_messageHead_2811_ = crate::leanh::lean_ctor_get(v_reader_2809_, 2);
                v_messageCount_2812_ = crate::leanh::lean_ctor_get(v_reader_2809_, 3);
                v_bodyBytesRead_2813_ = crate::leanh::lean_ctor_get(v_reader_2809_, 4);
                v_headerBytesRead_2814_ = crate::leanh::lean_ctor_get(v_reader_2809_, 5);
                v_noMoreInput_2815_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2823_ = (!crate::leanh::lean_is_exclusive(v_reader_2809_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = crate::leanh::lean_ctor_get(v_reader_2809_, 0);
                    crate::leanh::lean_dec(v_unused_2824_);
                    v___x_2817_ = v_reader_2809_;
                    v_isShared_2818_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2814_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2813_);
                    crate::leanh::lean_inc(v_messageCount_2812_);
                    crate::leanh::lean_inc(v_messageHead_2811_);
                    crate::leanh::lean_inc(v_input_2810_);
                    crate::leanh::lean_dec(v_reader_2809_);
                    v___x_2817_ = crate::leanh::lean_box(0);
                    v_isShared_2818_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2819_ = crate::leanh::lean_alloc_ctor(7, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2819_, 0, v_error_2808_);
                if v_isShared_2818_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2817_, 0, v___x_2819_);
                    v___x_2821_ = v___x_2817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_input_2810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_messageHead_2811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_messageCount_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_bodyBytesRead_2813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_headerBytesRead_2814_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2822_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2825_: *mut crate::leanh::LeanObject,
    mut v_error_2826_: *mut crate::leanh::LeanObject,
    mut v_reader_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2828_: u8 = 0;
    let mut v_res_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2828_ = (crate::leanh::lean_unbox(v_dir_2825_) as u8);
    v_res_2829_ =
        l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_2828_, v_error_2826_, v_reader_2827_);
    return v_res_2829_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_reset(
    mut v_dir_2830_: u8,
    mut v_reader_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2834_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2832_ = crate::leanh::lean_ctor_get(v_reader_2831_, 1);
                v_messageCount_2833_ = crate::leanh::lean_ctor_get(v_reader_2831_, 3);
                v_noMoreInput_2834_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2831_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2844_ = (!crate::leanh::lean_is_exclusive(v_reader_2831_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v_unused_2845_ = crate::leanh::lean_ctor_get(v_reader_2831_, 5);
                    crate::leanh::lean_dec(v_unused_2845_);
                    v_unused_2846_ = crate::leanh::lean_ctor_get(v_reader_2831_, 4);
                    crate::leanh::lean_dec(v_unused_2846_);
                    v_unused_2847_ = crate::leanh::lean_ctor_get(v_reader_2831_, 2);
                    crate::leanh::lean_dec(v_unused_2847_);
                    v_unused_2848_ = crate::leanh::lean_ctor_get(v_reader_2831_, 0);
                    crate::leanh::lean_dec(v_unused_2848_);
                    v___x_2836_ = v_reader_2831_;
                    v_isShared_2837_ = v_isSharedCheck_2844_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_messageCount_2833_);
                    crate::leanh::lean_inc(v_input_2832_);
                    crate::leanh::lean_dec(v_reader_2831_);
                    v___x_2836_ = crate::leanh::lean_box(0);
                    v_isShared_2837_ = v_isSharedCheck_2844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2838_ = crate::leanh::lean_box(0);
                v___x_2839_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_2830_);
                v___x_2840_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_2837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2836_, 5, v___x_2840_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 4, v___x_2840_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 2, v___x_2839_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 0, v___x_2838_);
                    v___x_2842_ = v___x_2836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_input_2832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v___x_2839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_messageCount_2833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v___x_2840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 5, v___x_2840_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2843_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2849_: *mut crate::leanh::LeanObject,
    mut v_reader_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2851_: u8 = 0;
    let mut v_res_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2851_ = (crate::leanh::lean_unbox(v_dir_2849_) as u8);
    v_res_2852_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_2851_, v_reader_2850_);
    return v_res_2852_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(
    mut v_reader_2853_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2856_: u8 = 0;
    let mut v___y_2858_: u8 = 0;
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: u8 = 0;
    let mut v_array_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2854_ = crate::leanh::lean_ctor_get(v_reader_2853_, 0);
                v_input_2855_ = crate::leanh::lean_ctor_get(v_reader_2853_, 1);
                v_noMoreInput_2856_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_array_2863_ = crate::leanh::lean_ctor_get(v_input_2855_, 0);
                v_idx_2864_ = crate::leanh::lean_ctor_get(v_input_2855_, 1);
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
                    match crate::leanh::lean_obj_tag(v_state_2854_) {
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
    mut v_reader_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2869_: u8 = 0;
    let mut v_r_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_2868_);
    crate::leanh::lean_dec_ref(v_reader_2868_);
    v_r_2870_ = crate::leanh::lean_box((v_res_2869_) as usize);
    return v_r_2870_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_needsMoreInput(
    mut v_dir_2871_: u8,
    mut v_reader_2872_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_state_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2875_: u8 = 0;
    let mut v___y_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: u8 = 0;
    let mut v_array_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2873_ = crate::leanh::lean_ctor_get(v_reader_2872_, 0);
                v_input_2874_ = crate::leanh::lean_ctor_get(v_reader_2872_, 1);
                v_noMoreInput_2875_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_array_2882_ = crate::leanh::lean_ctor_get(v_input_2874_, 0);
                v_idx_2883_ = crate::leanh::lean_ctor_get(v_input_2874_, 1);
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
                    match crate::leanh::lean_obj_tag(v_state_2873_) {
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
    mut v_dir_2887_: *mut crate::leanh::LeanObject,
    mut v_reader_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2889_: u8 = 0;
    let mut v_res_2890_: u8 = 0;
    let mut v_r_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2889_ = (crate::leanh::lean_unbox(v_dir_2887_) as u8);
    v_res_2890_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_2889_, v_reader_2888_);
    crate::leanh::lean_dec_ref(v_reader_2888_);
    v_r_2891_ = crate::leanh::lean_box((v_res_2890_) as usize);
    return v_r_2891_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_getError___redArg(
    mut v_reader_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2893_ = crate::leanh::lean_ctor_get(v_reader_2892_, 0);
                crate::leanh::lean_inc(v_state_2893_);
                crate::leanh::lean_dec_ref(v_reader_2892_);
                if crate::leanh::lean_obj_tag(v_state_2893_) == 7 {
                    v_error_2894_ = crate::leanh::lean_ctor_get(v_state_2893_, 0);
                    v_isSharedCheck_2901_ = (!crate::leanh::lean_is_exclusive(v_state_2893_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v_state_2893_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_error_2894_);
                        crate::leanh::lean_dec(v_state_2893_);
                        v___x_2896_ = crate::leanh::lean_box(0);
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_state_2893_);
                    v___x_2902_ = crate::leanh::lean_box(0);
                    return v___x_2902_;
                }
            }
            1 => {
                if v_isShared_2897_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2896_, 1);
                    v___x_2899_ = v___x_2896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_error_2894_);
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
    mut v_reader_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_2905_ = crate::leanh::lean_ctor_get(v_reader_2904_, 0);
                crate::leanh::lean_inc(v_state_2905_);
                crate::leanh::lean_dec_ref(v_reader_2904_);
                if crate::leanh::lean_obj_tag(v_state_2905_) == 7 {
                    v_error_2906_ = crate::leanh::lean_ctor_get(v_state_2905_, 0);
                    v_isSharedCheck_2913_ = (!crate::leanh::lean_is_exclusive(v_state_2905_)) as u8;
                    if v_isSharedCheck_2913_ == 0 {
                        v___x_2908_ = v_state_2905_;
                        v_isShared_2909_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_error_2906_);
                        crate::leanh::lean_dec(v_state_2905_);
                        v___x_2908_ = crate::leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_state_2905_);
                    v___x_2914_ = crate::leanh::lean_box(0);
                    return v___x_2914_;
                }
            }
            1 => {
                if v_isShared_2909_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2908_, 1);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_error_2906_);
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
    mut v_dir_2915_: *mut crate::leanh::LeanObject,
    mut v_reader_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2917_: u8 = 0;
    let mut v_res_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2917_ = (crate::leanh::lean_unbox(v_dir_2915_) as u8);
    v_res_2918_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_2917_, v_reader_2916_);
    return v_res_2918_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(
    mut v_reader_2919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_input_2920_ = crate::leanh::lean_ctor_get(v_reader_2919_, 1);
    v_array_2921_ = crate::leanh::lean_ctor_get(v_input_2920_, 0);
    v_idx_2922_ = crate::leanh::lean_ctor_get(v_input_2920_, 1);
    v___x_2923_ = lean_byte_array_size(v_array_2921_);
    v___x_2924_ = lean_nat_sub(v___x_2923_, v_idx_2922_);
    return v___x_2924_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(
    mut v_reader_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_2925_);
    crate::leanh::lean_dec_ref(v_reader_2925_);
    return v_res_2926_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes(
    mut v_dir_2927_: u8,
    mut v_reader_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_input_2929_ = crate::leanh::lean_ctor_get(v_reader_2928_, 1);
    v_array_2930_ = crate::leanh::lean_ctor_get(v_input_2929_, 0);
    v_idx_2931_ = crate::leanh::lean_ctor_get(v_input_2929_, 1);
    v___x_2932_ = lean_byte_array_size(v_array_2930_);
    v___x_2933_ = lean_nat_sub(v___x_2932_, v_idx_2931_);
    return v___x_2933_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(
    mut v_dir_2934_: *mut crate::leanh::LeanObject,
    mut v_reader_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2936_: u8 = 0;
    let mut v_res_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2936_ = (crate::leanh::lean_unbox(v_dir_2934_) as u8);
    v_res_2937_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_2936_, v_reader_2935_);
    crate::leanh::lean_dec_ref(v_reader_2935_);
    return v_res_2937_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance___redArg(
    mut v_n_2938_: *mut crate::leanh::LeanObject,
    mut v_reader_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2946_: u8 = 0;
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v_array_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2940_ = crate::leanh::lean_ctor_get(v_reader_2939_, 1);
                v_state_2941_ = crate::leanh::lean_ctor_get(v_reader_2939_, 0);
                v_messageHead_2942_ = crate::leanh::lean_ctor_get(v_reader_2939_, 2);
                v_messageCount_2943_ = crate::leanh::lean_ctor_get(v_reader_2939_, 3);
                v_bodyBytesRead_2944_ = crate::leanh::lean_ctor_get(v_reader_2939_, 4);
                v_headerBytesRead_2945_ = crate::leanh::lean_ctor_get(v_reader_2939_, 5);
                v_noMoreInput_2946_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2939_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2963_ = (!crate::leanh::lean_is_exclusive(v_reader_2939_)) as u8;
                if v_isSharedCheck_2963_ == 0 {
                    v___x_2948_ = v_reader_2939_;
                    v_isShared_2949_ = v_isSharedCheck_2963_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2945_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2944_);
                    crate::leanh::lean_inc(v_messageCount_2943_);
                    crate::leanh::lean_inc(v_messageHead_2942_);
                    crate::leanh::lean_inc(v_input_2940_);
                    crate::leanh::lean_inc(v_state_2941_);
                    crate::leanh::lean_dec(v_reader_2939_);
                    v___x_2948_ = crate::leanh::lean_box(0);
                    v_isShared_2949_ = v_isSharedCheck_2963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2950_ = crate::leanh::lean_ctor_get(v_input_2940_, 0);
                v_idx_2951_ = crate::leanh::lean_ctor_get(v_input_2940_, 1);
                v_isSharedCheck_2962_ = (!crate::leanh::lean_is_exclusive(v_input_2940_)) as u8;
                if v_isSharedCheck_2962_ == 0 {
                    v___x_2953_ = v_input_2940_;
                    v_isShared_2954_ = v_isSharedCheck_2962_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_2951_);
                    crate::leanh::lean_inc(v_array_2950_);
                    crate::leanh::lean_dec(v_input_2940_);
                    v___x_2953_ = crate::leanh::lean_box(0);
                    v_isShared_2954_ = v_isSharedCheck_2962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2955_ = lean_nat_add(v_idx_2951_, v_n_2938_);
                crate::leanh::lean_dec(v_idx_2951_);
                if v_isShared_2954_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2953_, 1, v___x_2955_);
                    v___x_2957_ = v___x_2953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_array_2950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2955_);
                    v___x_2957_ = v_reuseFailAlloc_2961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2948_, 1, v___x_2957_);
                    v___x_2959_ = v___x_2948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_state_2941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_messageHead_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_messageCount_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_bodyBytesRead_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_headerBytesRead_2945_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_n_2964_: *mut crate::leanh::LeanObject,
    mut v_reader_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_2964_, v_reader_2965_);
    crate::leanh::lean_dec(v_n_2964_);
    return v_res_2966_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_advance(
    mut v_dir_2967_: u8,
    mut v_n_2968_: *mut crate::leanh::LeanObject,
    mut v_reader_2969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_2976_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_array_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v_isSharedCheck_2993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_2970_ = crate::leanh::lean_ctor_get(v_reader_2969_, 1);
                v_state_2971_ = crate::leanh::lean_ctor_get(v_reader_2969_, 0);
                v_messageHead_2972_ = crate::leanh::lean_ctor_get(v_reader_2969_, 2);
                v_messageCount_2973_ = crate::leanh::lean_ctor_get(v_reader_2969_, 3);
                v_bodyBytesRead_2974_ = crate::leanh::lean_ctor_get(v_reader_2969_, 4);
                v_headerBytesRead_2975_ = crate::leanh::lean_ctor_get(v_reader_2969_, 5);
                v_noMoreInput_2976_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_2969_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_2993_ = (!crate::leanh::lean_is_exclusive(v_reader_2969_)) as u8;
                if v_isSharedCheck_2993_ == 0 {
                    v___x_2978_ = v_reader_2969_;
                    v_isShared_2979_ = v_isSharedCheck_2993_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_2975_);
                    crate::leanh::lean_inc(v_bodyBytesRead_2974_);
                    crate::leanh::lean_inc(v_messageCount_2973_);
                    crate::leanh::lean_inc(v_messageHead_2972_);
                    crate::leanh::lean_inc(v_input_2970_);
                    crate::leanh::lean_inc(v_state_2971_);
                    crate::leanh::lean_dec(v_reader_2969_);
                    v___x_2978_ = crate::leanh::lean_box(0);
                    v_isShared_2979_ = v_isSharedCheck_2993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_array_2980_ = crate::leanh::lean_ctor_get(v_input_2970_, 0);
                v_idx_2981_ = crate::leanh::lean_ctor_get(v_input_2970_, 1);
                v_isSharedCheck_2992_ = (!crate::leanh::lean_is_exclusive(v_input_2970_)) as u8;
                if v_isSharedCheck_2992_ == 0 {
                    v___x_2983_ = v_input_2970_;
                    v_isShared_2984_ = v_isSharedCheck_2992_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_2981_);
                    crate::leanh::lean_inc(v_array_2980_);
                    crate::leanh::lean_dec(v_input_2970_);
                    v___x_2983_ = crate::leanh::lean_box(0);
                    v_isShared_2984_ = v_isSharedCheck_2992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2985_ = lean_nat_add(v_idx_2981_, v_n_2968_);
                crate::leanh::lean_dec(v_idx_2981_);
                if v_isShared_2984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2983_, 1, v___x_2985_);
                    v___x_2987_ = v___x_2983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_array_2980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2985_);
                    v___x_2987_ = v_reuseFailAlloc_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2978_, 1, v___x_2987_);
                    v___x_2989_ = v___x_2978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_state_2971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_messageHead_2972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_messageCount_2973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_bodyBytesRead_2974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_headerBytesRead_2975_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2990_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_2994_: *mut crate::leanh::LeanObject,
    mut v_n_2995_: *mut crate::leanh::LeanObject,
    mut v_reader_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_2997_: u8 = 0;
    let mut v_res_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_2997_ = (crate::leanh::lean_unbox(v_dir_2994_) as u8);
    v_res_2998_ =
        l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_2997_, v_n_2995_, v_reader_2996_);
    crate::leanh::lean_dec(v_n_2995_);
    return v_res_2998_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(
    mut v_reader_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3005_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3002_ = crate::leanh::lean_ctor_get(v_reader_3001_, 1);
                v_messageHead_3003_ = crate::leanh::lean_ctor_get(v_reader_3001_, 2);
                v_messageCount_3004_ = crate::leanh::lean_ctor_get(v_reader_3001_, 3);
                v_noMoreInput_3005_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3001_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3014_ = (!crate::leanh::lean_is_exclusive(v_reader_3001_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v_unused_3015_ = crate::leanh::lean_ctor_get(v_reader_3001_, 5);
                    crate::leanh::lean_dec(v_unused_3015_);
                    v_unused_3016_ = crate::leanh::lean_ctor_get(v_reader_3001_, 4);
                    crate::leanh::lean_dec(v_unused_3016_);
                    v_unused_3017_ = crate::leanh::lean_ctor_get(v_reader_3001_, 0);
                    crate::leanh::lean_dec(v_unused_3017_);
                    v___x_3007_ = v_reader_3001_;
                    v_isShared_3008_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_messageCount_3004_);
                    crate::leanh::lean_inc(v_messageHead_3003_);
                    crate::leanh::lean_inc(v_input_3002_);
                    crate::leanh::lean_dec(v_reader_3001_);
                    v___x_3007_ = crate::leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3009_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3010_ = l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0;
                if v_isShared_3008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3007_, 5, v___x_3009_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 4, v___x_3009_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 0, v___x_3010_);
                    v___x_3012_ = v___x_3007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_input_3002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_messageHead_3003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_messageCount_3004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 4, v___x_3009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 5, v___x_3009_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3013_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_reader_3019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3023_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_unused_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3020_ = crate::leanh::lean_ctor_get(v_reader_3019_, 1);
                v_messageHead_3021_ = crate::leanh::lean_ctor_get(v_reader_3019_, 2);
                v_messageCount_3022_ = crate::leanh::lean_ctor_get(v_reader_3019_, 3);
                v_noMoreInput_3023_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3019_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3032_ = (!crate::leanh::lean_is_exclusive(v_reader_3019_)) as u8;
                if v_isSharedCheck_3032_ == 0 {
                    v_unused_3033_ = crate::leanh::lean_ctor_get(v_reader_3019_, 5);
                    crate::leanh::lean_dec(v_unused_3033_);
                    v_unused_3034_ = crate::leanh::lean_ctor_get(v_reader_3019_, 4);
                    crate::leanh::lean_dec(v_unused_3034_);
                    v_unused_3035_ = crate::leanh::lean_ctor_get(v_reader_3019_, 0);
                    crate::leanh::lean_dec(v_unused_3035_);
                    v___x_3025_ = v_reader_3019_;
                    v_isShared_3026_ = v_isSharedCheck_3032_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_messageCount_3022_);
                    crate::leanh::lean_inc(v_messageHead_3021_);
                    crate::leanh::lean_inc(v_input_3020_);
                    crate::leanh::lean_dec(v_reader_3019_);
                    v___x_3025_ = crate::leanh::lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3027_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3028_ = l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0;
                if v_isShared_3026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3025_, 5, v___x_3027_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 4, v___x_3027_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_3028_);
                    v___x_3030_ = v___x_3025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_input_3020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_messageHead_3021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_messageCount_3022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 4, v___x_3027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 5, v___x_3027_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3031_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_3036_: *mut crate::leanh::LeanObject,
    mut v_reader_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3038_: u8 = 0;
    let mut v_res_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3038_ = (crate::leanh::lean_unbox(v_dir_3036_) as u8);
    v_res_3039_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_3038_, v_reader_3037_);
    return v_res_3039_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(
    mut v_n_3040_: *mut crate::leanh::LeanObject,
    mut v_reader_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3048_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3042_ = crate::leanh::lean_ctor_get(v_reader_3041_, 0);
                v_input_3043_ = crate::leanh::lean_ctor_get(v_reader_3041_, 1);
                v_messageHead_3044_ = crate::leanh::lean_ctor_get(v_reader_3041_, 2);
                v_messageCount_3045_ = crate::leanh::lean_ctor_get(v_reader_3041_, 3);
                v_bodyBytesRead_3046_ = crate::leanh::lean_ctor_get(v_reader_3041_, 4);
                v_headerBytesRead_3047_ = crate::leanh::lean_ctor_get(v_reader_3041_, 5);
                v_noMoreInput_3048_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3041_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3056_ = (!crate::leanh::lean_is_exclusive(v_reader_3041_)) as u8;
                if v_isSharedCheck_3056_ == 0 {
                    v___x_3050_ = v_reader_3041_;
                    v_isShared_3051_ = v_isSharedCheck_3056_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3047_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3046_);
                    crate::leanh::lean_inc(v_messageCount_3045_);
                    crate::leanh::lean_inc(v_messageHead_3044_);
                    crate::leanh::lean_inc(v_input_3043_);
                    crate::leanh::lean_inc(v_state_3042_);
                    crate::leanh::lean_dec(v_reader_3041_);
                    v___x_3050_ = crate::leanh::lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3052_ = lean_nat_add(v_bodyBytesRead_3046_, v_n_3040_);
                crate::leanh::lean_dec(v_bodyBytesRead_3046_);
                if v_isShared_3051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3050_, 4, v___x_3052_);
                    v___x_3054_ = v___x_3050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_state_3042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_input_3043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_messageHead_3044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_messageCount_3045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 4, v___x_3052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 5, v_headerBytesRead_3047_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_n_3057_: *mut crate::leanh::LeanObject,
    mut v_reader_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_3057_, v_reader_3058_);
    crate::leanh::lean_dec(v_n_3057_);
    return v_res_3059_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addBodyBytes(
    mut v_dir_3060_: u8,
    mut v_n_3061_: *mut crate::leanh::LeanObject,
    mut v_reader_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3069_: u8 = 0;
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3063_ = crate::leanh::lean_ctor_get(v_reader_3062_, 0);
                v_input_3064_ = crate::leanh::lean_ctor_get(v_reader_3062_, 1);
                v_messageHead_3065_ = crate::leanh::lean_ctor_get(v_reader_3062_, 2);
                v_messageCount_3066_ = crate::leanh::lean_ctor_get(v_reader_3062_, 3);
                v_bodyBytesRead_3067_ = crate::leanh::lean_ctor_get(v_reader_3062_, 4);
                v_headerBytesRead_3068_ = crate::leanh::lean_ctor_get(v_reader_3062_, 5);
                v_noMoreInput_3069_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3077_ = (!crate::leanh::lean_is_exclusive(v_reader_3062_)) as u8;
                if v_isSharedCheck_3077_ == 0 {
                    v___x_3071_ = v_reader_3062_;
                    v_isShared_3072_ = v_isSharedCheck_3077_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3068_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3067_);
                    crate::leanh::lean_inc(v_messageCount_3066_);
                    crate::leanh::lean_inc(v_messageHead_3065_);
                    crate::leanh::lean_inc(v_input_3064_);
                    crate::leanh::lean_inc(v_state_3063_);
                    crate::leanh::lean_dec(v_reader_3062_);
                    v___x_3071_ = crate::leanh::lean_box(0);
                    v_isShared_3072_ = v_isSharedCheck_3077_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3073_ = lean_nat_add(v_bodyBytesRead_3067_, v_n_3061_);
                crate::leanh::lean_dec(v_bodyBytesRead_3067_);
                if v_isShared_3072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3071_, 4, v___x_3073_);
                    v___x_3075_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_state_3063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_input_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_messageHead_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_messageCount_3066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 5, v_headerBytesRead_3068_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3076_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_3078_: *mut crate::leanh::LeanObject,
    mut v_n_3079_: *mut crate::leanh::LeanObject,
    mut v_reader_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3081_ = (crate::leanh::lean_unbox(v_dir_3078_) as u8);
    v_res_3082_ =
        l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_3081_, v_n_3079_, v_reader_3080_);
    crate::leanh::lean_dec(v_n_3079_);
    return v_res_3082_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(
    mut v_n_3083_: *mut crate::leanh::LeanObject,
    mut v_reader_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3091_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3085_ = crate::leanh::lean_ctor_get(v_reader_3084_, 0);
                v_input_3086_ = crate::leanh::lean_ctor_get(v_reader_3084_, 1);
                v_messageHead_3087_ = crate::leanh::lean_ctor_get(v_reader_3084_, 2);
                v_messageCount_3088_ = crate::leanh::lean_ctor_get(v_reader_3084_, 3);
                v_bodyBytesRead_3089_ = crate::leanh::lean_ctor_get(v_reader_3084_, 4);
                v_headerBytesRead_3090_ = crate::leanh::lean_ctor_get(v_reader_3084_, 5);
                v_noMoreInput_3091_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3084_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3099_ = (!crate::leanh::lean_is_exclusive(v_reader_3084_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3093_ = v_reader_3084_;
                    v_isShared_3094_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3090_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3089_);
                    crate::leanh::lean_inc(v_messageCount_3088_);
                    crate::leanh::lean_inc(v_messageHead_3087_);
                    crate::leanh::lean_inc(v_input_3086_);
                    crate::leanh::lean_inc(v_state_3085_);
                    crate::leanh::lean_dec(v_reader_3084_);
                    v___x_3093_ = crate::leanh::lean_box(0);
                    v_isShared_3094_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3095_ = lean_nat_add(v_headerBytesRead_3090_, v_n_3083_);
                crate::leanh::lean_dec(v_headerBytesRead_3090_);
                if v_isShared_3094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3093_, 5, v___x_3095_);
                    v___x_3097_ = v___x_3093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_state_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_input_3086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_messageHead_3087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_messageCount_3088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_bodyBytesRead_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 5, v___x_3095_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3098_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_n_3100_: *mut crate::leanh::LeanObject,
    mut v_reader_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3102_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_3100_, v_reader_3101_);
    crate::leanh::lean_dec(v_n_3100_);
    return v_res_3102_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_addHeaderBytes(
    mut v_dir_3103_: u8,
    mut v_n_3104_: *mut crate::leanh::LeanObject,
    mut v_reader_3105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3112_: u8 = 0;
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3106_ = crate::leanh::lean_ctor_get(v_reader_3105_, 0);
                v_input_3107_ = crate::leanh::lean_ctor_get(v_reader_3105_, 1);
                v_messageHead_3108_ = crate::leanh::lean_ctor_get(v_reader_3105_, 2);
                v_messageCount_3109_ = crate::leanh::lean_ctor_get(v_reader_3105_, 3);
                v_bodyBytesRead_3110_ = crate::leanh::lean_ctor_get(v_reader_3105_, 4);
                v_headerBytesRead_3111_ = crate::leanh::lean_ctor_get(v_reader_3105_, 5);
                v_noMoreInput_3112_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3105_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3120_ = (!crate::leanh::lean_is_exclusive(v_reader_3105_)) as u8;
                if v_isSharedCheck_3120_ == 0 {
                    v___x_3114_ = v_reader_3105_;
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3111_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3110_);
                    crate::leanh::lean_inc(v_messageCount_3109_);
                    crate::leanh::lean_inc(v_messageHead_3108_);
                    crate::leanh::lean_inc(v_input_3107_);
                    crate::leanh::lean_inc(v_state_3106_);
                    crate::leanh::lean_dec(v_reader_3105_);
                    v___x_3114_ = crate::leanh::lean_box(0);
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3116_ = lean_nat_add(v_headerBytesRead_3111_, v_n_3104_);
                crate::leanh::lean_dec(v_headerBytesRead_3111_);
                if v_isShared_3115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3114_, 5, v___x_3116_);
                    v___x_3118_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_state_3106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_input_3107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_messageHead_3108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_messageCount_3109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_bodyBytesRead_3110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 5, v___x_3116_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3119_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_3121_: *mut crate::leanh::LeanObject,
    mut v_n_3122_: *mut crate::leanh::LeanObject,
    mut v_reader_3123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3124_: u8 = 0;
    let mut v_res_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3124_ = (crate::leanh::lean_unbox(v_dir_3121_) as u8);
    v_res_3125_ =
        l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_3124_, v_n_3122_, v_reader_3123_);
    crate::leanh::lean_dec(v_n_3122_);
    return v_res_3125_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(
    mut v_size_3126_: *mut crate::leanh::LeanObject,
    mut v_reader_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3133_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_unused_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3128_ = crate::leanh::lean_ctor_get(v_reader_3127_, 1);
                v_messageHead_3129_ = crate::leanh::lean_ctor_get(v_reader_3127_, 2);
                v_messageCount_3130_ = crate::leanh::lean_ctor_get(v_reader_3127_, 3);
                v_bodyBytesRead_3131_ = crate::leanh::lean_ctor_get(v_reader_3127_, 4);
                v_headerBytesRead_3132_ = crate::leanh::lean_ctor_get(v_reader_3127_, 5);
                v_noMoreInput_3133_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3127_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3142_ = (!crate::leanh::lean_is_exclusive(v_reader_3127_)) as u8;
                if v_isSharedCheck_3142_ == 0 {
                    v_unused_3143_ = crate::leanh::lean_ctor_get(v_reader_3127_, 0);
                    crate::leanh::lean_dec(v_unused_3143_);
                    v___x_3135_ = v_reader_3127_;
                    v_isShared_3136_ = v_isSharedCheck_3142_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3132_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3131_);
                    crate::leanh::lean_inc(v_messageCount_3130_);
                    crate::leanh::lean_inc(v_messageHead_3129_);
                    crate::leanh::lean_inc(v_input_3128_);
                    crate::leanh::lean_dec(v_reader_3127_);
                    v___x_3135_ = crate::leanh::lean_box(0);
                    v_isShared_3136_ = v_isSharedCheck_3142_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3137_, 0, v_size_3126_);
                v___x_3138_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                if v_isShared_3136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3135_, 0, v___x_3138_);
                    v___x_3140_ = v___x_3135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_input_3128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_messageHead_3129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 3, v_messageCount_3130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 4, v_bodyBytesRead_3131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 5, v_headerBytesRead_3132_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_size_3145_: *mut crate::leanh::LeanObject,
    mut v_reader_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3152_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_unused_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3147_ = crate::leanh::lean_ctor_get(v_reader_3146_, 1);
                v_messageHead_3148_ = crate::leanh::lean_ctor_get(v_reader_3146_, 2);
                v_messageCount_3149_ = crate::leanh::lean_ctor_get(v_reader_3146_, 3);
                v_bodyBytesRead_3150_ = crate::leanh::lean_ctor_get(v_reader_3146_, 4);
                v_headerBytesRead_3151_ = crate::leanh::lean_ctor_get(v_reader_3146_, 5);
                v_noMoreInput_3152_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3161_ = (!crate::leanh::lean_is_exclusive(v_reader_3146_)) as u8;
                if v_isSharedCheck_3161_ == 0 {
                    v_unused_3162_ = crate::leanh::lean_ctor_get(v_reader_3146_, 0);
                    crate::leanh::lean_dec(v_unused_3162_);
                    v___x_3154_ = v_reader_3146_;
                    v_isShared_3155_ = v_isSharedCheck_3161_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3151_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3150_);
                    crate::leanh::lean_inc(v_messageCount_3149_);
                    crate::leanh::lean_inc(v_messageHead_3148_);
                    crate::leanh::lean_inc(v_input_3147_);
                    crate::leanh::lean_dec(v_reader_3146_);
                    v___x_3154_ = crate::leanh::lean_box(0);
                    v_isShared_3155_ = v_isSharedCheck_3161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3156_, 0, v_size_3145_);
                v___x_3157_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                if v_isShared_3155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3154_, 0, v___x_3157_);
                    v___x_3159_ = v___x_3154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_input_3147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_messageHead_3148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_messageCount_3149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_bodyBytesRead_3150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 5, v_headerBytesRead_3151_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3160_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_3163_: *mut crate::leanh::LeanObject,
    mut v_size_3164_: *mut crate::leanh::LeanObject,
    mut v_reader_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3166_: u8 = 0;
    let mut v_res_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3166_ = (crate::leanh::lean_unbox(v_dir_3163_) as u8);
    v_res_3167_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(
        v_dir_boxed_3166_,
        v_size_3164_,
        v_reader_3165_,
    );
    return v_res_3167_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(
    mut v_reader_3170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3176_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3179_: u8 = 0;
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_unused_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3171_ = crate::leanh::lean_ctor_get(v_reader_3170_, 1);
                v_messageHead_3172_ = crate::leanh::lean_ctor_get(v_reader_3170_, 2);
                v_messageCount_3173_ = crate::leanh::lean_ctor_get(v_reader_3170_, 3);
                v_bodyBytesRead_3174_ = crate::leanh::lean_ctor_get(v_reader_3170_, 4);
                v_headerBytesRead_3175_ = crate::leanh::lean_ctor_get(v_reader_3170_, 5);
                v_noMoreInput_3176_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3170_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3184_ = (!crate::leanh::lean_is_exclusive(v_reader_3170_)) as u8;
                if v_isSharedCheck_3184_ == 0 {
                    v_unused_3185_ = crate::leanh::lean_ctor_get(v_reader_3170_, 0);
                    crate::leanh::lean_dec(v_unused_3185_);
                    v___x_3178_ = v_reader_3170_;
                    v_isShared_3179_ = v_isSharedCheck_3184_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3175_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3174_);
                    crate::leanh::lean_inc(v_messageCount_3173_);
                    crate::leanh::lean_inc(v_messageHead_3172_);
                    crate::leanh::lean_inc(v_input_3171_);
                    crate::leanh::lean_dec(v_reader_3170_);
                    v___x_3178_ = crate::leanh::lean_box(0);
                    v_isShared_3179_ = v_isSharedCheck_3184_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3180_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0;
                if v_isShared_3179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3178_, 0, v___x_3180_);
                    v___x_3182_ = v___x_3178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_input_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_messageHead_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_messageCount_3173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_bodyBytesRead_3174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_headerBytesRead_3175_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_reader_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_input_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noMoreInput_3193_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3201_: u8 = 0;
    let mut v_unused_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_3188_ = crate::leanh::lean_ctor_get(v_reader_3187_, 1);
                v_messageHead_3189_ = crate::leanh::lean_ctor_get(v_reader_3187_, 2);
                v_messageCount_3190_ = crate::leanh::lean_ctor_get(v_reader_3187_, 3);
                v_bodyBytesRead_3191_ = crate::leanh::lean_ctor_get(v_reader_3187_, 4);
                v_headerBytesRead_3192_ = crate::leanh::lean_ctor_get(v_reader_3187_, 5);
                v_noMoreInput_3193_ = crate::leanh::lean_ctor_get_uint8(
                    v_reader_3187_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_isSharedCheck_3201_ = (!crate::leanh::lean_is_exclusive(v_reader_3187_)) as u8;
                if v_isSharedCheck_3201_ == 0 {
                    v_unused_3202_ = crate::leanh::lean_ctor_get(v_reader_3187_, 0);
                    crate::leanh::lean_dec(v_unused_3202_);
                    v___x_3195_ = v_reader_3187_;
                    v_isShared_3196_ = v_isSharedCheck_3201_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3192_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3191_);
                    crate::leanh::lean_inc(v_messageCount_3190_);
                    crate::leanh::lean_inc(v_messageHead_3189_);
                    crate::leanh::lean_inc(v_input_3188_);
                    crate::leanh::lean_dec(v_reader_3187_);
                    v___x_3195_ = crate::leanh::lean_box(0);
                    v_isShared_3196_ = v_isSharedCheck_3201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3197_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0;
                if v_isShared_3196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3195_, 0, v___x_3197_);
                    v___x_3199_ = v___x_3195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_input_3188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_messageHead_3189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_messageCount_3190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 4, v_bodyBytesRead_3191_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 5, v_headerBytesRead_3192_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3200_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_dir_3203_: *mut crate::leanh::LeanObject,
    mut v_reader_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3205_: u8 = 0;
    let mut v_res_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3205_ = (crate::leanh::lean_unbox(v_dir_3203_) as u8);
    v_res_3206_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_3205_, v_reader_3204_);
    return v_res_3206_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(
    mut v_reader_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3208_ = crate::leanh::lean_ctor_get(v_reader_3207_, 0);
                v_input_3209_ = crate::leanh::lean_ctor_get(v_reader_3207_, 1);
                v_messageHead_3210_ = crate::leanh::lean_ctor_get(v_reader_3207_, 2);
                v_messageCount_3211_ = crate::leanh::lean_ctor_get(v_reader_3207_, 3);
                v_bodyBytesRead_3212_ = crate::leanh::lean_ctor_get(v_reader_3207_, 4);
                v_headerBytesRead_3213_ = crate::leanh::lean_ctor_get(v_reader_3207_, 5);
                v_isSharedCheck_3221_ = (!crate::leanh::lean_is_exclusive(v_reader_3207_)) as u8;
                if v_isSharedCheck_3221_ == 0 {
                    v___x_3215_ = v_reader_3207_;
                    v_isShared_3216_ = v_isSharedCheck_3221_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3213_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3212_);
                    crate::leanh::lean_inc(v_messageCount_3211_);
                    crate::leanh::lean_inc(v_messageHead_3210_);
                    crate::leanh::lean_inc(v_input_3209_);
                    crate::leanh::lean_inc(v_state_3208_);
                    crate::leanh::lean_dec(v_reader_3207_);
                    v___x_3215_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3220_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_state_3208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_input_3209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_messageHead_3210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_messageCount_3211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_bodyBytesRead_3212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 5, v_headerBytesRead_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3219_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
    mut v_reader_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageHead_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messageCount_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyBytesRead_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerBytesRead_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_3224_ = crate::leanh::lean_ctor_get(v_reader_3223_, 0);
                v_input_3225_ = crate::leanh::lean_ctor_get(v_reader_3223_, 1);
                v_messageHead_3226_ = crate::leanh::lean_ctor_get(v_reader_3223_, 2);
                v_messageCount_3227_ = crate::leanh::lean_ctor_get(v_reader_3223_, 3);
                v_bodyBytesRead_3228_ = crate::leanh::lean_ctor_get(v_reader_3223_, 4);
                v_headerBytesRead_3229_ = crate::leanh::lean_ctor_get(v_reader_3223_, 5);
                v_isSharedCheck_3237_ = (!crate::leanh::lean_is_exclusive(v_reader_3223_)) as u8;
                if v_isSharedCheck_3237_ == 0 {
                    v___x_3231_ = v_reader_3223_;
                    v_isShared_3232_ = v_isSharedCheck_3237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_headerBytesRead_3229_);
                    crate::leanh::lean_inc(v_bodyBytesRead_3228_);
                    crate::leanh::lean_inc(v_messageCount_3227_);
                    crate::leanh::lean_inc(v_messageHead_3226_);
                    crate::leanh::lean_inc(v_input_3225_);
                    crate::leanh::lean_inc(v_state_3224_);
                    crate::leanh::lean_dec(v_reader_3223_);
                    v___x_3231_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3236_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_state_3224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_input_3225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_messageHead_3226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_messageCount_3227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_bodyBytesRead_3228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 5, v_headerBytesRead_3229_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3235_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v___x_3233_,
                );
                return v___x_3235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(
    mut v_dir_3238_: *mut crate::leanh::LeanObject,
    mut v_reader_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3240_: u8 = 0;
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3240_ = (crate::leanh::lean_unbox(v_dir_3238_) as u8);
    v_res_3241_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_3240_, v_reader_3239_);
    return v_res_3241_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(
    mut v_dir_3242_: u8,
    mut v_reader_3243_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_messageHead_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    v_messageHead_3244_ = crate::leanh::lean_ctor_get(v_reader_3243_, 2);
    v___x_3245_ =
        l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_3242_, v_messageHead_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(
    mut v_dir_3246_: *mut crate::leanh::LeanObject,
    mut v_reader_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_boxed_3248_: u8 = 0;
    let mut v_res_3249_: u8 = 0;
    let mut v_r_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_3248_ = (crate::leanh::lean_unbox(v_dir_3246_) as u8);
    v_res_3249_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_3248_, v_reader_3247_);
    crate::leanh::lean_dec_ref(v_reader_3247_);
    v_r_3250_ = crate::leanh::lean_box((v_res_3249_) as usize);
    return v_r_3250_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Reader(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Reader(
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
pub unsafe fn initialize_Std_Http_Protocol_H1_Reader(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Reader(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Reader(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Reader(builtin);
}
