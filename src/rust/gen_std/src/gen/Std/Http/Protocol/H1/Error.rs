// Lean compiler output
// Module: Std.Http.Protocol.H1.Error
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Http::Protocol::H1::Config::{
    initialize_Std_Http_Protocol_H1_Config, runtime_initialize_Std_Http_Protocol_H1_Config,
};
use crate::r#gen::Std::Http::Protocol::H1::Message::{
    initialize_Std_Http_Protocol_H1_Message, runtime_initialize_Std_Http_Protocol_H1_Message,
};
use crate::r#gen::Std::Http::Protocol::H1::Parser::{
    initialize_Std_Http_Protocol_H1_Parser, runtime_initialize_Std_Http_Protocol_H1_Parser,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_append;
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le, lean_string_dec_eq};
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value:
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
        46, 69, 114, 114, 111, 114, 46, 104, 101, 97, 100, 101, 114, 115, 84, 111, 111, 76, 97,
        114, 103, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value:
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
        46, 69, 114, 114, 111, 114, 46, 116, 111, 111, 77, 97, 110, 121, 72, 101, 97, 100, 101,
        114, 115, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 98, 97, 100, 77, 101, 115, 115, 97, 103, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value:
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
        46, 69, 114, 114, 111, 114, 46, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110, 67, 108,
        111, 115, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 67, 104, 117, 110, 107,
        0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 86,
        101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 117, 114, 105, 84, 111, 111, 76, 111, 110, 103, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value:
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
        46, 69, 114, 114, 111, 114, 46, 101, 110, 116, 105, 116, 121, 84, 111, 111, 76, 97, 114,
        103, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 116, 105, 109, 101, 111, 117, 116, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value:
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
        46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 72, 101, 97, 100, 101,
        114, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value:
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
        46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 83, 116, 97, 116, 117,
        115, 76, 105, 110, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 114, 114, 111, 114, 46, 111, 116, 104, 101, 114, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Protocol_H1_instReprError_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instReprError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_instReprError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instBEqError___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Protocol_H1_instBEqError_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instBEqError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_instBEqError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
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
        73, 110, 118, 97, 108, 105, 100, 32, 115, 116, 97, 116, 117, 115, 32, 108, 105, 110, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 104, 101, 97, 100, 101, 114, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value:
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
    m_data: [84, 105, 109, 101, 111, 117, 116, 0],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value:
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
        69, 110, 116, 105, 116, 121, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [85, 82, 73, 32, 116, 111, 111, 32, 108, 111, 110, 103, 0],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
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
        85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 118, 101, 114, 115, 105, 111,
        110, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value:
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
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 99, 104, 117, 110, 107, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value:
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
        67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 32, 99, 108, 111, 115, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value:
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
    m_data: [66, 97, 100, 32, 109, 101, 115, 115, 97, 103, 101, 0],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value:
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
        84, 111, 111, 32, 109, 97, 110, 121, 32, 104, 101, 97, 100, 101, 114, 115, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value:
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
        72, 101, 97, 100, 101, 114, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value:
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
    m_data: [
        79, 116, 104, 101, 114, 32, 101, 114, 114, 111, 114, 58, 32, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___closed__0_value:
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
    m_fun: l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_instToStringError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Protocol_H1_instToStringError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorIdx(
    mut v_x_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_365_) {
        0 => {
            let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_366_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_366_;
        }
        1 => {
            let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_367_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_367_;
        }
        2 => {
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_368_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_368_;
        }
        3 => {
            let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_369_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_369_;
        }
        4 => {
            let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_370_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_370_;
        }
        5 => {
            let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_371_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_371_;
        }
        6 => {
            let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_372_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_372_;
        }
        7 => {
            let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_373_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_373_;
        }
        8 => {
            let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_374_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_374_;
        }
        9 => {
            let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_375_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_375_;
        }
        10 => {
            let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_376_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_376_;
        }
        _ => {
            let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_377_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_377_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorIdx___boxed(
    mut v_x_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_379_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_378_);
    crate::leanh::lean_dec(v_x_378_);
    return v_res_379_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim___redArg(
    mut v_t_380_: *mut crate::leanh::LeanObject,
    mut v_k_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_380_) == 11 {
        let mut v_message_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_message_382_ = crate::leanh::lean_ctor_get(v_t_380_, 0);
        crate::leanh::lean_inc_ref(v_message_382_);
        crate::leanh::lean_dec_ref_known(v_t_380_, 1);
        v___x_383_ = crate::leanh::lean_apply_1(v_k_381_, v_message_382_);
        return v___x_383_;
    } else {
        crate::leanh::lean_dec(v_t_380_);
        return v_k_381_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim(
    mut v_motive_384_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_385_: *mut crate::leanh::LeanObject,
    mut v_t_386_: *mut crate::leanh::LeanObject,
    mut v_h_387_: *mut crate::leanh::LeanObject,
    mut v_k_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_386_, v_k_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim___boxed(
    mut v_motive_390_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_391_: *mut crate::leanh::LeanObject,
    mut v_t_392_: *mut crate::leanh::LeanObject,
    mut v_h_393_: *mut crate::leanh::LeanObject,
    mut v_k_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_Std_Http_Protocol_H1_Error_ctorElim(
        v_motive_390_,
        v_ctorIdx_391_,
        v_t_392_,
        v_h_393_,
        v_k_394_,
    );
    crate::leanh::lean_dec(v_ctorIdx_391_);
    return v_res_395_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim___redArg(
    mut v_t_396_: *mut crate::leanh::LeanObject,
    mut v_invalidStatusLine_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_396_, v_invalidStatusLine_397_);
    return v___x_398_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim(
    mut v_motive_399_: *mut crate::leanh::LeanObject,
    mut v_t_400_: *mut crate::leanh::LeanObject,
    mut v_h_401_: *mut crate::leanh::LeanObject,
    mut v_invalidStatusLine_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_400_, v_invalidStatusLine_402_);
    return v___x_403_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidHeader_elim___redArg(
    mut v_t_404_: *mut crate::leanh::LeanObject,
    mut v_invalidHeader_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_404_, v_invalidHeader_405_);
    return v___x_406_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidHeader_elim(
    mut v_motive_407_: *mut crate::leanh::LeanObject,
    mut v_t_408_: *mut crate::leanh::LeanObject,
    mut v_h_409_: *mut crate::leanh::LeanObject,
    mut v_invalidHeader_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_408_, v_invalidHeader_410_);
    return v___x_411_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_timeout_elim___redArg(
    mut v_t_412_: *mut crate::leanh::LeanObject,
    mut v_timeout_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_412_, v_timeout_413_);
    return v___x_414_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_timeout_elim(
    mut v_motive_415_: *mut crate::leanh::LeanObject,
    mut v_t_416_: *mut crate::leanh::LeanObject,
    mut v_h_417_: *mut crate::leanh::LeanObject,
    mut v_timeout_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_416_, v_timeout_418_);
    return v___x_419_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_entityTooLarge_elim___redArg(
    mut v_t_420_: *mut crate::leanh::LeanObject,
    mut v_entityTooLarge_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_420_, v_entityTooLarge_421_);
    return v___x_422_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_entityTooLarge_elim(
    mut v_motive_423_: *mut crate::leanh::LeanObject,
    mut v_t_424_: *mut crate::leanh::LeanObject,
    mut v_h_425_: *mut crate::leanh::LeanObject,
    mut v_entityTooLarge_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_424_, v_entityTooLarge_426_);
    return v___x_427_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_uriTooLong_elim___redArg(
    mut v_t_428_: *mut crate::leanh::LeanObject,
    mut v_uriTooLong_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_428_, v_uriTooLong_429_);
    return v___x_430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_uriTooLong_elim(
    mut v_motive_431_: *mut crate::leanh::LeanObject,
    mut v_t_432_: *mut crate::leanh::LeanObject,
    mut v_h_433_: *mut crate::leanh::LeanObject,
    mut v_uriTooLong_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_432_, v_uriTooLong_434_);
    return v___x_435_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim___redArg(
    mut v_t_436_: *mut crate::leanh::LeanObject,
    mut v_unsupportedVersion_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ =
        l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_436_, v_unsupportedVersion_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim(
    mut v_motive_439_: *mut crate::leanh::LeanObject,
    mut v_t_440_: *mut crate::leanh::LeanObject,
    mut v_h_441_: *mut crate::leanh::LeanObject,
    mut v_unsupportedVersion_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ =
        l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_440_, v_unsupportedVersion_442_);
    return v___x_443_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(
    mut v_t_444_: *mut crate::leanh::LeanObject,
    mut v_invalidChunk_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_444_, v_invalidChunk_445_);
    return v___x_446_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidChunk_elim(
    mut v_motive_447_: *mut crate::leanh::LeanObject,
    mut v_t_448_: *mut crate::leanh::LeanObject,
    mut v_h_449_: *mut crate::leanh::LeanObject,
    mut v_invalidChunk_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_448_, v_invalidChunk_450_);
    return v___x_451_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(
    mut v_t_452_: *mut crate::leanh::LeanObject,
    mut v_connectionClosed_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_454_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_452_, v_connectionClosed_453_);
    return v___x_454_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_connectionClosed_elim(
    mut v_motive_455_: *mut crate::leanh::LeanObject,
    mut v_t_456_: *mut crate::leanh::LeanObject,
    mut v_h_457_: *mut crate::leanh::LeanObject,
    mut v_connectionClosed_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_456_, v_connectionClosed_458_);
    return v___x_459_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(
    mut v_t_460_: *mut crate::leanh::LeanObject,
    mut v_badMessage_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_460_, v_badMessage_461_);
    return v___x_462_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_badMessage_elim(
    mut v_motive_463_: *mut crate::leanh::LeanObject,
    mut v_t_464_: *mut crate::leanh::LeanObject,
    mut v_h_465_: *mut crate::leanh::LeanObject,
    mut v_badMessage_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_464_, v_badMessage_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(
    mut v_t_468_: *mut crate::leanh::LeanObject,
    mut v_tooManyHeaders_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_468_, v_tooManyHeaders_469_);
    return v___x_470_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(
    mut v_motive_471_: *mut crate::leanh::LeanObject,
    mut v_t_472_: *mut crate::leanh::LeanObject,
    mut v_h_473_: *mut crate::leanh::LeanObject,
    mut v_tooManyHeaders_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_472_, v_tooManyHeaders_474_);
    return v___x_475_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(
    mut v_t_476_: *mut crate::leanh::LeanObject,
    mut v_headersTooLarge_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_476_, v_headersTooLarge_477_);
    return v___x_478_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(
    mut v_motive_479_: *mut crate::leanh::LeanObject,
    mut v_t_480_: *mut crate::leanh::LeanObject,
    mut v_h_481_: *mut crate::leanh::LeanObject,
    mut v_headersTooLarge_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_480_, v_headersTooLarge_482_);
    return v___x_483_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_other_elim___redArg(
    mut v_t_484_: *mut crate::leanh::LeanObject,
    mut v_other_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_484_, v_other_485_);
    return v___x_486_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_other_elim(
    mut v_motive_487_: *mut crate::leanh::LeanObject,
    mut v_t_488_: *mut crate::leanh::LeanObject,
    mut v_h_489_: *mut crate::leanh::LeanObject,
    mut v_other_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_491_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_488_, v_other_490_);
    return v___x_491_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_526_ = lean_nat_to_int(v___x_525_);
    return v___x_526_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_528_ = lean_nat_to_int(v___x_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprError_repr(
    mut v_x_535_: *mut crate::leanh::LeanObject,
    mut v_prec_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: u8 = 0;
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: u8 = 0;
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___y_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_535_) {
                0 => {
                    v___x_614_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_536_);
                    if v___x_615_ == 0 {
                        v___x_616_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_608_ = v___x_616_;
                        state = 11;
                        continue;
                    } else {
                        v___x_617_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_608_ = v___x_617_;
                        state = 11;
                        continue;
                    }
                }
                1 => {
                    v___x_618_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_536_);
                    if v___x_619_ == 0 {
                        v___x_620_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_601_ = v___x_620_;
                        state = 10;
                        continue;
                    } else {
                        v___x_621_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_601_ = v___x_621_;
                        state = 10;
                        continue;
                    }
                }
                2 => {
                    v___x_622_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_623_ = lean_nat_dec_le(v___x_622_, v_prec_536_);
                    if v___x_623_ == 0 {
                        v___x_624_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_594_ = v___x_624_;
                        state = 9;
                        continue;
                    } else {
                        v___x_625_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_594_ = v___x_625_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v___x_626_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_536_);
                    if v___x_627_ == 0 {
                        v___x_628_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_587_ = v___x_628_;
                        state = 8;
                        continue;
                    } else {
                        v___x_629_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_587_ = v___x_629_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    v___x_630_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_631_ = lean_nat_dec_le(v___x_630_, v_prec_536_);
                    if v___x_631_ == 0 {
                        v___x_632_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_580_ = v___x_632_;
                        state = 7;
                        continue;
                    } else {
                        v___x_633_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_580_ = v___x_633_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v___x_634_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_635_ = lean_nat_dec_le(v___x_634_, v_prec_536_);
                    if v___x_635_ == 0 {
                        v___x_636_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_573_ = v___x_636_;
                        state = 6;
                        continue;
                    } else {
                        v___x_637_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_573_ = v___x_637_;
                        state = 6;
                        continue;
                    }
                }
                6 => {
                    v___x_638_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_536_);
                    if v___x_639_ == 0 {
                        v___x_640_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_566_ = v___x_640_;
                        state = 5;
                        continue;
                    } else {
                        v___x_641_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_566_ = v___x_641_;
                        state = 5;
                        continue;
                    }
                }
                7 => {
                    v___x_642_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_643_ = lean_nat_dec_le(v___x_642_, v_prec_536_);
                    if v___x_643_ == 0 {
                        v___x_644_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_559_ = v___x_644_;
                        state = 4;
                        continue;
                    } else {
                        v___x_645_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_559_ = v___x_645_;
                        state = 4;
                        continue;
                    }
                }
                8 => {
                    v___x_646_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_647_ = lean_nat_dec_le(v___x_646_, v_prec_536_);
                    if v___x_647_ == 0 {
                        v___x_648_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_552_ = v___x_648_;
                        state = 3;
                        continue;
                    } else {
                        v___x_649_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_552_ = v___x_649_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v___x_650_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_651_ = lean_nat_dec_le(v___x_650_, v_prec_536_);
                    if v___x_651_ == 0 {
                        v___x_652_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_545_ = v___x_652_;
                        state = 2;
                        continue;
                    } else {
                        v___x_653_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_545_ = v___x_653_;
                        state = 2;
                        continue;
                    }
                }
                10 => {
                    v___x_654_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_655_ = lean_nat_dec_le(v___x_654_, v_prec_536_);
                    if v___x_655_ == 0 {
                        v___x_656_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                        );
                        v___y_538_ = v___x_656_;
                        state = 1;
                        continue;
                    } else {
                        v___x_657_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                        );
                        v___y_538_ = v___x_657_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_message_658_ = crate::leanh::lean_ctor_get(v_x_535_, 0);
                    v_isSharedCheck_678_ = (!crate::leanh::lean_is_exclusive(v_x_535_)) as u8;
                    if v_isSharedCheck_678_ == 0 {
                        v___x_660_ = v_x_535_;
                        v_isShared_661_ = v_isSharedCheck_678_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_message_658_);
                        crate::leanh::lean_dec(v_x_535_);
                        v___x_660_ = crate::leanh::lean_box(0);
                        v_isShared_661_ = v_isSharedCheck_678_;
                        state = 12;
                        continue;
                    }
                }
            },
            1 => {
                v___x_539_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__1;
                crate::leanh::lean_inc(v___y_538_);
                v___x_540_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_540_, 0, v___y_538_);
                crate::leanh::lean_ctor_set(v___x_540_, 1, v___x_539_);
                v___x_541_ = 0;
                v___x_542_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_542_, 0, v___x_540_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_541_,
                );
                v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_536_);
                return v___x_543_;
            }
            2 => {
                v___x_546_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__3;
                crate::leanh::lean_inc(v___y_545_);
                v___x_547_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_547_, 0, v___y_545_);
                crate::leanh::lean_ctor_set(v___x_547_, 1, v___x_546_);
                v___x_548_ = 0;
                v___x_549_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_547_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_549_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_548_,
                );
                v___x_550_ = l_Repr_addAppParen(v___x_549_, v_prec_536_);
                return v___x_550_;
            }
            3 => {
                v___x_553_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__5;
                crate::leanh::lean_inc(v___y_552_);
                v___x_554_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_554_, 0, v___y_552_);
                crate::leanh::lean_ctor_set(v___x_554_, 1, v___x_553_);
                v___x_555_ = 0;
                v___x_556_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_556_, 0, v___x_554_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_556_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_555_,
                );
                v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_536_);
                return v___x_557_;
            }
            4 => {
                v___x_560_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__7;
                crate::leanh::lean_inc(v___y_559_);
                v___x_561_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_561_, 0, v___y_559_);
                crate::leanh::lean_ctor_set(v___x_561_, 1, v___x_560_);
                v___x_562_ = 0;
                v___x_563_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_563_, 0, v___x_561_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_562_,
                );
                v___x_564_ = l_Repr_addAppParen(v___x_563_, v_prec_536_);
                return v___x_564_;
            }
            5 => {
                v___x_567_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__9;
                crate::leanh::lean_inc(v___y_566_);
                v___x_568_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_568_, 0, v___y_566_);
                crate::leanh::lean_ctor_set(v___x_568_, 1, v___x_567_);
                v___x_569_ = 0;
                v___x_570_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_570_, 0, v___x_568_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_570_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_569_,
                );
                v___x_571_ = l_Repr_addAppParen(v___x_570_, v_prec_536_);
                return v___x_571_;
            }
            6 => {
                v___x_574_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__11;
                crate::leanh::lean_inc(v___y_573_);
                v___x_575_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_575_, 0, v___y_573_);
                crate::leanh::lean_ctor_set(v___x_575_, 1, v___x_574_);
                v___x_576_ = 0;
                v___x_577_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_577_, 0, v___x_575_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_576_,
                );
                v___x_578_ = l_Repr_addAppParen(v___x_577_, v_prec_536_);
                return v___x_578_;
            }
            7 => {
                v___x_581_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__13;
                crate::leanh::lean_inc(v___y_580_);
                v___x_582_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_582_, 0, v___y_580_);
                crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
                v___x_583_ = 0;
                v___x_584_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_582_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_584_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_583_,
                );
                v___x_585_ = l_Repr_addAppParen(v___x_584_, v_prec_536_);
                return v___x_585_;
            }
            8 => {
                v___x_588_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__15;
                crate::leanh::lean_inc(v___y_587_);
                v___x_589_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_589_, 0, v___y_587_);
                crate::leanh::lean_ctor_set(v___x_589_, 1, v___x_588_);
                v___x_590_ = 0;
                v___x_591_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_591_, 0, v___x_589_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_591_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_590_,
                );
                v___x_592_ = l_Repr_addAppParen(v___x_591_, v_prec_536_);
                return v___x_592_;
            }
            9 => {
                v___x_595_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__17;
                crate::leanh::lean_inc(v___y_594_);
                v___x_596_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_596_, 0, v___y_594_);
                crate::leanh::lean_ctor_set(v___x_596_, 1, v___x_595_);
                v___x_597_ = 0;
                v___x_598_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_598_, 0, v___x_596_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_597_,
                );
                v___x_599_ = l_Repr_addAppParen(v___x_598_, v_prec_536_);
                return v___x_599_;
            }
            10 => {
                v___x_602_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__19;
                crate::leanh::lean_inc(v___y_601_);
                v___x_603_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_603_, 0, v___y_601_);
                crate::leanh::lean_ctor_set(v___x_603_, 1, v___x_602_);
                v___x_604_ = 0;
                v___x_605_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_605_, 0, v___x_603_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_605_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_536_);
                return v___x_606_;
            }
            11 => {
                v___x_609_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__21;
                crate::leanh::lean_inc(v___y_608_);
                v___x_610_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_610_, 0, v___y_608_);
                crate::leanh::lean_ctor_set(v___x_610_, 1, v___x_609_);
                v___x_611_ = 0;
                v___x_612_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_612_, 0, v___x_610_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_611_,
                );
                v___x_613_ = l_Repr_addAppParen(v___x_612_, v_prec_536_);
                return v___x_613_;
            }
            12 => {
                v___x_674_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_675_ = lean_nat_dec_le(v___x_674_, v_prec_536_);
                if v___x_675_ == 0 {
                    v___x_676_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_instReprError_repr___closed__22
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once
                        ),
                        _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22,
                    );
                    v___y_663_ = v___x_676_;
                    state = 13;
                    continue;
                } else {
                    v___x_677_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_instReprError_repr___closed__23
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once
                        ),
                        _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23,
                    );
                    v___y_663_ = v___x_677_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_664_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__26;
                v___x_665_ = l_String_quote(v_message_658_);
                if v_isShared_661_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_660_, 3);
                    crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_665_);
                    v___x_667_ = v___x_660_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_665_);
                    v___x_667_ = v_reuseFailAlloc_673_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_668_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_664_);
                crate::leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
                crate::leanh::lean_inc(v___y_663_);
                v___x_669_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_669_, 0, v___y_663_);
                crate::leanh::lean_ctor_set(v___x_669_, 1, v___x_668_);
                v___x_670_ = 0;
                v___x_671_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_671_, 0, v___x_669_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_670_,
                );
                v___x_672_ = l_Repr_addAppParen(v___x_671_, v_prec_536_);
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprError_repr___boxed(
    mut v_x_679_: *mut crate::leanh::LeanObject,
    mut v_prec_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_681_ = l_Std_Http_Protocol_H1_instReprError_repr(v_x_679_, v_prec_680_);
    crate::leanh::lean_dec(v_prec_680_);
    return v_res_681_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqError_beq(
    mut v_x_684_: *mut crate::leanh::LeanObject,
    mut v_x_685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    v___x_686_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_684_);
    v___x_687_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_685_);
    v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
    crate::leanh::lean_dec(v___x_687_);
    crate::leanh::lean_dec(v___x_686_);
    if v___x_688_ == 0 {
        return v___x_688_;
    } else {
        if crate::leanh::lean_obj_tag(v_x_684_) == 11 {
            let mut v_message_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_message_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_691_: u8 = 0;
            v_message_689_ = crate::leanh::lean_ctor_get(v_x_684_, 0);
            v_message_690_ = crate::leanh::lean_ctor_get(v_x_685_, 0);
            v___x_691_ = lean_string_dec_eq(v_message_689_, v_message_690_);
            return v___x_691_;
        } else {
            return v___x_688_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqError_beq___boxed(
    mut v_x_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_694_: u8 = 0;
    let mut v_r_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_692_, v_x_693_);
    crate::leanh::lean_dec(v_x_693_);
    crate::leanh::lean_dec(v_x_692_);
    v_r_695_ = crate::leanh::lean_box((v_res_694_) as usize);
    return v_r_695_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instToStringError___lam__0(
    mut v_x_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_710_) {
        0 => {
            let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_711_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0;
            return v___x_711_;
        }
        1 => {
            let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_712_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1;
            return v___x_712_;
        }
        2 => {
            let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_713_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2;
            return v___x_713_;
        }
        3 => {
            let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_714_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3;
            return v___x_714_;
        }
        4 => {
            let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_715_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4;
            return v___x_715_;
        }
        5 => {
            let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_716_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5;
            return v___x_716_;
        }
        6 => {
            let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_717_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6;
            return v___x_717_;
        }
        7 => {
            let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_718_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7;
            return v___x_718_;
        }
        8 => {
            let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_719_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8;
            return v___x_719_;
        }
        9 => {
            let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_720_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9;
            return v___x_720_;
        }
        10 => {
            let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_721_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10;
            return v___x_721_;
        }
        _ => {
            let mut v_message_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_message_722_ = crate::leanh::lean_ctor_get(v_x_710_, 0);
            v___x_723_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11;
            v___x_724_ = lean_string_append(v___x_723_, v_message_722_);
            return v___x_724_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(
    mut v_x_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Http_Protocol_H1_instToStringError___lam__0(v_x_725_);
    crate::leanh::lean_dec(v_x_725_);
    return v_res_726_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Error(
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
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Error(
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
pub unsafe fn initialize_Std_Http_Protocol_H1_Error(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Error(builtin);
}
