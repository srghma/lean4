// Lean compiler output
// Module: Std.Http.Protocol.H1.Event
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message Std.Http.Protocol.H1.Error
use crate::ffi::{lean_nat_dec_le, lean_nat_to_int};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Http::Protocol::H1::Config::{
    initialize_Std_Http_Protocol_H1_Config, runtime_initialize_Std_Http_Protocol_H1_Config,
};
use crate::r#gen::Std::Http::Protocol::H1::Error::{
    initialize_Std_Http_Protocol_H1_Error, l_Std_Http_Protocol_H1_instReprError_repr,
    runtime_initialize_Std_Http_Protocol_H1_Error,
};
use crate::r#gen::Std::Http::Protocol::H1::Message::{
    initialize_Std_Http_Protocol_H1_Message, l_Std_Http_Protocol_H1_instReprHead,
    runtime_initialize_Std_Http_Protocol_H1_Message,
};
use crate::r#gen::Std::Http::Protocol::H1::Parser::{
    initialize_Std_Http_Protocol_H1_Parser, runtime_initialize_Std_Http_Protocol_H1_Parser,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub static l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value:
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
static mut l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
        46, 69, 118, 101, 110, 116, 46, 99, 108, 111, 115, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 118, 101, 110, 116, 46, 99, 108, 111, 115, 101, 66, 111, 100, 121, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
        46, 69, 118, 101, 110, 116, 46, 110, 101, 101, 100, 65, 110, 115, 119, 101, 114, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 118, 101, 110, 116, 46, 110, 101, 120, 116, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 118, 101, 110, 116, 46, 99, 111, 110, 116, 105, 110, 117, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
        46, 69, 118, 101, 110, 116, 46, 101, 110, 100, 72, 101, 97, 100, 101, 114, 115, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
        46, 69, 118, 101, 110, 116, 46, 110, 101, 101, 100, 77, 111, 114, 101, 68, 97, 116, 97, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 69, 118, 101, 110, 116, 46, 102, 97, 105, 108, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value:
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
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(
    mut v_x_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_358_) {
        0 => {
            let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_359_ = leanh::lean_unsigned_to_nat(0);
            return v___x_359_;
        }
        1 => {
            let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_360_ = leanh::lean_unsigned_to_nat(1);
            return v___x_360_;
        }
        2 => {
            let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_361_ = leanh::lean_unsigned_to_nat(2);
            return v___x_361_;
        }
        3 => {
            let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_362_ = leanh::lean_unsigned_to_nat(3);
            return v___x_362_;
        }
        4 => {
            let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_363_ = leanh::lean_unsigned_to_nat(4);
            return v___x_363_;
        }
        5 => {
            let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_364_ = leanh::lean_unsigned_to_nat(5);
            return v___x_364_;
        }
        6 => {
            let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_365_ = leanh::lean_unsigned_to_nat(6);
            return v___x_365_;
        }
        _ => {
            let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_366_ = leanh::lean_unsigned_to_nat(7);
            return v___x_366_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___redArg___boxed(
    mut v_x_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_367_);
    leanh::lean_dec(v_x_367_);
    return v_res_368_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx(
    mut v_dir_369_: u8,
    mut v_x_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_370_);
    return v___x_371_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___boxed(
    mut v_dir_372_: *mut leanh::LeanObject,
    mut v_x_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_374_: u8 = 0;
    let mut v_res_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_374_ = (leanh::lean_unbox(v_dir_372_) as u8);
    v_res_375_ = l_Std_Http_Protocol_H1_Event_ctorIdx(v_dir_boxed_374_, v_x_373_);
    leanh::lean_dec(v_x_373_);
    return v_res_375_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim___redArg(
    mut v_t_376_: *mut leanh::LeanObject,
    mut v_k_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_376_) {
        0 => {
            let mut v_head_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_378_ = leanh::lean_ctor_get(v_t_376_, 0);
            leanh::lean_inc(v_head_378_);
            leanh::lean_dec_ref_known(v_t_376_, 1);
            v___x_379_ = leanh::lean_apply_1(v_k_377_, v_head_378_);
            return v___x_379_;
        }
        1 => {
            let mut v_size_380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_size_380_ = leanh::lean_ctor_get(v_t_376_, 0);
            leanh::lean_inc(v_size_380_);
            leanh::lean_dec_ref_known(v_t_376_, 1);
            v___x_381_ = leanh::lean_apply_1(v_k_377_, v_size_380_);
            return v___x_381_;
        }
        2 => {
            let mut v_err_382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_err_382_ = leanh::lean_ctor_get(v_t_376_, 0);
            leanh::lean_inc(v_err_382_);
            leanh::lean_dec_ref_known(v_t_376_, 1);
            v___x_383_ = leanh::lean_apply_1(v_k_377_, v_err_382_);
            return v___x_383_;
        }
        _ => {
            leanh::lean_dec(v_t_376_);
            return v_k_377_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim(
    mut v_dir_384_: u8,
    mut v_motive_385_: *mut leanh::LeanObject,
    mut v_ctorIdx_386_: *mut leanh::LeanObject,
    mut v_t_387_: *mut leanh::LeanObject,
    mut v_h_388_: *mut leanh::LeanObject,
    mut v_k_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_387_, v_k_389_);
    return v___x_390_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim___boxed(
    mut v_dir_391_: *mut leanh::LeanObject,
    mut v_motive_392_: *mut leanh::LeanObject,
    mut v_ctorIdx_393_: *mut leanh::LeanObject,
    mut v_t_394_: *mut leanh::LeanObject,
    mut v_h_395_: *mut leanh::LeanObject,
    mut v_k_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_397_: u8 = 0;
    let mut v_res_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_397_ = (leanh::lean_unbox(v_dir_391_) as u8);
    v_res_398_ = l_Std_Http_Protocol_H1_Event_ctorElim(
        v_dir_boxed_397_,
        v_motive_392_,
        v_ctorIdx_393_,
        v_t_394_,
        v_h_395_,
        v_k_396_,
    );
    leanh::lean_dec(v_ctorIdx_393_);
    return v_res_398_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(
    mut v_t_399_: *mut leanh::LeanObject,
    mut v_endHeaders_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_399_, v_endHeaders_400_);
    return v___x_401_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim(
    mut v_dir_402_: u8,
    mut v_motive_403_: *mut leanh::LeanObject,
    mut v_t_404_: *mut leanh::LeanObject,
    mut v_h_405_: *mut leanh::LeanObject,
    mut v_endHeaders_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_404_, v_endHeaders_406_);
    return v___x_407_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(
    mut v_dir_408_: *mut leanh::LeanObject,
    mut v_motive_409_: *mut leanh::LeanObject,
    mut v_t_410_: *mut leanh::LeanObject,
    mut v_h_411_: *mut leanh::LeanObject,
    mut v_endHeaders_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_413_: u8 = 0;
    let mut v_res_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_413_ = (leanh::lean_unbox(v_dir_408_) as u8);
    v_res_414_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(
        v_dir_boxed_413_,
        v_motive_409_,
        v_t_410_,
        v_h_411_,
        v_endHeaders_412_,
    );
    return v_res_414_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(
    mut v_t_415_: *mut leanh::LeanObject,
    mut v_needMoreData_416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_415_, v_needMoreData_416_);
    return v___x_417_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim(
    mut v_dir_418_: u8,
    mut v_motive_419_: *mut leanh::LeanObject,
    mut v_t_420_: *mut leanh::LeanObject,
    mut v_h_421_: *mut leanh::LeanObject,
    mut v_needMoreData_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_420_, v_needMoreData_422_);
    return v___x_423_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(
    mut v_dir_424_: *mut leanh::LeanObject,
    mut v_motive_425_: *mut leanh::LeanObject,
    mut v_t_426_: *mut leanh::LeanObject,
    mut v_h_427_: *mut leanh::LeanObject,
    mut v_needMoreData_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_429_: u8 = 0;
    let mut v_res_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_429_ = (leanh::lean_unbox(v_dir_424_) as u8);
    v_res_430_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(
        v_dir_boxed_429_,
        v_motive_425_,
        v_t_426_,
        v_h_427_,
        v_needMoreData_428_,
    );
    return v_res_430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim___redArg(
    mut v_t_431_: *mut leanh::LeanObject,
    mut v_failed_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_431_, v_failed_432_);
    return v___x_433_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim(
    mut v_dir_434_: u8,
    mut v_motive_435_: *mut leanh::LeanObject,
    mut v_t_436_: *mut leanh::LeanObject,
    mut v_h_437_: *mut leanh::LeanObject,
    mut v_failed_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_436_, v_failed_438_);
    return v___x_439_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim___boxed(
    mut v_dir_440_: *mut leanh::LeanObject,
    mut v_motive_441_: *mut leanh::LeanObject,
    mut v_t_442_: *mut leanh::LeanObject,
    mut v_h_443_: *mut leanh::LeanObject,
    mut v_failed_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_445_: u8 = 0;
    let mut v_res_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_445_ = (leanh::lean_unbox(v_dir_440_) as u8);
    v_res_446_ = l_Std_Http_Protocol_H1_Event_failed_elim(
        v_dir_boxed_445_,
        v_motive_441_,
        v_t_442_,
        v_h_443_,
        v_failed_444_,
    );
    return v_res_446_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim___redArg(
    mut v_t_447_: *mut leanh::LeanObject,
    mut v_close_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_447_, v_close_448_);
    return v___x_449_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim(
    mut v_dir_450_: u8,
    mut v_motive_451_: *mut leanh::LeanObject,
    mut v_t_452_: *mut leanh::LeanObject,
    mut v_h_453_: *mut leanh::LeanObject,
    mut v_close_454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_452_, v_close_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim___boxed(
    mut v_dir_456_: *mut leanh::LeanObject,
    mut v_motive_457_: *mut leanh::LeanObject,
    mut v_t_458_: *mut leanh::LeanObject,
    mut v_h_459_: *mut leanh::LeanObject,
    mut v_close_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_461_: u8 = 0;
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_461_ = (leanh::lean_unbox(v_dir_456_) as u8);
    v_res_462_ = l_Std_Http_Protocol_H1_Event_close_elim(
        v_dir_boxed_461_,
        v_motive_457_,
        v_t_458_,
        v_h_459_,
        v_close_460_,
    );
    return v_res_462_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(
    mut v_t_463_: *mut leanh::LeanObject,
    mut v_closeBody_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_463_, v_closeBody_464_);
    return v___x_465_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim(
    mut v_dir_466_: u8,
    mut v_motive_467_: *mut leanh::LeanObject,
    mut v_t_468_: *mut leanh::LeanObject,
    mut v_h_469_: *mut leanh::LeanObject,
    mut v_closeBody_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_468_, v_closeBody_470_);
    return v___x_471_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim___boxed(
    mut v_dir_472_: *mut leanh::LeanObject,
    mut v_motive_473_: *mut leanh::LeanObject,
    mut v_t_474_: *mut leanh::LeanObject,
    mut v_h_475_: *mut leanh::LeanObject,
    mut v_closeBody_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_477_: u8 = 0;
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_477_ = (leanh::lean_unbox(v_dir_472_) as u8);
    v_res_478_ = l_Std_Http_Protocol_H1_Event_closeBody_elim(
        v_dir_boxed_477_,
        v_motive_473_,
        v_t_474_,
        v_h_475_,
        v_closeBody_476_,
    );
    return v_res_478_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim___redArg(
    mut v_t_479_: *mut leanh::LeanObject,
    mut v_needAnswer_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_481_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_479_, v_needAnswer_480_);
    return v___x_481_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim(
    mut v_dir_482_: u8,
    mut v_motive_483_: *mut leanh::LeanObject,
    mut v_t_484_: *mut leanh::LeanObject,
    mut v_h_485_: *mut leanh::LeanObject,
    mut v_needAnswer_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_484_, v_needAnswer_486_);
    return v___x_487_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(
    mut v_dir_488_: *mut leanh::LeanObject,
    mut v_motive_489_: *mut leanh::LeanObject,
    mut v_t_490_: *mut leanh::LeanObject,
    mut v_h_491_: *mut leanh::LeanObject,
    mut v_needAnswer_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_493_: u8 = 0;
    let mut v_res_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_493_ = (leanh::lean_unbox(v_dir_488_) as u8);
    v_res_494_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(
        v_dir_boxed_493_,
        v_motive_489_,
        v_t_490_,
        v_h_491_,
        v_needAnswer_492_,
    );
    return v_res_494_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim___redArg(
    mut v_t_495_: *mut leanh::LeanObject,
    mut v_next_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_497_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_495_, v_next_496_);
    return v___x_497_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim(
    mut v_dir_498_: u8,
    mut v_motive_499_: *mut leanh::LeanObject,
    mut v_t_500_: *mut leanh::LeanObject,
    mut v_h_501_: *mut leanh::LeanObject,
    mut v_next_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_500_, v_next_502_);
    return v___x_503_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim___boxed(
    mut v_dir_504_: *mut leanh::LeanObject,
    mut v_motive_505_: *mut leanh::LeanObject,
    mut v_t_506_: *mut leanh::LeanObject,
    mut v_h_507_: *mut leanh::LeanObject,
    mut v_next_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_509_: u8 = 0;
    let mut v_res_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_509_ = (leanh::lean_unbox(v_dir_504_) as u8);
    v_res_510_ = l_Std_Http_Protocol_H1_Event_next_elim(
        v_dir_boxed_509_,
        v_motive_505_,
        v_t_506_,
        v_h_507_,
        v_next_508_,
    );
    return v_res_510_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim___redArg(
    mut v_t_511_: *mut leanh::LeanObject,
    mut v_continue_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_511_, v_continue_512_);
    return v___x_513_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim(
    mut v_dir_514_: u8,
    mut v_motive_515_: *mut leanh::LeanObject,
    mut v_t_516_: *mut leanh::LeanObject,
    mut v_h_517_: *mut leanh::LeanObject,
    mut v_continue_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_519_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_516_, v_continue_518_);
    return v___x_519_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim___boxed(
    mut v_dir_520_: *mut leanh::LeanObject,
    mut v_motive_521_: *mut leanh::LeanObject,
    mut v_t_522_: *mut leanh::LeanObject,
    mut v_h_523_: *mut leanh::LeanObject,
    mut v_continue_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_525_ = (leanh::lean_unbox(v_dir_520_) as u8);
    v_res_526_ = l_Std_Http_Protocol_H1_Event_continue_elim(
        v_dir_boxed_525_,
        v_motive_521_,
        v_t_522_,
        v_h_523_,
        v_continue_524_,
    );
    return v_res_526_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent_default(
    mut v_dir_529_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0;
    return v___x_530_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(
    mut v_dir_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_boxed_532_: u8 = 0;
    let mut v_res_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_boxed_532_ = (leanh::lean_unbox(v_dir_531_) as u8);
    v_res_533_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_boxed_532_);
    return v_res_533_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent(
    mut v_a_534_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_a_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(
    mut v_a_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5__boxed_537_: u8 = 0;
    let mut v_res_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_5__boxed_537_ = (leanh::lean_unbox(v_a_536_) as u8);
    v_res_538_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_5__boxed_537_);
    return v_res_538_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(
    mut v_x_545_: *mut leanh::LeanObject,
    mut v_x_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_545_) == 0 {
                    v___x_547_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1;
                    return v___x_547_;
                } else {
                    v_val_548_ = leanh::lean_ctor_get(v_x_545_, 0);
                    v_isSharedCheck_559_ = (!leanh::lean_is_exclusive(v_x_545_)) as u8;
                    if v_isSharedCheck_559_ == 0 {
                        v___x_550_ = v_x_545_;
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_548_);
                        leanh::lean_dec(v_x_545_);
                        v___x_550_ = leanh::lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_552_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3;
                v___x_553_ = l_Nat_reprFast(v_val_548_);
                if v_isShared_551_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_550_, 3);
                    leanh::lean_ctor_set(v___x_550_, 0, v___x_553_);
                    v___x_555_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_553_);
                    v___x_555_ = v_reuseFailAlloc_558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_556_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_556_, 0, v___x_552_);
                leanh::lean_ctor_set(v___x_556_, 1, v___x_555_);
                v___x_557_ = l_Repr_addAppParen(v___x_556_, v_x_546_);
                return v___x_557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(
    mut v_x_560_: *mut leanh::LeanObject,
    mut v_x_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ =
        l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_x_560_, v_x_561_);
    leanh::lean_dec(v_x_561_);
    return v_res_562_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = leanh::lean_unsigned_to_nat(2);
    v___x_585_ = lean_nat_to_int(v___x_584_);
    return v___x_585_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = leanh::lean_unsigned_to_nat(1);
    v___x_587_ = lean_nat_to_int(v___x_586_);
    return v___x_587_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent_repr(
    mut v_dir_600_: u8,
    mut v_x_601_: *mut leanh::LeanObject,
    mut v_prec_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: u8 = 0;
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358__overap_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_601_) {
                0 => {
                    v_head_638_ = leanh::lean_ctor_get(v_x_601_, 0);
                    leanh::lean_inc(v_head_638_);
                    leanh::lean_dec_ref_known(v_x_601_, 1);
                    v___x_650_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_651_ = lean_nat_dec_le(v___x_650_, v_prec_602_);
                    if v___x_651_ == 0 {
                        v___x_652_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_640_ = v___x_652_;
                        state = 6;
                        continue;
                    } else {
                        v___x_653_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_640_ = v___x_653_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    v_size_654_ = leanh::lean_ctor_get(v_x_601_, 0);
                    leanh::lean_inc(v_size_654_);
                    leanh::lean_dec_ref_known(v_x_601_, 1);
                    v___x_665_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_602_);
                    if v___x_666_ == 0 {
                        v___x_667_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_656_ = v___x_667_;
                        state = 7;
                        continue;
                    } else {
                        v___x_668_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_656_ = v___x_668_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_err_669_ = leanh::lean_ctor_get(v_x_601_, 0);
                    leanh::lean_inc(v_err_669_);
                    leanh::lean_dec_ref_known(v_x_601_, 1);
                    v___x_680_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_681_ = lean_nat_dec_le(v___x_680_, v_prec_602_);
                    if v___x_681_ == 0 {
                        v___x_682_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_671_ = v___x_682_;
                        state = 8;
                        continue;
                    } else {
                        v___x_683_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_671_ = v___x_683_;
                        state = 8;
                        continue;
                    }
                }
                3 => {
                    v___x_684_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_685_ = lean_nat_dec_le(v___x_684_, v_prec_602_);
                    if v___x_685_ == 0 {
                        v___x_686_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_604_ = v___x_686_;
                        state = 1;
                        continue;
                    } else {
                        v___x_687_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_604_ = v___x_687_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v___x_688_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_689_ = lean_nat_dec_le(v___x_688_, v_prec_602_);
                    if v___x_689_ == 0 {
                        v___x_690_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_611_ = v___x_690_;
                        state = 2;
                        continue;
                    } else {
                        v___x_691_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_611_ = v___x_691_;
                        state = 2;
                        continue;
                    }
                }
                5 => {
                    v___x_692_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_693_ = lean_nat_dec_le(v___x_692_, v_prec_602_);
                    if v___x_693_ == 0 {
                        v___x_694_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_618_ = v___x_694_;
                        state = 3;
                        continue;
                    } else {
                        v___x_695_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_618_ = v___x_695_;
                        state = 3;
                        continue;
                    }
                }
                6 => {
                    v___x_696_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_697_ = lean_nat_dec_le(v___x_696_, v_prec_602_);
                    if v___x_697_ == 0 {
                        v___x_698_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_625_ = v___x_698_;
                        state = 4;
                        continue;
                    } else {
                        v___x_699_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_625_ = v___x_699_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v___x_700_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_701_ = lean_nat_dec_le(v___x_700_, v_prec_602_);
                    if v___x_701_ == 0 {
                        v___x_702_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_632_ = v___x_702_;
                        state = 5;
                        continue;
                    } else {
                        v___x_703_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_632_ = v___x_703_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_605_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1;
                leanh::lean_inc(v___y_604_);
                v___x_606_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_606_, 0, v___y_604_);
                leanh::lean_ctor_set(v___x_606_, 1, v___x_605_);
                v___x_607_ = 0;
                v___x_608_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_608_, 0, v___x_606_);
                leanh::lean_ctor_set_uint8(
                    v___x_608_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_607_,
                );
                v___x_609_ = l_Repr_addAppParen(v___x_608_, v_prec_602_);
                return v___x_609_;
            }
            2 => {
                v___x_612_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3;
                leanh::lean_inc(v___y_611_);
                v___x_613_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_613_, 0, v___y_611_);
                leanh::lean_ctor_set(v___x_613_, 1, v___x_612_);
                v___x_614_ = 0;
                v___x_615_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_615_, 0, v___x_613_);
                leanh::lean_ctor_set_uint8(
                    v___x_615_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_614_,
                );
                v___x_616_ = l_Repr_addAppParen(v___x_615_, v_prec_602_);
                return v___x_616_;
            }
            3 => {
                v___x_619_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5;
                leanh::lean_inc(v___y_618_);
                v___x_620_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_620_, 0, v___y_618_);
                leanh::lean_ctor_set(v___x_620_, 1, v___x_619_);
                v___x_621_ = 0;
                v___x_622_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_622_, 0, v___x_620_);
                leanh::lean_ctor_set_uint8(
                    v___x_622_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_621_,
                );
                v___x_623_ = l_Repr_addAppParen(v___x_622_, v_prec_602_);
                return v___x_623_;
            }
            4 => {
                v___x_626_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7;
                leanh::lean_inc(v___y_625_);
                v___x_627_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_627_, 0, v___y_625_);
                leanh::lean_ctor_set(v___x_627_, 1, v___x_626_);
                v___x_628_ = 0;
                v___x_629_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_629_, 0, v___x_627_);
                leanh::lean_ctor_set_uint8(
                    v___x_629_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_628_,
                );
                v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_602_);
                return v___x_630_;
            }
            5 => {
                v___x_633_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9;
                leanh::lean_inc(v___y_632_);
                v___x_634_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_634_, 0, v___y_632_);
                leanh::lean_ctor_set(v___x_634_, 1, v___x_633_);
                v___x_635_ = 0;
                v___x_636_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_636_, 0, v___x_634_);
                leanh::lean_ctor_set_uint8(
                    v___x_636_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_635_,
                );
                v___x_637_ = l_Repr_addAppParen(v___x_636_, v_prec_602_);
                return v___x_637_;
            }
            6 => {
                v___x_641_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12;
                v___x_642_ = leanh::lean_unsigned_to_nat(1024);
                v___x_358__overap_643_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_600_);
                v___x_644_ =
                    leanh::lean_apply_2(v___x_358__overap_643_, v_head_638_, v___x_642_);
                v___x_645_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_645_, 0, v___x_641_);
                leanh::lean_ctor_set(v___x_645_, 1, v___x_644_);
                leanh::lean_inc(v___y_640_);
                v___x_646_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_646_, 0, v___y_640_);
                leanh::lean_ctor_set(v___x_646_, 1, v___x_645_);
                v___x_647_ = 0;
                v___x_648_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_648_, 0, v___x_646_);
                leanh::lean_ctor_set_uint8(
                    v___x_648_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_647_,
                );
                v___x_649_ = l_Repr_addAppParen(v___x_648_, v_prec_602_);
                return v___x_649_;
            }
            7 => {
                v___x_657_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17;
                v___x_658_ = leanh::lean_unsigned_to_nat(1024);
                v___x_659_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(
                    v_size_654_,
                    v___x_658_,
                );
                v___x_660_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_660_, 0, v___x_657_);
                leanh::lean_ctor_set(v___x_660_, 1, v___x_659_);
                leanh::lean_inc(v___y_656_);
                v___x_661_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_661_, 0, v___y_656_);
                leanh::lean_ctor_set(v___x_661_, 1, v___x_660_);
                v___x_662_ = 0;
                v___x_663_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_663_, 0, v___x_661_);
                leanh::lean_ctor_set_uint8(
                    v___x_663_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_662_,
                );
                v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_602_);
                return v___x_664_;
            }
            8 => {
                v___x_672_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20;
                v___x_673_ = leanh::lean_unsigned_to_nat(1024);
                v___x_674_ = l_Std_Http_Protocol_H1_instReprError_repr(v_err_669_, v___x_673_);
                v___x_675_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_675_, 0, v___x_672_);
                leanh::lean_ctor_set(v___x_675_, 1, v___x_674_);
                leanh::lean_inc(v___y_671_);
                v___x_676_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_676_, 0, v___y_671_);
                leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = 0;
                v___x_678_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_678_, 0, v___x_676_);
                leanh::lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_677_,
                );
                v___x_679_ = l_Repr_addAppParen(v___x_678_, v_prec_602_);
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(
    mut v_dir_704_: *mut leanh::LeanObject,
    mut v_x_705_: *mut leanh::LeanObject,
    mut v_prec_706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_701__boxed_707_: u8 = 0;
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_701__boxed_707_ = (leanh::lean_unbox(v_dir_704_) as u8);
    v_res_708_ =
        l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_701__boxed_707_, v_x_705_, v_prec_706_);
    leanh::lean_dec(v_prec_706_);
    return v_res_708_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent(
    mut v_dir_709_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = leanh::lean_box((v_dir_709_) as usize);
    v___x_711_ = leanh::lean_alloc_closure(
        l_Std_Http_Protocol_H1_instReprEvent_repr___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_711_, 0, v___x_710_);
    return v___x_711_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent___boxed(
    mut v_dir_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_5__boxed_713_: u8 = 0;
    let mut v_res_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_713_ = (leanh::lean_unbox(v_dir_712_) as u8);
    v_res_714_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_5__boxed_713_);
    return v_res_714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Event(
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
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Event(
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
pub unsafe fn initialize_Std_Http_Protocol_H1_Event(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Std_Http_Protocol_H1_Event(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Event(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Event(builtin);
}