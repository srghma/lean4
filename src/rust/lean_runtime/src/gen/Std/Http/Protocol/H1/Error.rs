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
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_string_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value: LeanStringObject<43> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 104, 101, 97, 100, 101, 114, 115, 84, 111, 111, 76,
            97, 114, 103, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 116, 111, 111, 77, 97, 110, 121, 72, 101, 97, 100,
            101, 114, 115, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 98, 97, 100, 77, 101, 115, 115, 97, 103, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110, 67,
            108, 111, 115, 101, 100, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 67, 104, 117,
            110, 107, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101,
            100, 86, 101, 114, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 117, 114, 105, 84, 111, 111, 76, 111, 110, 103, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 101, 110, 116, 105, 116, 121, 84, 111, 111, 76, 97,
            114, 103, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 116, 105, 109, 101, 111, 117, 116, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 72, 101, 97, 100,
            101, 114, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108, 105, 100, 83, 116, 97, 116,
            117, 115, 76, 105, 110, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value)
        as *mut LeanObject;
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 114, 114, 111, 114, 46, 111, 116, 104, 101, 114, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprError_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprError___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Protocol_H1_instReprError_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_instReprError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Protocol_H1_instReprError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprError___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instBEqError___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Protocol_H1_instBEqError_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_instBEqError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqError___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Protocol_H1_instBEqError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instBEqError___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value: LeanStringObject<
    20,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value: LeanStringObject<
    15,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value: LeanStringObject<
    17,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value: LeanStringObject<
    20,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value: LeanStringObject<
    18,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value: LeanStringObject<
    17,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value: LeanStringObject<
    18,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instToStringError___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_instToStringError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Protocol_H1_instToStringError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instToStringError___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorIdx(
    mut v_x_365_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_365_) {
        0 => {
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            v___x_366_ = lean_unsigned_to_nat(0);
            return v___x_366_;
        }
        1 => {
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            v___x_367_ = lean_unsigned_to_nat(1);
            return v___x_367_;
        }
        2 => {
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            v___x_368_ = lean_unsigned_to_nat(2);
            return v___x_368_;
        }
        3 => {
            let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
            v___x_369_ = lean_unsigned_to_nat(3);
            return v___x_369_;
        }
        4 => {
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            v___x_370_ = lean_unsigned_to_nat(4);
            return v___x_370_;
        }
        5 => {
            let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
            v___x_371_ = lean_unsigned_to_nat(5);
            return v___x_371_;
        }
        6 => {
            let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
            v___x_372_ = lean_unsigned_to_nat(6);
            return v___x_372_;
        }
        7 => {
            let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
            v___x_373_ = lean_unsigned_to_nat(7);
            return v___x_373_;
        }
        8 => {
            let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
            v___x_374_ = lean_unsigned_to_nat(8);
            return v___x_374_;
        }
        9 => {
            let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
            v___x_375_ = lean_unsigned_to_nat(9);
            return v___x_375_;
        }
        10 => {
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            v___x_376_ = lean_unsigned_to_nat(10);
            return v___x_376_;
        }
        _ => {
            let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
            v___x_377_ = lean_unsigned_to_nat(11);
            return v___x_377_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorIdx___boxed(
    mut v_x_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_379_: *mut LeanObject = core::ptr::null_mut();
    v_res_379_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_378_);
    lean_dec(v_x_378_);
    return v_res_379_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim___redArg(
    mut v_t_380_: *mut LeanObject,
    mut v_k_381_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_380_) == 11 {
        let mut v_message_382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
        v_message_382_ = lean_ctor_get(v_t_380_, 0);
        lean_inc_ref(v_message_382_);
        lean_dec_ref_known(v_t_380_, 1);
        v___x_383_ = lean_apply_1(v_k_381_, v_message_382_);
        return v___x_383_;
    } else {
        lean_dec(v_t_380_);
        return v_k_381_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim(
    mut v_motive_384_: *mut LeanObject,
    mut v_ctorIdx_385_: *mut LeanObject,
    mut v_t_386_: *mut LeanObject,
    mut v_h_387_: *mut LeanObject,
    mut v_k_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_386_, v_k_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_ctorElim___boxed(
    mut v_motive_390_: *mut LeanObject,
    mut v_ctorIdx_391_: *mut LeanObject,
    mut v_t_392_: *mut LeanObject,
    mut v_h_393_: *mut LeanObject,
    mut v_k_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_395_: *mut LeanObject = core::ptr::null_mut();
    v_res_395_ = l_Std_Http_Protocol_H1_Error_ctorElim(
        v_motive_390_,
        v_ctorIdx_391_,
        v_t_392_,
        v_h_393_,
        v_k_394_,
    );
    lean_dec(v_ctorIdx_391_);
    return v_res_395_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim___redArg(
    mut v_t_396_: *mut LeanObject,
    mut v_invalidStatusLine_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_396_, v_invalidStatusLine_397_);
    return v___x_398_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim(
    mut v_motive_399_: *mut LeanObject,
    mut v_t_400_: *mut LeanObject,
    mut v_h_401_: *mut LeanObject,
    mut v_invalidStatusLine_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v___x_403_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_400_, v_invalidStatusLine_402_);
    return v___x_403_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidHeader_elim___redArg(
    mut v_t_404_: *mut LeanObject,
    mut v_invalidHeader_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_404_, v_invalidHeader_405_);
    return v___x_406_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidHeader_elim(
    mut v_motive_407_: *mut LeanObject,
    mut v_t_408_: *mut LeanObject,
    mut v_h_409_: *mut LeanObject,
    mut v_invalidHeader_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_408_, v_invalidHeader_410_);
    return v___x_411_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_timeout_elim___redArg(
    mut v_t_412_: *mut LeanObject,
    mut v_timeout_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_412_, v_timeout_413_);
    return v___x_414_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_timeout_elim(
    mut v_motive_415_: *mut LeanObject,
    mut v_t_416_: *mut LeanObject,
    mut v_h_417_: *mut LeanObject,
    mut v_timeout_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_416_, v_timeout_418_);
    return v___x_419_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_entityTooLarge_elim___redArg(
    mut v_t_420_: *mut LeanObject,
    mut v_entityTooLarge_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_420_, v_entityTooLarge_421_);
    return v___x_422_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_entityTooLarge_elim(
    mut v_motive_423_: *mut LeanObject,
    mut v_t_424_: *mut LeanObject,
    mut v_h_425_: *mut LeanObject,
    mut v_entityTooLarge_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_424_, v_entityTooLarge_426_);
    return v___x_427_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_uriTooLong_elim___redArg(
    mut v_t_428_: *mut LeanObject,
    mut v_uriTooLong_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_428_, v_uriTooLong_429_);
    return v___x_430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_uriTooLong_elim(
    mut v_motive_431_: *mut LeanObject,
    mut v_t_432_: *mut LeanObject,
    mut v_h_433_: *mut LeanObject,
    mut v_uriTooLong_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_432_, v_uriTooLong_434_);
    return v___x_435_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim___redArg(
    mut v_t_436_: *mut LeanObject,
    mut v_unsupportedVersion_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ =
        l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_436_, v_unsupportedVersion_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim(
    mut v_motive_439_: *mut LeanObject,
    mut v_t_440_: *mut LeanObject,
    mut v_h_441_: *mut LeanObject,
    mut v_unsupportedVersion_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_443_ =
        l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_440_, v_unsupportedVersion_442_);
    return v___x_443_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(
    mut v_t_444_: *mut LeanObject,
    mut v_invalidChunk_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_444_, v_invalidChunk_445_);
    return v___x_446_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_invalidChunk_elim(
    mut v_motive_447_: *mut LeanObject,
    mut v_t_448_: *mut LeanObject,
    mut v_h_449_: *mut LeanObject,
    mut v_invalidChunk_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v___x_451_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_448_, v_invalidChunk_450_);
    return v___x_451_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(
    mut v_t_452_: *mut LeanObject,
    mut v_connectionClosed_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    v___x_454_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_452_, v_connectionClosed_453_);
    return v___x_454_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_connectionClosed_elim(
    mut v_motive_455_: *mut LeanObject,
    mut v_t_456_: *mut LeanObject,
    mut v_h_457_: *mut LeanObject,
    mut v_connectionClosed_458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___x_459_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_456_, v_connectionClosed_458_);
    return v___x_459_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(
    mut v_t_460_: *mut LeanObject,
    mut v_badMessage_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    v___x_462_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_460_, v_badMessage_461_);
    return v___x_462_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_badMessage_elim(
    mut v_motive_463_: *mut LeanObject,
    mut v_t_464_: *mut LeanObject,
    mut v_h_465_: *mut LeanObject,
    mut v_badMessage_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_464_, v_badMessage_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(
    mut v_t_468_: *mut LeanObject,
    mut v_tooManyHeaders_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_468_, v_tooManyHeaders_469_);
    return v___x_470_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(
    mut v_motive_471_: *mut LeanObject,
    mut v_t_472_: *mut LeanObject,
    mut v_h_473_: *mut LeanObject,
    mut v_tooManyHeaders_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_472_, v_tooManyHeaders_474_);
    return v___x_475_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(
    mut v_t_476_: *mut LeanObject,
    mut v_headersTooLarge_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_476_, v_headersTooLarge_477_);
    return v___x_478_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(
    mut v_motive_479_: *mut LeanObject,
    mut v_t_480_: *mut LeanObject,
    mut v_h_481_: *mut LeanObject,
    mut v_headersTooLarge_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_480_, v_headersTooLarge_482_);
    return v___x_483_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_other_elim___redArg(
    mut v_t_484_: *mut LeanObject,
    mut v_other_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_484_, v_other_485_);
    return v___x_486_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Error_other_elim(
    mut v_motive_487_: *mut LeanObject,
    mut v_t_488_: *mut LeanObject,
    mut v_h_489_: *mut LeanObject,
    mut v_other_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    v___x_491_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_488_, v_other_490_);
    return v___x_491_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22() -> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_525_ = lean_unsigned_to_nat(2);
    v___x_526_ = lean_nat_to_int(v___x_525_);
    return v___x_526_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23() -> *mut LeanObject {
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v___x_527_ = lean_unsigned_to_nat(1);
    v___x_528_ = lean_nat_to_int(v___x_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprError_repr(
    mut v_x_535_: *mut LeanObject,
    mut v_prec_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: u8 = 0;
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: u8 = 0;
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: u8 = 0;
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_message_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___y_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_535_) {
                0 => {
                    v___x_614_ = lean_unsigned_to_nat(1024);
                    v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_536_);
                    if v___x_615_ == 0 {
                        v___x_616_ = lean_obj_once(
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
                        v___x_617_ = lean_obj_once(
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
                    v___x_618_ = lean_unsigned_to_nat(1024);
                    v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_536_);
                    if v___x_619_ == 0 {
                        v___x_620_ = lean_obj_once(
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
                        v___x_621_ = lean_obj_once(
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
                    v___x_622_ = lean_unsigned_to_nat(1024);
                    v___x_623_ = lean_nat_dec_le(v___x_622_, v_prec_536_);
                    if v___x_623_ == 0 {
                        v___x_624_ = lean_obj_once(
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
                        v___x_625_ = lean_obj_once(
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
                    v___x_626_ = lean_unsigned_to_nat(1024);
                    v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_536_);
                    if v___x_627_ == 0 {
                        v___x_628_ = lean_obj_once(
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
                        v___x_629_ = lean_obj_once(
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
                    v___x_630_ = lean_unsigned_to_nat(1024);
                    v___x_631_ = lean_nat_dec_le(v___x_630_, v_prec_536_);
                    if v___x_631_ == 0 {
                        v___x_632_ = lean_obj_once(
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
                        v___x_633_ = lean_obj_once(
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
                    v___x_634_ = lean_unsigned_to_nat(1024);
                    v___x_635_ = lean_nat_dec_le(v___x_634_, v_prec_536_);
                    if v___x_635_ == 0 {
                        v___x_636_ = lean_obj_once(
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
                        v___x_637_ = lean_obj_once(
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
                    v___x_638_ = lean_unsigned_to_nat(1024);
                    v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_536_);
                    if v___x_639_ == 0 {
                        v___x_640_ = lean_obj_once(
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
                        v___x_641_ = lean_obj_once(
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
                    v___x_642_ = lean_unsigned_to_nat(1024);
                    v___x_643_ = lean_nat_dec_le(v___x_642_, v_prec_536_);
                    if v___x_643_ == 0 {
                        v___x_644_ = lean_obj_once(
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
                        v___x_645_ = lean_obj_once(
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
                    v___x_646_ = lean_unsigned_to_nat(1024);
                    v___x_647_ = lean_nat_dec_le(v___x_646_, v_prec_536_);
                    if v___x_647_ == 0 {
                        v___x_648_ = lean_obj_once(
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
                        v___x_649_ = lean_obj_once(
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
                    v___x_650_ = lean_unsigned_to_nat(1024);
                    v___x_651_ = lean_nat_dec_le(v___x_650_, v_prec_536_);
                    if v___x_651_ == 0 {
                        v___x_652_ = lean_obj_once(
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
                        v___x_653_ = lean_obj_once(
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
                    v___x_654_ = lean_unsigned_to_nat(1024);
                    v___x_655_ = lean_nat_dec_le(v___x_654_, v_prec_536_);
                    if v___x_655_ == 0 {
                        v___x_656_ = lean_obj_once(
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
                        v___x_657_ = lean_obj_once(
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
                    v_message_658_ = lean_ctor_get(v_x_535_, 0);
                    v_isSharedCheck_678_ = (!lean_is_exclusive(v_x_535_)) as u8;
                    if v_isSharedCheck_678_ == 0 {
                        v___x_660_ = v_x_535_;
                        v_isShared_661_ = v_isSharedCheck_678_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_message_658_);
                        lean_dec(v_x_535_);
                        v___x_660_ = lean_box(0);
                        v_isShared_661_ = v_isSharedCheck_678_;
                        state = 12;
                        continue;
                    }
                }
            },
            1 => {
                v___x_539_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__1;
                lean_inc(v___y_538_);
                v___x_540_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_540_, 0, v___y_538_);
                lean_ctor_set(v___x_540_, 1, v___x_539_);
                v___x_541_ = 0;
                v___x_542_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_542_, 0, v___x_540_);
                lean_ctor_set_uint8(
                    v___x_542_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_541_,
                );
                v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_536_);
                return v___x_543_;
            }
            2 => {
                v___x_546_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__3;
                lean_inc(v___y_545_);
                v___x_547_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_547_, 0, v___y_545_);
                lean_ctor_set(v___x_547_, 1, v___x_546_);
                v___x_548_ = 0;
                v___x_549_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_549_, 0, v___x_547_);
                lean_ctor_set_uint8(
                    v___x_549_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_548_,
                );
                v___x_550_ = l_Repr_addAppParen(v___x_549_, v_prec_536_);
                return v___x_550_;
            }
            3 => {
                v___x_553_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__5;
                lean_inc(v___y_552_);
                v___x_554_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_554_, 0, v___y_552_);
                lean_ctor_set(v___x_554_, 1, v___x_553_);
                v___x_555_ = 0;
                v___x_556_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_556_, 0, v___x_554_);
                lean_ctor_set_uint8(
                    v___x_556_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_555_,
                );
                v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_536_);
                return v___x_557_;
            }
            4 => {
                v___x_560_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__7;
                lean_inc(v___y_559_);
                v___x_561_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_561_, 0, v___y_559_);
                lean_ctor_set(v___x_561_, 1, v___x_560_);
                v___x_562_ = 0;
                v___x_563_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_563_, 0, v___x_561_);
                lean_ctor_set_uint8(
                    v___x_563_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_562_,
                );
                v___x_564_ = l_Repr_addAppParen(v___x_563_, v_prec_536_);
                return v___x_564_;
            }
            5 => {
                v___x_567_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__9;
                lean_inc(v___y_566_);
                v___x_568_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_568_, 0, v___y_566_);
                lean_ctor_set(v___x_568_, 1, v___x_567_);
                v___x_569_ = 0;
                v___x_570_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_570_, 0, v___x_568_);
                lean_ctor_set_uint8(
                    v___x_570_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_569_,
                );
                v___x_571_ = l_Repr_addAppParen(v___x_570_, v_prec_536_);
                return v___x_571_;
            }
            6 => {
                v___x_574_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__11;
                lean_inc(v___y_573_);
                v___x_575_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_575_, 0, v___y_573_);
                lean_ctor_set(v___x_575_, 1, v___x_574_);
                v___x_576_ = 0;
                v___x_577_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_577_, 0, v___x_575_);
                lean_ctor_set_uint8(
                    v___x_577_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_576_,
                );
                v___x_578_ = l_Repr_addAppParen(v___x_577_, v_prec_536_);
                return v___x_578_;
            }
            7 => {
                v___x_581_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__13;
                lean_inc(v___y_580_);
                v___x_582_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_582_, 0, v___y_580_);
                lean_ctor_set(v___x_582_, 1, v___x_581_);
                v___x_583_ = 0;
                v___x_584_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_584_, 0, v___x_582_);
                lean_ctor_set_uint8(
                    v___x_584_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_583_,
                );
                v___x_585_ = l_Repr_addAppParen(v___x_584_, v_prec_536_);
                return v___x_585_;
            }
            8 => {
                v___x_588_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__15;
                lean_inc(v___y_587_);
                v___x_589_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_589_, 0, v___y_587_);
                lean_ctor_set(v___x_589_, 1, v___x_588_);
                v___x_590_ = 0;
                v___x_591_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_591_, 0, v___x_589_);
                lean_ctor_set_uint8(
                    v___x_591_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_590_,
                );
                v___x_592_ = l_Repr_addAppParen(v___x_591_, v_prec_536_);
                return v___x_592_;
            }
            9 => {
                v___x_595_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__17;
                lean_inc(v___y_594_);
                v___x_596_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_596_, 0, v___y_594_);
                lean_ctor_set(v___x_596_, 1, v___x_595_);
                v___x_597_ = 0;
                v___x_598_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_598_, 0, v___x_596_);
                lean_ctor_set_uint8(
                    v___x_598_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_597_,
                );
                v___x_599_ = l_Repr_addAppParen(v___x_598_, v_prec_536_);
                return v___x_599_;
            }
            10 => {
                v___x_602_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__19;
                lean_inc(v___y_601_);
                v___x_603_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_603_, 0, v___y_601_);
                lean_ctor_set(v___x_603_, 1, v___x_602_);
                v___x_604_ = 0;
                v___x_605_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_605_, 0, v___x_603_);
                lean_ctor_set_uint8(
                    v___x_605_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_536_);
                return v___x_606_;
            }
            11 => {
                v___x_609_ = l_Std_Http_Protocol_H1_instReprError_repr___closed__21;
                lean_inc(v___y_608_);
                v___x_610_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_610_, 0, v___y_608_);
                lean_ctor_set(v___x_610_, 1, v___x_609_);
                v___x_611_ = 0;
                v___x_612_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_612_, 0, v___x_610_);
                lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_611_,
                );
                v___x_613_ = l_Repr_addAppParen(v___x_612_, v_prec_536_);
                return v___x_613_;
            }
            12 => {
                v___x_674_ = lean_unsigned_to_nat(1024);
                v___x_675_ = lean_nat_dec_le(v___x_674_, v_prec_536_);
                if v___x_675_ == 0 {
                    v___x_676_ = lean_obj_once(
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
                    v___x_677_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_660_, 3);
                    lean_ctor_set(v___x_660_, 0, v___x_665_);
                    v___x_667_ = v___x_660_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_665_);
                    v___x_667_ = v_reuseFailAlloc_673_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_668_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_668_, 0, v___x_664_);
                lean_ctor_set(v___x_668_, 1, v___x_667_);
                lean_inc(v___y_663_);
                v___x_669_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_669_, 0, v___y_663_);
                lean_ctor_set(v___x_669_, 1, v___x_668_);
                v___x_670_ = 0;
                v___x_671_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_671_, 0, v___x_669_);
                lean_ctor_set_uint8(
                    v___x_671_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_679_: *mut LeanObject,
    mut v_prec_680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_681_: *mut LeanObject = core::ptr::null_mut();
    v_res_681_ = l_Std_Http_Protocol_H1_instReprError_repr(v_x_679_, v_prec_680_);
    lean_dec(v_prec_680_);
    return v_res_681_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqError_beq(
    mut v_x_684_: *mut LeanObject,
    mut v_x_685_: *mut LeanObject,
) -> u8 {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    v___x_686_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_684_);
    v___x_687_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_685_);
    v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
    lean_dec(v___x_687_);
    lean_dec(v___x_686_);
    if v___x_688_ == 0 {
        return v___x_688_;
    } else {
        if lean_obj_tag(v_x_684_) == 11 {
            let mut v_message_689_: *mut LeanObject = core::ptr::null_mut();
            let mut v_message_690_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_691_: u8 = 0;
            v_message_689_ = lean_ctor_get(v_x_684_, 0);
            v_message_690_ = lean_ctor_get(v_x_685_, 0);
            v___x_691_ = lean_string_dec_eq(v_message_689_, v_message_690_);
            return v___x_691_;
        } else {
            return v___x_688_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instBEqError_beq___boxed(
    mut v_x_692_: *mut LeanObject,
    mut v_x_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: u8 = 0;
    let mut v_r_695_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_692_, v_x_693_);
    lean_dec(v_x_693_);
    lean_dec(v_x_692_);
    v_r_695_ = lean_box((v_res_694_) as usize);
    return v_r_695_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instToStringError___lam__0(
    mut v_x_710_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_710_) {
        0 => {
            let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
            v___x_711_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0;
            return v___x_711_;
        }
        1 => {
            let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
            v___x_712_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1;
            return v___x_712_;
        }
        2 => {
            let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
            v___x_713_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2;
            return v___x_713_;
        }
        3 => {
            let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
            v___x_714_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3;
            return v___x_714_;
        }
        4 => {
            let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
            v___x_715_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4;
            return v___x_715_;
        }
        5 => {
            let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
            v___x_716_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5;
            return v___x_716_;
        }
        6 => {
            let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
            v___x_717_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6;
            return v___x_717_;
        }
        7 => {
            let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
            v___x_718_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7;
            return v___x_718_;
        }
        8 => {
            let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
            v___x_719_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8;
            return v___x_719_;
        }
        9 => {
            let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
            v___x_720_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9;
            return v___x_720_;
        }
        10 => {
            let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
            v___x_721_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10;
            return v___x_721_;
        }
        _ => {
            let mut v_message_722_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
            v_message_722_ = lean_ctor_get(v_x_710_, 0);
            v___x_723_ = l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11;
            v___x_724_ = lean_string_append(v___x_723_, v_message_722_);
            return v___x_724_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(
    mut v_x_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Http_Protocol_H1_instToStringError___lam__0(v_x_725_);
    lean_dec(v_x_725_);
    return v_res_726_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Protocol_H1_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Error(builtin);
}
