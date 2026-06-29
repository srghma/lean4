// Lean compiler output
// Module: Std.Http.Data.Method
// Imports: Init.Data.ToString Std.Http.Internal
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::{lean_string_append, lean_string_to_utf8};
use crate::ffi::{
    lean_array_push, lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_panic_fn_borrowed, lean_string_dec_eq,
};
pub static l_Std_Http_instReprMethod_repr___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 97, 99, 108,
            0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__2_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 98, 97, 115,
            101, 108, 105, 110, 101, 67, 111, 110, 116, 114, 111, 108, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__4_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 98, 105, 110,
            100, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__6_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 99, 104, 101,
            99, 107, 105, 110, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__8_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 99, 104, 101,
            99, 107, 111, 117, 116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__10_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 99, 111, 110,
            110, 101, 99, 116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__12_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 99, 111, 112,
            121, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__14_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 100, 101,
            108, 101, 116, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__16_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 103, 101,
            116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__18_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 104, 101, 97,
            100, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__20_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 108, 97, 98,
            101, 108, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__22_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 108, 105,
            110, 107, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__24_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 108, 111, 99,
            107, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__25_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__26_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 101,
            114, 103, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__28_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 107, 97,
            99, 116, 105, 118, 105, 116, 121, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__29_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__30_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 107, 99,
            97, 108, 101, 110, 100, 97, 114, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__31_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__32_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 107, 99,
            111, 108, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__33_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__32_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__34_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 107,
            114, 101, 100, 105, 114, 101, 99, 116, 114, 101, 102, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__35_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__34_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__36_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 107,
            119, 111, 114, 107, 115, 112, 97, 99, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__37_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__36_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__38_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 109, 111,
            118, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__39_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__38_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__40_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 111, 112,
            116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__41_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__40_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__42_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 111, 114,
            100, 101, 114, 112, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__43_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__42_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__44_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 97, 116,
            99, 104, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__45_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__44_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__46_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 111,
            115, 116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__47_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__46_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__48_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 114,
            105, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__49_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__48_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__50_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 114,
            111, 112, 102, 105, 110, 100, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__51_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__50_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__52_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 114,
            111, 112, 112, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__53_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__52_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__54_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 112, 117,
            116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__55_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__54_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__56_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 113, 117,
            101, 114, 121, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__57_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__56_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__58_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 114, 101, 98,
            105, 110, 100, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__59_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__58_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__60_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 114, 101,
            112, 111, 114, 116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__61_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__60_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__62_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 115, 101, 97,
            114, 99, 104, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__63_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__62_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__64_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 116, 114, 97,
            99, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__65_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__64_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__65: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__66_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 110, 98,
            105, 110, 100, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__66: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__67_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__66_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__67: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__68_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 110, 99,
            104, 101, 99, 107, 111, 117, 116, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__68: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__69_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__68_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__69: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__70_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 110,
            108, 105, 110, 107, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__70: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__71_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__70_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__71: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__72_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 110,
            108, 111, 99, 107, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__72: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__72_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__73_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__72_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__73: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__73_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__74_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 112,
            100, 97, 116, 101, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__74: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__75_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__74_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__75: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__75_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__76_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 117, 112,
            100, 97, 116, 101, 114, 101, 100, 105, 114, 101, 99, 116, 114, 101, 102, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__76: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__76_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__77_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__76_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__77: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__77_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__78_value: crate::leanh::LeanStringObject<31> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 118, 101,
            114, 115, 105, 111, 110, 67, 111, 110, 116, 114, 111, 108, 0,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__78: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__78_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprMethod_repr___closed__79_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__78_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprMethod_repr___closed__79: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod_repr___closed__79_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_instReprMethod_repr___closed__80_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprMethod_repr___closed__80: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_instReprMethod_repr___closed__81_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprMethod_repr___closed__81: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprMethod___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprMethod_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprMethod___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instReprMethod: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprMethod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedMethod_default: u8 = 0;
pub static mut l_Std_Http_instInhabitedMethod: u8 = 0;
pub static l_Std_Http_instBEqMethod___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instBEqMethod_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instBEqMethod___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqMethod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instBEqMethod: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqMethod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__1_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__5_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__6_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__7_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__8_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__9_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__11_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__12_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__13_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__14_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__15_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__16_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__17_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__18_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__19_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__20_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__21_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__22_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__23_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__24_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__25_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__26_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__27_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__28_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__29_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__30_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__31_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__32_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__33_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__34_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__35_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__36_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__37_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__38_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__39_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Method_ofString_x3f___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__40_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__41_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__42_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__43_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__44_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__45_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__46_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__47_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__48_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__49_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__50_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__51_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((28 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__52_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__53_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__54_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__55_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__56_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__57_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__58_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__59_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__60_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__61_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((18 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__62_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__63_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__64_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__65_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__65: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__66_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__66: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__67_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__67: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__68_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((11 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__68: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__69_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__69: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__70_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((9 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__70: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__71_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__71: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__72_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((7 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__72: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__72_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__73_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__73: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__73_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__74_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__74: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__75_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__75: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__75_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__76_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__76: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__76_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__77_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__77: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__77_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__78_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Http_Method_ofString_x3f___closed__78: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__78_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x3f___closed__79_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Method_ofString_x3f___closed__79: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x3f___closed__79_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x21___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 77, 101, 116, 104, 111,
            100, 0,
        ],
    };
static mut l_Std_Http_Method_ofString_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x21___closed__1_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 77, 101, 116, 104, 111, 100, 46, 111, 102, 83,
            116, 114, 105, 110, 103, 33, 0,
        ],
    };
static mut l_Std_Http_Method_ofString_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_ofString_x21___closed__2_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            105, 110, 118, 97, 108, 105, 100, 32, 72, 84, 84, 80, 32, 109, 101, 116, 104, 111, 100,
            58, 32, 0,
        ],
    };
static mut l_Std_Http_Method_ofString_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_ofString_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Method_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Method_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Method_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Method_instEncodeV11___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Method_instEncodeV11___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Method_instEncodeV11___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_instEncodeV11___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Method_instEncodeV11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Method_instEncodeV11___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Method_ctorIdx(mut v_x_1725_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_1725_ {
        0 => {
            let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1726_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1726_;
        }
        1 => {
            let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1727_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1727_;
        }
        2 => {
            let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1728_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1728_;
        }
        3 => {
            let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1729_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1729_;
        }
        4 => {
            let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1730_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1730_;
        }
        5 => {
            let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1731_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1731_;
        }
        6 => {
            let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1732_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1732_;
        }
        7 => {
            let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1733_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1733_;
        }
        8 => {
            let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1734_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1734_;
        }
        9 => {
            let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1735_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1735_;
        }
        10 => {
            let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1736_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1736_;
        }
        11 => {
            let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1737_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1737_;
        }
        12 => {
            let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1738_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1738_;
        }
        13 => {
            let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1739_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_1739_;
        }
        14 => {
            let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1740_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_1740_;
        }
        15 => {
            let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1741_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_1741_;
        }
        16 => {
            let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1742_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_1742_;
        }
        17 => {
            let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1743_ = crate::leanh::lean_unsigned_to_nat(17);
            return v___x_1743_;
        }
        18 => {
            let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1744_ = crate::leanh::lean_unsigned_to_nat(18);
            return v___x_1744_;
        }
        19 => {
            let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1745_ = crate::leanh::lean_unsigned_to_nat(19);
            return v___x_1745_;
        }
        20 => {
            let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1746_ = crate::leanh::lean_unsigned_to_nat(20);
            return v___x_1746_;
        }
        21 => {
            let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1747_ = crate::leanh::lean_unsigned_to_nat(21);
            return v___x_1747_;
        }
        22 => {
            let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1748_ = crate::leanh::lean_unsigned_to_nat(22);
            return v___x_1748_;
        }
        23 => {
            let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1749_ = crate::leanh::lean_unsigned_to_nat(23);
            return v___x_1749_;
        }
        24 => {
            let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1750_ = crate::leanh::lean_unsigned_to_nat(24);
            return v___x_1750_;
        }
        25 => {
            let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1751_ = crate::leanh::lean_unsigned_to_nat(25);
            return v___x_1751_;
        }
        26 => {
            let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1752_ = crate::leanh::lean_unsigned_to_nat(26);
            return v___x_1752_;
        }
        27 => {
            let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1753_ = crate::leanh::lean_unsigned_to_nat(27);
            return v___x_1753_;
        }
        28 => {
            let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1754_ = crate::leanh::lean_unsigned_to_nat(28);
            return v___x_1754_;
        }
        29 => {
            let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1755_ = crate::leanh::lean_unsigned_to_nat(29);
            return v___x_1755_;
        }
        30 => {
            let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1756_ = crate::leanh::lean_unsigned_to_nat(30);
            return v___x_1756_;
        }
        31 => {
            let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1757_ = crate::leanh::lean_unsigned_to_nat(31);
            return v___x_1757_;
        }
        32 => {
            let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1758_ = crate::leanh::lean_unsigned_to_nat(32);
            return v___x_1758_;
        }
        33 => {
            let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1759_ = crate::leanh::lean_unsigned_to_nat(33);
            return v___x_1759_;
        }
        34 => {
            let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1760_ = crate::leanh::lean_unsigned_to_nat(34);
            return v___x_1760_;
        }
        35 => {
            let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1761_ = crate::leanh::lean_unsigned_to_nat(35);
            return v___x_1761_;
        }
        36 => {
            let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1762_ = crate::leanh::lean_unsigned_to_nat(36);
            return v___x_1762_;
        }
        37 => {
            let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1763_ = crate::leanh::lean_unsigned_to_nat(37);
            return v___x_1763_;
        }
        38 => {
            let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1764_ = crate::leanh::lean_unsigned_to_nat(38);
            return v___x_1764_;
        }
        _ => {
            let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1765_ = crate::leanh::lean_unsigned_to_nat(39);
            return v___x_1765_;
        }
    }
}
pub unsafe fn l_Std_Http_Method_ctorIdx___boxed(
    mut v_x_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1767_: u8 = 0;
    let mut v_res_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1767_ = (crate::leanh::lean_unbox(v_x_1766_) as u8);
    v_res_1768_ = l_Std_Http_Method_ctorIdx(v_x_boxed_1767_);
    return v_res_1768_;
}
pub unsafe fn l_Std_Http_Method_toCtorIdx(mut v_x_1769_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l_Std_Http_Method_ctorIdx(v_x_1769_);
    return v___x_1770_;
}
pub unsafe fn l_Std_Http_Method_toCtorIdx___boxed(
    mut v_x_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1772_: u8 = 0;
    let mut v_res_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1772_ = (crate::leanh::lean_unbox(v_x_1771_) as u8);
    v_res_1773_ = l_Std_Http_Method_toCtorIdx(v_x_4__boxed_1772_);
    return v_res_1773_;
}
pub unsafe fn l_Std_Http_Method_ctorElim___redArg(
    mut v_k_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1774_);
    return v_k_1774_;
}
pub unsafe fn l_Std_Http_Method_ctorElim___redArg___boxed(
    mut v_k_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Std_Http_Method_ctorElim___redArg(v_k_1775_);
    crate::leanh::lean_dec(v_k_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Std_Http_Method_ctorElim(
    mut v_motive_1777_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1778_: *mut crate::leanh::LeanObject,
    mut v_t_1779_: u8,
    mut v_h_1780_: *mut crate::leanh::LeanObject,
    mut v_k_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1781_);
    return v_k_1781_;
}
pub unsafe fn l_Std_Http_Method_ctorElim___boxed(
    mut v_motive_1782_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1783_: *mut crate::leanh::LeanObject,
    mut v_t_1784_: *mut crate::leanh::LeanObject,
    mut v_h_1785_: *mut crate::leanh::LeanObject,
    mut v_k_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1787_: u8 = 0;
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1787_ = (crate::leanh::lean_unbox(v_t_1784_) as u8);
    v_res_1788_ = l_Std_Http_Method_ctorElim(
        v_motive_1782_,
        v_ctorIdx_1783_,
        v_t_boxed_1787_,
        v_h_1785_,
        v_k_1786_,
    );
    crate::leanh::lean_dec(v_k_1786_);
    crate::leanh::lean_dec(v_ctorIdx_1783_);
    return v_res_1788_;
}
pub unsafe fn l_Std_Http_Method_acl_elim___redArg(
    mut v_acl_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_acl_1789_);
    return v_acl_1789_;
}
pub unsafe fn l_Std_Http_Method_acl_elim___redArg___boxed(
    mut v_acl_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1791_ = l_Std_Http_Method_acl_elim___redArg(v_acl_1790_);
    crate::leanh::lean_dec(v_acl_1790_);
    return v_res_1791_;
}
pub unsafe fn l_Std_Http_Method_acl_elim(
    mut v_motive_1792_: *mut crate::leanh::LeanObject,
    mut v_t_1793_: u8,
    mut v_h_1794_: *mut crate::leanh::LeanObject,
    mut v_acl_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_acl_1795_);
    return v_acl_1795_;
}
pub unsafe fn l_Std_Http_Method_acl_elim___boxed(
    mut v_motive_1796_: *mut crate::leanh::LeanObject,
    mut v_t_1797_: *mut crate::leanh::LeanObject,
    mut v_h_1798_: *mut crate::leanh::LeanObject,
    mut v_acl_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1800_: u8 = 0;
    let mut v_res_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1800_ = (crate::leanh::lean_unbox(v_t_1797_) as u8);
    v_res_1801_ =
        l_Std_Http_Method_acl_elim(v_motive_1796_, v_t_boxed_1800_, v_h_1798_, v_acl_1799_);
    crate::leanh::lean_dec(v_acl_1799_);
    return v_res_1801_;
}
pub unsafe fn l_Std_Http_Method_baselineControl_elim___redArg(
    mut v_baselineControl_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_baselineControl_1802_);
    return v_baselineControl_1802_;
}
pub unsafe fn l_Std_Http_Method_baselineControl_elim___redArg___boxed(
    mut v_baselineControl_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Std_Http_Method_baselineControl_elim___redArg(v_baselineControl_1803_);
    crate::leanh::lean_dec(v_baselineControl_1803_);
    return v_res_1804_;
}
pub unsafe fn l_Std_Http_Method_baselineControl_elim(
    mut v_motive_1805_: *mut crate::leanh::LeanObject,
    mut v_t_1806_: u8,
    mut v_h_1807_: *mut crate::leanh::LeanObject,
    mut v_baselineControl_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_baselineControl_1808_);
    return v_baselineControl_1808_;
}
pub unsafe fn l_Std_Http_Method_baselineControl_elim___boxed(
    mut v_motive_1809_: *mut crate::leanh::LeanObject,
    mut v_t_1810_: *mut crate::leanh::LeanObject,
    mut v_h_1811_: *mut crate::leanh::LeanObject,
    mut v_baselineControl_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1813_: u8 = 0;
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1813_ = (crate::leanh::lean_unbox(v_t_1810_) as u8);
    v_res_1814_ = l_Std_Http_Method_baselineControl_elim(
        v_motive_1809_,
        v_t_boxed_1813_,
        v_h_1811_,
        v_baselineControl_1812_,
    );
    crate::leanh::lean_dec(v_baselineControl_1812_);
    return v_res_1814_;
}
pub unsafe fn l_Std_Http_Method_bind_elim___redArg(
    mut v_bind_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_bind_1815_);
    return v_bind_1815_;
}
pub unsafe fn l_Std_Http_Method_bind_elim___redArg___boxed(
    mut v_bind_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Std_Http_Method_bind_elim___redArg(v_bind_1816_);
    crate::leanh::lean_dec(v_bind_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Std_Http_Method_bind_elim(
    mut v_motive_1818_: *mut crate::leanh::LeanObject,
    mut v_t_1819_: u8,
    mut v_h_1820_: *mut crate::leanh::LeanObject,
    mut v_bind_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_bind_1821_);
    return v_bind_1821_;
}
pub unsafe fn l_Std_Http_Method_bind_elim___boxed(
    mut v_motive_1822_: *mut crate::leanh::LeanObject,
    mut v_t_1823_: *mut crate::leanh::LeanObject,
    mut v_h_1824_: *mut crate::leanh::LeanObject,
    mut v_bind_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1826_: u8 = 0;
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1826_ = (crate::leanh::lean_unbox(v_t_1823_) as u8);
    v_res_1827_ =
        l_Std_Http_Method_bind_elim(v_motive_1822_, v_t_boxed_1826_, v_h_1824_, v_bind_1825_);
    crate::leanh::lean_dec(v_bind_1825_);
    return v_res_1827_;
}
pub unsafe fn l_Std_Http_Method_checkin_elim___redArg(
    mut v_checkin_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_checkin_1828_);
    return v_checkin_1828_;
}
pub unsafe fn l_Std_Http_Method_checkin_elim___redArg___boxed(
    mut v_checkin_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Std_Http_Method_checkin_elim___redArg(v_checkin_1829_);
    crate::leanh::lean_dec(v_checkin_1829_);
    return v_res_1830_;
}
pub unsafe fn l_Std_Http_Method_checkin_elim(
    mut v_motive_1831_: *mut crate::leanh::LeanObject,
    mut v_t_1832_: u8,
    mut v_h_1833_: *mut crate::leanh::LeanObject,
    mut v_checkin_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_checkin_1834_);
    return v_checkin_1834_;
}
pub unsafe fn l_Std_Http_Method_checkin_elim___boxed(
    mut v_motive_1835_: *mut crate::leanh::LeanObject,
    mut v_t_1836_: *mut crate::leanh::LeanObject,
    mut v_h_1837_: *mut crate::leanh::LeanObject,
    mut v_checkin_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1839_: u8 = 0;
    let mut v_res_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1839_ = (crate::leanh::lean_unbox(v_t_1836_) as u8);
    v_res_1840_ =
        l_Std_Http_Method_checkin_elim(v_motive_1835_, v_t_boxed_1839_, v_h_1837_, v_checkin_1838_);
    crate::leanh::lean_dec(v_checkin_1838_);
    return v_res_1840_;
}
pub unsafe fn l_Std_Http_Method_checkout_elim___redArg(
    mut v_checkout_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_checkout_1841_);
    return v_checkout_1841_;
}
pub unsafe fn l_Std_Http_Method_checkout_elim___redArg___boxed(
    mut v_checkout_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Std_Http_Method_checkout_elim___redArg(v_checkout_1842_);
    crate::leanh::lean_dec(v_checkout_1842_);
    return v_res_1843_;
}
pub unsafe fn l_Std_Http_Method_checkout_elim(
    mut v_motive_1844_: *mut crate::leanh::LeanObject,
    mut v_t_1845_: u8,
    mut v_h_1846_: *mut crate::leanh::LeanObject,
    mut v_checkout_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_checkout_1847_);
    return v_checkout_1847_;
}
pub unsafe fn l_Std_Http_Method_checkout_elim___boxed(
    mut v_motive_1848_: *mut crate::leanh::LeanObject,
    mut v_t_1849_: *mut crate::leanh::LeanObject,
    mut v_h_1850_: *mut crate::leanh::LeanObject,
    mut v_checkout_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1852_: u8 = 0;
    let mut v_res_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1852_ = (crate::leanh::lean_unbox(v_t_1849_) as u8);
    v_res_1853_ = l_Std_Http_Method_checkout_elim(
        v_motive_1848_,
        v_t_boxed_1852_,
        v_h_1850_,
        v_checkout_1851_,
    );
    crate::leanh::lean_dec(v_checkout_1851_);
    return v_res_1853_;
}
pub unsafe fn l_Std_Http_Method_connect_elim___redArg(
    mut v_connect_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_connect_1854_);
    return v_connect_1854_;
}
pub unsafe fn l_Std_Http_Method_connect_elim___redArg___boxed(
    mut v_connect_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Std_Http_Method_connect_elim___redArg(v_connect_1855_);
    crate::leanh::lean_dec(v_connect_1855_);
    return v_res_1856_;
}
pub unsafe fn l_Std_Http_Method_connect_elim(
    mut v_motive_1857_: *mut crate::leanh::LeanObject,
    mut v_t_1858_: u8,
    mut v_h_1859_: *mut crate::leanh::LeanObject,
    mut v_connect_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_connect_1860_);
    return v_connect_1860_;
}
pub unsafe fn l_Std_Http_Method_connect_elim___boxed(
    mut v_motive_1861_: *mut crate::leanh::LeanObject,
    mut v_t_1862_: *mut crate::leanh::LeanObject,
    mut v_h_1863_: *mut crate::leanh::LeanObject,
    mut v_connect_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1865_: u8 = 0;
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1865_ = (crate::leanh::lean_unbox(v_t_1862_) as u8);
    v_res_1866_ =
        l_Std_Http_Method_connect_elim(v_motive_1861_, v_t_boxed_1865_, v_h_1863_, v_connect_1864_);
    crate::leanh::lean_dec(v_connect_1864_);
    return v_res_1866_;
}
pub unsafe fn l_Std_Http_Method_copy_elim___redArg(
    mut v_copy_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_copy_1867_);
    return v_copy_1867_;
}
pub unsafe fn l_Std_Http_Method_copy_elim___redArg___boxed(
    mut v_copy_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Std_Http_Method_copy_elim___redArg(v_copy_1868_);
    crate::leanh::lean_dec(v_copy_1868_);
    return v_res_1869_;
}
pub unsafe fn l_Std_Http_Method_copy_elim(
    mut v_motive_1870_: *mut crate::leanh::LeanObject,
    mut v_t_1871_: u8,
    mut v_h_1872_: *mut crate::leanh::LeanObject,
    mut v_copy_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_copy_1873_);
    return v_copy_1873_;
}
pub unsafe fn l_Std_Http_Method_copy_elim___boxed(
    mut v_motive_1874_: *mut crate::leanh::LeanObject,
    mut v_t_1875_: *mut crate::leanh::LeanObject,
    mut v_h_1876_: *mut crate::leanh::LeanObject,
    mut v_copy_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1878_: u8 = 0;
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1878_ = (crate::leanh::lean_unbox(v_t_1875_) as u8);
    v_res_1879_ =
        l_Std_Http_Method_copy_elim(v_motive_1874_, v_t_boxed_1878_, v_h_1876_, v_copy_1877_);
    crate::leanh::lean_dec(v_copy_1877_);
    return v_res_1879_;
}
pub unsafe fn l_Std_Http_Method_delete_elim___redArg(
    mut v_delete_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_delete_1880_);
    return v_delete_1880_;
}
pub unsafe fn l_Std_Http_Method_delete_elim___redArg___boxed(
    mut v_delete_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1882_ = l_Std_Http_Method_delete_elim___redArg(v_delete_1881_);
    crate::leanh::lean_dec(v_delete_1881_);
    return v_res_1882_;
}
pub unsafe fn l_Std_Http_Method_delete_elim(
    mut v_motive_1883_: *mut crate::leanh::LeanObject,
    mut v_t_1884_: u8,
    mut v_h_1885_: *mut crate::leanh::LeanObject,
    mut v_delete_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_delete_1886_);
    return v_delete_1886_;
}
pub unsafe fn l_Std_Http_Method_delete_elim___boxed(
    mut v_motive_1887_: *mut crate::leanh::LeanObject,
    mut v_t_1888_: *mut crate::leanh::LeanObject,
    mut v_h_1889_: *mut crate::leanh::LeanObject,
    mut v_delete_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1891_: u8 = 0;
    let mut v_res_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1891_ = (crate::leanh::lean_unbox(v_t_1888_) as u8);
    v_res_1892_ =
        l_Std_Http_Method_delete_elim(v_motive_1887_, v_t_boxed_1891_, v_h_1889_, v_delete_1890_);
    crate::leanh::lean_dec(v_delete_1890_);
    return v_res_1892_;
}
pub unsafe fn l_Std_Http_Method_get_elim___redArg(
    mut v_get_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_get_1893_);
    return v_get_1893_;
}
pub unsafe fn l_Std_Http_Method_get_elim___redArg___boxed(
    mut v_get_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Std_Http_Method_get_elim___redArg(v_get_1894_);
    crate::leanh::lean_dec(v_get_1894_);
    return v_res_1895_;
}
pub unsafe fn l_Std_Http_Method_get_elim(
    mut v_motive_1896_: *mut crate::leanh::LeanObject,
    mut v_t_1897_: u8,
    mut v_h_1898_: *mut crate::leanh::LeanObject,
    mut v_get_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_get_1899_);
    return v_get_1899_;
}
pub unsafe fn l_Std_Http_Method_get_elim___boxed(
    mut v_motive_1900_: *mut crate::leanh::LeanObject,
    mut v_t_1901_: *mut crate::leanh::LeanObject,
    mut v_h_1902_: *mut crate::leanh::LeanObject,
    mut v_get_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1904_: u8 = 0;
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1904_ = (crate::leanh::lean_unbox(v_t_1901_) as u8);
    v_res_1905_ =
        l_Std_Http_Method_get_elim(v_motive_1900_, v_t_boxed_1904_, v_h_1902_, v_get_1903_);
    crate::leanh::lean_dec(v_get_1903_);
    return v_res_1905_;
}
pub unsafe fn l_Std_Http_Method_head_elim___redArg(
    mut v_head_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_head_1906_);
    return v_head_1906_;
}
pub unsafe fn l_Std_Http_Method_head_elim___redArg___boxed(
    mut v_head_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Std_Http_Method_head_elim___redArg(v_head_1907_);
    crate::leanh::lean_dec(v_head_1907_);
    return v_res_1908_;
}
pub unsafe fn l_Std_Http_Method_head_elim(
    mut v_motive_1909_: *mut crate::leanh::LeanObject,
    mut v_t_1910_: u8,
    mut v_h_1911_: *mut crate::leanh::LeanObject,
    mut v_head_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_head_1912_);
    return v_head_1912_;
}
pub unsafe fn l_Std_Http_Method_head_elim___boxed(
    mut v_motive_1913_: *mut crate::leanh::LeanObject,
    mut v_t_1914_: *mut crate::leanh::LeanObject,
    mut v_h_1915_: *mut crate::leanh::LeanObject,
    mut v_head_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1917_: u8 = 0;
    let mut v_res_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1917_ = (crate::leanh::lean_unbox(v_t_1914_) as u8);
    v_res_1918_ =
        l_Std_Http_Method_head_elim(v_motive_1913_, v_t_boxed_1917_, v_h_1915_, v_head_1916_);
    crate::leanh::lean_dec(v_head_1916_);
    return v_res_1918_;
}
pub unsafe fn l_Std_Http_Method_label_elim___redArg(
    mut v_label_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_label_1919_);
    return v_label_1919_;
}
pub unsafe fn l_Std_Http_Method_label_elim___redArg___boxed(
    mut v_label_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1921_ = l_Std_Http_Method_label_elim___redArg(v_label_1920_);
    crate::leanh::lean_dec(v_label_1920_);
    return v_res_1921_;
}
pub unsafe fn l_Std_Http_Method_label_elim(
    mut v_motive_1922_: *mut crate::leanh::LeanObject,
    mut v_t_1923_: u8,
    mut v_h_1924_: *mut crate::leanh::LeanObject,
    mut v_label_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_label_1925_);
    return v_label_1925_;
}
pub unsafe fn l_Std_Http_Method_label_elim___boxed(
    mut v_motive_1926_: *mut crate::leanh::LeanObject,
    mut v_t_1927_: *mut crate::leanh::LeanObject,
    mut v_h_1928_: *mut crate::leanh::LeanObject,
    mut v_label_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1930_: u8 = 0;
    let mut v_res_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1930_ = (crate::leanh::lean_unbox(v_t_1927_) as u8);
    v_res_1931_ =
        l_Std_Http_Method_label_elim(v_motive_1926_, v_t_boxed_1930_, v_h_1928_, v_label_1929_);
    crate::leanh::lean_dec(v_label_1929_);
    return v_res_1931_;
}
pub unsafe fn l_Std_Http_Method_link_elim___redArg(
    mut v_link_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_link_1932_);
    return v_link_1932_;
}
pub unsafe fn l_Std_Http_Method_link_elim___redArg___boxed(
    mut v_link_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Std_Http_Method_link_elim___redArg(v_link_1933_);
    crate::leanh::lean_dec(v_link_1933_);
    return v_res_1934_;
}
pub unsafe fn l_Std_Http_Method_link_elim(
    mut v_motive_1935_: *mut crate::leanh::LeanObject,
    mut v_t_1936_: u8,
    mut v_h_1937_: *mut crate::leanh::LeanObject,
    mut v_link_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_link_1938_);
    return v_link_1938_;
}
pub unsafe fn l_Std_Http_Method_link_elim___boxed(
    mut v_motive_1939_: *mut crate::leanh::LeanObject,
    mut v_t_1940_: *mut crate::leanh::LeanObject,
    mut v_h_1941_: *mut crate::leanh::LeanObject,
    mut v_link_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1943_ = (crate::leanh::lean_unbox(v_t_1940_) as u8);
    v_res_1944_ =
        l_Std_Http_Method_link_elim(v_motive_1939_, v_t_boxed_1943_, v_h_1941_, v_link_1942_);
    crate::leanh::lean_dec(v_link_1942_);
    return v_res_1944_;
}
pub unsafe fn l_Std_Http_Method_lock_elim___redArg(
    mut v_lock_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lock_1945_);
    return v_lock_1945_;
}
pub unsafe fn l_Std_Http_Method_lock_elim___redArg___boxed(
    mut v_lock_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Std_Http_Method_lock_elim___redArg(v_lock_1946_);
    crate::leanh::lean_dec(v_lock_1946_);
    return v_res_1947_;
}
pub unsafe fn l_Std_Http_Method_lock_elim(
    mut v_motive_1948_: *mut crate::leanh::LeanObject,
    mut v_t_1949_: u8,
    mut v_h_1950_: *mut crate::leanh::LeanObject,
    mut v_lock_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lock_1951_);
    return v_lock_1951_;
}
pub unsafe fn l_Std_Http_Method_lock_elim___boxed(
    mut v_motive_1952_: *mut crate::leanh::LeanObject,
    mut v_t_1953_: *mut crate::leanh::LeanObject,
    mut v_h_1954_: *mut crate::leanh::LeanObject,
    mut v_lock_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1956_: u8 = 0;
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1956_ = (crate::leanh::lean_unbox(v_t_1953_) as u8);
    v_res_1957_ =
        l_Std_Http_Method_lock_elim(v_motive_1952_, v_t_boxed_1956_, v_h_1954_, v_lock_1955_);
    crate::leanh::lean_dec(v_lock_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Std_Http_Method_merge_elim___redArg(
    mut v_merge_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_merge_1958_);
    return v_merge_1958_;
}
pub unsafe fn l_Std_Http_Method_merge_elim___redArg___boxed(
    mut v_merge_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Std_Http_Method_merge_elim___redArg(v_merge_1959_);
    crate::leanh::lean_dec(v_merge_1959_);
    return v_res_1960_;
}
pub unsafe fn l_Std_Http_Method_merge_elim(
    mut v_motive_1961_: *mut crate::leanh::LeanObject,
    mut v_t_1962_: u8,
    mut v_h_1963_: *mut crate::leanh::LeanObject,
    mut v_merge_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_merge_1964_);
    return v_merge_1964_;
}
pub unsafe fn l_Std_Http_Method_merge_elim___boxed(
    mut v_motive_1965_: *mut crate::leanh::LeanObject,
    mut v_t_1966_: *mut crate::leanh::LeanObject,
    mut v_h_1967_: *mut crate::leanh::LeanObject,
    mut v_merge_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1969_: u8 = 0;
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1969_ = (crate::leanh::lean_unbox(v_t_1966_) as u8);
    v_res_1970_ =
        l_Std_Http_Method_merge_elim(v_motive_1965_, v_t_boxed_1969_, v_h_1967_, v_merge_1968_);
    crate::leanh::lean_dec(v_merge_1968_);
    return v_res_1970_;
}
pub unsafe fn l_Std_Http_Method_mkactivity_elim___redArg(
    mut v_mkactivity_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkactivity_1971_);
    return v_mkactivity_1971_;
}
pub unsafe fn l_Std_Http_Method_mkactivity_elim___redArg___boxed(
    mut v_mkactivity_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Std_Http_Method_mkactivity_elim___redArg(v_mkactivity_1972_);
    crate::leanh::lean_dec(v_mkactivity_1972_);
    return v_res_1973_;
}
pub unsafe fn l_Std_Http_Method_mkactivity_elim(
    mut v_motive_1974_: *mut crate::leanh::LeanObject,
    mut v_t_1975_: u8,
    mut v_h_1976_: *mut crate::leanh::LeanObject,
    mut v_mkactivity_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkactivity_1977_);
    return v_mkactivity_1977_;
}
pub unsafe fn l_Std_Http_Method_mkactivity_elim___boxed(
    mut v_motive_1978_: *mut crate::leanh::LeanObject,
    mut v_t_1979_: *mut crate::leanh::LeanObject,
    mut v_h_1980_: *mut crate::leanh::LeanObject,
    mut v_mkactivity_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1982_: u8 = 0;
    let mut v_res_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1982_ = (crate::leanh::lean_unbox(v_t_1979_) as u8);
    v_res_1983_ = l_Std_Http_Method_mkactivity_elim(
        v_motive_1978_,
        v_t_boxed_1982_,
        v_h_1980_,
        v_mkactivity_1981_,
    );
    crate::leanh::lean_dec(v_mkactivity_1981_);
    return v_res_1983_;
}
pub unsafe fn l_Std_Http_Method_mkcalendar_elim___redArg(
    mut v_mkcalendar_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkcalendar_1984_);
    return v_mkcalendar_1984_;
}
pub unsafe fn l_Std_Http_Method_mkcalendar_elim___redArg___boxed(
    mut v_mkcalendar_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l_Std_Http_Method_mkcalendar_elim___redArg(v_mkcalendar_1985_);
    crate::leanh::lean_dec(v_mkcalendar_1985_);
    return v_res_1986_;
}
pub unsafe fn l_Std_Http_Method_mkcalendar_elim(
    mut v_motive_1987_: *mut crate::leanh::LeanObject,
    mut v_t_1988_: u8,
    mut v_h_1989_: *mut crate::leanh::LeanObject,
    mut v_mkcalendar_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkcalendar_1990_);
    return v_mkcalendar_1990_;
}
pub unsafe fn l_Std_Http_Method_mkcalendar_elim___boxed(
    mut v_motive_1991_: *mut crate::leanh::LeanObject,
    mut v_t_1992_: *mut crate::leanh::LeanObject,
    mut v_h_1993_: *mut crate::leanh::LeanObject,
    mut v_mkcalendar_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1995_: u8 = 0;
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1995_ = (crate::leanh::lean_unbox(v_t_1992_) as u8);
    v_res_1996_ = l_Std_Http_Method_mkcalendar_elim(
        v_motive_1991_,
        v_t_boxed_1995_,
        v_h_1993_,
        v_mkcalendar_1994_,
    );
    crate::leanh::lean_dec(v_mkcalendar_1994_);
    return v_res_1996_;
}
pub unsafe fn l_Std_Http_Method_mkcol_elim___redArg(
    mut v_mkcol_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkcol_1997_);
    return v_mkcol_1997_;
}
pub unsafe fn l_Std_Http_Method_mkcol_elim___redArg___boxed(
    mut v_mkcol_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1999_ = l_Std_Http_Method_mkcol_elim___redArg(v_mkcol_1998_);
    crate::leanh::lean_dec(v_mkcol_1998_);
    return v_res_1999_;
}
pub unsafe fn l_Std_Http_Method_mkcol_elim(
    mut v_motive_2000_: *mut crate::leanh::LeanObject,
    mut v_t_2001_: u8,
    mut v_h_2002_: *mut crate::leanh::LeanObject,
    mut v_mkcol_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkcol_2003_);
    return v_mkcol_2003_;
}
pub unsafe fn l_Std_Http_Method_mkcol_elim___boxed(
    mut v_motive_2004_: *mut crate::leanh::LeanObject,
    mut v_t_2005_: *mut crate::leanh::LeanObject,
    mut v_h_2006_: *mut crate::leanh::LeanObject,
    mut v_mkcol_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2008_: u8 = 0;
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2008_ = (crate::leanh::lean_unbox(v_t_2005_) as u8);
    v_res_2009_ =
        l_Std_Http_Method_mkcol_elim(v_motive_2004_, v_t_boxed_2008_, v_h_2006_, v_mkcol_2007_);
    crate::leanh::lean_dec(v_mkcol_2007_);
    return v_res_2009_;
}
pub unsafe fn l_Std_Http_Method_mkredirectref_elim___redArg(
    mut v_mkredirectref_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkredirectref_2010_);
    return v_mkredirectref_2010_;
}
pub unsafe fn l_Std_Http_Method_mkredirectref_elim___redArg___boxed(
    mut v_mkredirectref_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ = l_Std_Http_Method_mkredirectref_elim___redArg(v_mkredirectref_2011_);
    crate::leanh::lean_dec(v_mkredirectref_2011_);
    return v_res_2012_;
}
pub unsafe fn l_Std_Http_Method_mkredirectref_elim(
    mut v_motive_2013_: *mut crate::leanh::LeanObject,
    mut v_t_2014_: u8,
    mut v_h_2015_: *mut crate::leanh::LeanObject,
    mut v_mkredirectref_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkredirectref_2016_);
    return v_mkredirectref_2016_;
}
pub unsafe fn l_Std_Http_Method_mkredirectref_elim___boxed(
    mut v_motive_2017_: *mut crate::leanh::LeanObject,
    mut v_t_2018_: *mut crate::leanh::LeanObject,
    mut v_h_2019_: *mut crate::leanh::LeanObject,
    mut v_mkredirectref_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2021_: u8 = 0;
    let mut v_res_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2021_ = (crate::leanh::lean_unbox(v_t_2018_) as u8);
    v_res_2022_ = l_Std_Http_Method_mkredirectref_elim(
        v_motive_2017_,
        v_t_boxed_2021_,
        v_h_2019_,
        v_mkredirectref_2020_,
    );
    crate::leanh::lean_dec(v_mkredirectref_2020_);
    return v_res_2022_;
}
pub unsafe fn l_Std_Http_Method_mkworkspace_elim___redArg(
    mut v_mkworkspace_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkworkspace_2023_);
    return v_mkworkspace_2023_;
}
pub unsafe fn l_Std_Http_Method_mkworkspace_elim___redArg___boxed(
    mut v_mkworkspace_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Std_Http_Method_mkworkspace_elim___redArg(v_mkworkspace_2024_);
    crate::leanh::lean_dec(v_mkworkspace_2024_);
    return v_res_2025_;
}
pub unsafe fn l_Std_Http_Method_mkworkspace_elim(
    mut v_motive_2026_: *mut crate::leanh::LeanObject,
    mut v_t_2027_: u8,
    mut v_h_2028_: *mut crate::leanh::LeanObject,
    mut v_mkworkspace_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mkworkspace_2029_);
    return v_mkworkspace_2029_;
}
pub unsafe fn l_Std_Http_Method_mkworkspace_elim___boxed(
    mut v_motive_2030_: *mut crate::leanh::LeanObject,
    mut v_t_2031_: *mut crate::leanh::LeanObject,
    mut v_h_2032_: *mut crate::leanh::LeanObject,
    mut v_mkworkspace_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2034_: u8 = 0;
    let mut v_res_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2034_ = (crate::leanh::lean_unbox(v_t_2031_) as u8);
    v_res_2035_ = l_Std_Http_Method_mkworkspace_elim(
        v_motive_2030_,
        v_t_boxed_2034_,
        v_h_2032_,
        v_mkworkspace_2033_,
    );
    crate::leanh::lean_dec(v_mkworkspace_2033_);
    return v_res_2035_;
}
pub unsafe fn l_Std_Http_Method_move_elim___redArg(
    mut v_move_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_move_2036_);
    return v_move_2036_;
}
pub unsafe fn l_Std_Http_Method_move_elim___redArg___boxed(
    mut v_move_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Std_Http_Method_move_elim___redArg(v_move_2037_);
    crate::leanh::lean_dec(v_move_2037_);
    return v_res_2038_;
}
pub unsafe fn l_Std_Http_Method_move_elim(
    mut v_motive_2039_: *mut crate::leanh::LeanObject,
    mut v_t_2040_: u8,
    mut v_h_2041_: *mut crate::leanh::LeanObject,
    mut v_move_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_move_2042_);
    return v_move_2042_;
}
pub unsafe fn l_Std_Http_Method_move_elim___boxed(
    mut v_motive_2043_: *mut crate::leanh::LeanObject,
    mut v_t_2044_: *mut crate::leanh::LeanObject,
    mut v_h_2045_: *mut crate::leanh::LeanObject,
    mut v_move_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2047_: u8 = 0;
    let mut v_res_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2047_ = (crate::leanh::lean_unbox(v_t_2044_) as u8);
    v_res_2048_ =
        l_Std_Http_Method_move_elim(v_motive_2043_, v_t_boxed_2047_, v_h_2045_, v_move_2046_);
    crate::leanh::lean_dec(v_move_2046_);
    return v_res_2048_;
}
pub unsafe fn l_Std_Http_Method_options_elim___redArg(
    mut v_options_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_options_2049_);
    return v_options_2049_;
}
pub unsafe fn l_Std_Http_Method_options_elim___redArg___boxed(
    mut v_options_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Std_Http_Method_options_elim___redArg(v_options_2050_);
    crate::leanh::lean_dec(v_options_2050_);
    return v_res_2051_;
}
pub unsafe fn l_Std_Http_Method_options_elim(
    mut v_motive_2052_: *mut crate::leanh::LeanObject,
    mut v_t_2053_: u8,
    mut v_h_2054_: *mut crate::leanh::LeanObject,
    mut v_options_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_options_2055_);
    return v_options_2055_;
}
pub unsafe fn l_Std_Http_Method_options_elim___boxed(
    mut v_motive_2056_: *mut crate::leanh::LeanObject,
    mut v_t_2057_: *mut crate::leanh::LeanObject,
    mut v_h_2058_: *mut crate::leanh::LeanObject,
    mut v_options_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2060_: u8 = 0;
    let mut v_res_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2060_ = (crate::leanh::lean_unbox(v_t_2057_) as u8);
    v_res_2061_ =
        l_Std_Http_Method_options_elim(v_motive_2056_, v_t_boxed_2060_, v_h_2058_, v_options_2059_);
    crate::leanh::lean_dec(v_options_2059_);
    return v_res_2061_;
}
pub unsafe fn l_Std_Http_Method_orderpatch_elim___redArg(
    mut v_orderpatch_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_orderpatch_2062_);
    return v_orderpatch_2062_;
}
pub unsafe fn l_Std_Http_Method_orderpatch_elim___redArg___boxed(
    mut v_orderpatch_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Std_Http_Method_orderpatch_elim___redArg(v_orderpatch_2063_);
    crate::leanh::lean_dec(v_orderpatch_2063_);
    return v_res_2064_;
}
pub unsafe fn l_Std_Http_Method_orderpatch_elim(
    mut v_motive_2065_: *mut crate::leanh::LeanObject,
    mut v_t_2066_: u8,
    mut v_h_2067_: *mut crate::leanh::LeanObject,
    mut v_orderpatch_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_orderpatch_2068_);
    return v_orderpatch_2068_;
}
pub unsafe fn l_Std_Http_Method_orderpatch_elim___boxed(
    mut v_motive_2069_: *mut crate::leanh::LeanObject,
    mut v_t_2070_: *mut crate::leanh::LeanObject,
    mut v_h_2071_: *mut crate::leanh::LeanObject,
    mut v_orderpatch_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2073_: u8 = 0;
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2073_ = (crate::leanh::lean_unbox(v_t_2070_) as u8);
    v_res_2074_ = l_Std_Http_Method_orderpatch_elim(
        v_motive_2069_,
        v_t_boxed_2073_,
        v_h_2071_,
        v_orderpatch_2072_,
    );
    crate::leanh::lean_dec(v_orderpatch_2072_);
    return v_res_2074_;
}
pub unsafe fn l_Std_Http_Method_patch_elim___redArg(
    mut v_patch_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_patch_2075_);
    return v_patch_2075_;
}
pub unsafe fn l_Std_Http_Method_patch_elim___redArg___boxed(
    mut v_patch_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2077_ = l_Std_Http_Method_patch_elim___redArg(v_patch_2076_);
    crate::leanh::lean_dec(v_patch_2076_);
    return v_res_2077_;
}
pub unsafe fn l_Std_Http_Method_patch_elim(
    mut v_motive_2078_: *mut crate::leanh::LeanObject,
    mut v_t_2079_: u8,
    mut v_h_2080_: *mut crate::leanh::LeanObject,
    mut v_patch_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_patch_2081_);
    return v_patch_2081_;
}
pub unsafe fn l_Std_Http_Method_patch_elim___boxed(
    mut v_motive_2082_: *mut crate::leanh::LeanObject,
    mut v_t_2083_: *mut crate::leanh::LeanObject,
    mut v_h_2084_: *mut crate::leanh::LeanObject,
    mut v_patch_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2086_: u8 = 0;
    let mut v_res_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2086_ = (crate::leanh::lean_unbox(v_t_2083_) as u8);
    v_res_2087_ =
        l_Std_Http_Method_patch_elim(v_motive_2082_, v_t_boxed_2086_, v_h_2084_, v_patch_2085_);
    crate::leanh::lean_dec(v_patch_2085_);
    return v_res_2087_;
}
pub unsafe fn l_Std_Http_Method_post_elim___redArg(
    mut v_post_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_post_2088_);
    return v_post_2088_;
}
pub unsafe fn l_Std_Http_Method_post_elim___redArg___boxed(
    mut v_post_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Std_Http_Method_post_elim___redArg(v_post_2089_);
    crate::leanh::lean_dec(v_post_2089_);
    return v_res_2090_;
}
pub unsafe fn l_Std_Http_Method_post_elim(
    mut v_motive_2091_: *mut crate::leanh::LeanObject,
    mut v_t_2092_: u8,
    mut v_h_2093_: *mut crate::leanh::LeanObject,
    mut v_post_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_post_2094_);
    return v_post_2094_;
}
pub unsafe fn l_Std_Http_Method_post_elim___boxed(
    mut v_motive_2095_: *mut crate::leanh::LeanObject,
    mut v_t_2096_: *mut crate::leanh::LeanObject,
    mut v_h_2097_: *mut crate::leanh::LeanObject,
    mut v_post_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2099_: u8 = 0;
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2099_ = (crate::leanh::lean_unbox(v_t_2096_) as u8);
    v_res_2100_ =
        l_Std_Http_Method_post_elim(v_motive_2095_, v_t_boxed_2099_, v_h_2097_, v_post_2098_);
    crate::leanh::lean_dec(v_post_2098_);
    return v_res_2100_;
}
pub unsafe fn l_Std_Http_Method_pri_elim___redArg(
    mut v_pri_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pri_2101_);
    return v_pri_2101_;
}
pub unsafe fn l_Std_Http_Method_pri_elim___redArg___boxed(
    mut v_pri_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2103_ = l_Std_Http_Method_pri_elim___redArg(v_pri_2102_);
    crate::leanh::lean_dec(v_pri_2102_);
    return v_res_2103_;
}
pub unsafe fn l_Std_Http_Method_pri_elim(
    mut v_motive_2104_: *mut crate::leanh::LeanObject,
    mut v_t_2105_: u8,
    mut v_h_2106_: *mut crate::leanh::LeanObject,
    mut v_pri_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pri_2107_);
    return v_pri_2107_;
}
pub unsafe fn l_Std_Http_Method_pri_elim___boxed(
    mut v_motive_2108_: *mut crate::leanh::LeanObject,
    mut v_t_2109_: *mut crate::leanh::LeanObject,
    mut v_h_2110_: *mut crate::leanh::LeanObject,
    mut v_pri_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2112_: u8 = 0;
    let mut v_res_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2112_ = (crate::leanh::lean_unbox(v_t_2109_) as u8);
    v_res_2113_ =
        l_Std_Http_Method_pri_elim(v_motive_2108_, v_t_boxed_2112_, v_h_2110_, v_pri_2111_);
    crate::leanh::lean_dec(v_pri_2111_);
    return v_res_2113_;
}
pub unsafe fn l_Std_Http_Method_propfind_elim___redArg(
    mut v_propfind_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_propfind_2114_);
    return v_propfind_2114_;
}
pub unsafe fn l_Std_Http_Method_propfind_elim___redArg___boxed(
    mut v_propfind_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Std_Http_Method_propfind_elim___redArg(v_propfind_2115_);
    crate::leanh::lean_dec(v_propfind_2115_);
    return v_res_2116_;
}
pub unsafe fn l_Std_Http_Method_propfind_elim(
    mut v_motive_2117_: *mut crate::leanh::LeanObject,
    mut v_t_2118_: u8,
    mut v_h_2119_: *mut crate::leanh::LeanObject,
    mut v_propfind_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_propfind_2120_);
    return v_propfind_2120_;
}
pub unsafe fn l_Std_Http_Method_propfind_elim___boxed(
    mut v_motive_2121_: *mut crate::leanh::LeanObject,
    mut v_t_2122_: *mut crate::leanh::LeanObject,
    mut v_h_2123_: *mut crate::leanh::LeanObject,
    mut v_propfind_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2125_: u8 = 0;
    let mut v_res_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2125_ = (crate::leanh::lean_unbox(v_t_2122_) as u8);
    v_res_2126_ = l_Std_Http_Method_propfind_elim(
        v_motive_2121_,
        v_t_boxed_2125_,
        v_h_2123_,
        v_propfind_2124_,
    );
    crate::leanh::lean_dec(v_propfind_2124_);
    return v_res_2126_;
}
pub unsafe fn l_Std_Http_Method_proppatch_elim___redArg(
    mut v_proppatch_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_proppatch_2127_);
    return v_proppatch_2127_;
}
pub unsafe fn l_Std_Http_Method_proppatch_elim___redArg___boxed(
    mut v_proppatch_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Std_Http_Method_proppatch_elim___redArg(v_proppatch_2128_);
    crate::leanh::lean_dec(v_proppatch_2128_);
    return v_res_2129_;
}
pub unsafe fn l_Std_Http_Method_proppatch_elim(
    mut v_motive_2130_: *mut crate::leanh::LeanObject,
    mut v_t_2131_: u8,
    mut v_h_2132_: *mut crate::leanh::LeanObject,
    mut v_proppatch_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_proppatch_2133_);
    return v_proppatch_2133_;
}
pub unsafe fn l_Std_Http_Method_proppatch_elim___boxed(
    mut v_motive_2134_: *mut crate::leanh::LeanObject,
    mut v_t_2135_: *mut crate::leanh::LeanObject,
    mut v_h_2136_: *mut crate::leanh::LeanObject,
    mut v_proppatch_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2138_: u8 = 0;
    let mut v_res_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2138_ = (crate::leanh::lean_unbox(v_t_2135_) as u8);
    v_res_2139_ = l_Std_Http_Method_proppatch_elim(
        v_motive_2134_,
        v_t_boxed_2138_,
        v_h_2136_,
        v_proppatch_2137_,
    );
    crate::leanh::lean_dec(v_proppatch_2137_);
    return v_res_2139_;
}
pub unsafe fn l_Std_Http_Method_put_elim___redArg(
    mut v_put_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_put_2140_);
    return v_put_2140_;
}
pub unsafe fn l_Std_Http_Method_put_elim___redArg___boxed(
    mut v_put_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2142_ = l_Std_Http_Method_put_elim___redArg(v_put_2141_);
    crate::leanh::lean_dec(v_put_2141_);
    return v_res_2142_;
}
pub unsafe fn l_Std_Http_Method_put_elim(
    mut v_motive_2143_: *mut crate::leanh::LeanObject,
    mut v_t_2144_: u8,
    mut v_h_2145_: *mut crate::leanh::LeanObject,
    mut v_put_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_put_2146_);
    return v_put_2146_;
}
pub unsafe fn l_Std_Http_Method_put_elim___boxed(
    mut v_motive_2147_: *mut crate::leanh::LeanObject,
    mut v_t_2148_: *mut crate::leanh::LeanObject,
    mut v_h_2149_: *mut crate::leanh::LeanObject,
    mut v_put_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2151_: u8 = 0;
    let mut v_res_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2151_ = (crate::leanh::lean_unbox(v_t_2148_) as u8);
    v_res_2152_ =
        l_Std_Http_Method_put_elim(v_motive_2147_, v_t_boxed_2151_, v_h_2149_, v_put_2150_);
    crate::leanh::lean_dec(v_put_2150_);
    return v_res_2152_;
}
pub unsafe fn l_Std_Http_Method_query_elim___redArg(
    mut v_query_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_query_2153_);
    return v_query_2153_;
}
pub unsafe fn l_Std_Http_Method_query_elim___redArg___boxed(
    mut v_query_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Std_Http_Method_query_elim___redArg(v_query_2154_);
    crate::leanh::lean_dec(v_query_2154_);
    return v_res_2155_;
}
pub unsafe fn l_Std_Http_Method_query_elim(
    mut v_motive_2156_: *mut crate::leanh::LeanObject,
    mut v_t_2157_: u8,
    mut v_h_2158_: *mut crate::leanh::LeanObject,
    mut v_query_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_query_2159_);
    return v_query_2159_;
}
pub unsafe fn l_Std_Http_Method_query_elim___boxed(
    mut v_motive_2160_: *mut crate::leanh::LeanObject,
    mut v_t_2161_: *mut crate::leanh::LeanObject,
    mut v_h_2162_: *mut crate::leanh::LeanObject,
    mut v_query_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2164_: u8 = 0;
    let mut v_res_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2164_ = (crate::leanh::lean_unbox(v_t_2161_) as u8);
    v_res_2165_ =
        l_Std_Http_Method_query_elim(v_motive_2160_, v_t_boxed_2164_, v_h_2162_, v_query_2163_);
    crate::leanh::lean_dec(v_query_2163_);
    return v_res_2165_;
}
pub unsafe fn l_Std_Http_Method_rebind_elim___redArg(
    mut v_rebind_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_rebind_2166_);
    return v_rebind_2166_;
}
pub unsafe fn l_Std_Http_Method_rebind_elim___redArg___boxed(
    mut v_rebind_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Std_Http_Method_rebind_elim___redArg(v_rebind_2167_);
    crate::leanh::lean_dec(v_rebind_2167_);
    return v_res_2168_;
}
pub unsafe fn l_Std_Http_Method_rebind_elim(
    mut v_motive_2169_: *mut crate::leanh::LeanObject,
    mut v_t_2170_: u8,
    mut v_h_2171_: *mut crate::leanh::LeanObject,
    mut v_rebind_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_rebind_2172_);
    return v_rebind_2172_;
}
pub unsafe fn l_Std_Http_Method_rebind_elim___boxed(
    mut v_motive_2173_: *mut crate::leanh::LeanObject,
    mut v_t_2174_: *mut crate::leanh::LeanObject,
    mut v_h_2175_: *mut crate::leanh::LeanObject,
    mut v_rebind_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2177_: u8 = 0;
    let mut v_res_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2177_ = (crate::leanh::lean_unbox(v_t_2174_) as u8);
    v_res_2178_ =
        l_Std_Http_Method_rebind_elim(v_motive_2173_, v_t_boxed_2177_, v_h_2175_, v_rebind_2176_);
    crate::leanh::lean_dec(v_rebind_2176_);
    return v_res_2178_;
}
pub unsafe fn l_Std_Http_Method_report_elim___redArg(
    mut v_report_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_report_2179_);
    return v_report_2179_;
}
pub unsafe fn l_Std_Http_Method_report_elim___redArg___boxed(
    mut v_report_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2181_ = l_Std_Http_Method_report_elim___redArg(v_report_2180_);
    crate::leanh::lean_dec(v_report_2180_);
    return v_res_2181_;
}
pub unsafe fn l_Std_Http_Method_report_elim(
    mut v_motive_2182_: *mut crate::leanh::LeanObject,
    mut v_t_2183_: u8,
    mut v_h_2184_: *mut crate::leanh::LeanObject,
    mut v_report_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_report_2185_);
    return v_report_2185_;
}
pub unsafe fn l_Std_Http_Method_report_elim___boxed(
    mut v_motive_2186_: *mut crate::leanh::LeanObject,
    mut v_t_2187_: *mut crate::leanh::LeanObject,
    mut v_h_2188_: *mut crate::leanh::LeanObject,
    mut v_report_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2190_: u8 = 0;
    let mut v_res_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2190_ = (crate::leanh::lean_unbox(v_t_2187_) as u8);
    v_res_2191_ =
        l_Std_Http_Method_report_elim(v_motive_2186_, v_t_boxed_2190_, v_h_2188_, v_report_2189_);
    crate::leanh::lean_dec(v_report_2189_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Http_Method_search_elim___redArg(
    mut v_search_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_search_2192_);
    return v_search_2192_;
}
pub unsafe fn l_Std_Http_Method_search_elim___redArg___boxed(
    mut v_search_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_Std_Http_Method_search_elim___redArg(v_search_2193_);
    crate::leanh::lean_dec(v_search_2193_);
    return v_res_2194_;
}
pub unsafe fn l_Std_Http_Method_search_elim(
    mut v_motive_2195_: *mut crate::leanh::LeanObject,
    mut v_t_2196_: u8,
    mut v_h_2197_: *mut crate::leanh::LeanObject,
    mut v_search_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_search_2198_);
    return v_search_2198_;
}
pub unsafe fn l_Std_Http_Method_search_elim___boxed(
    mut v_motive_2199_: *mut crate::leanh::LeanObject,
    mut v_t_2200_: *mut crate::leanh::LeanObject,
    mut v_h_2201_: *mut crate::leanh::LeanObject,
    mut v_search_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2203_: u8 = 0;
    let mut v_res_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2203_ = (crate::leanh::lean_unbox(v_t_2200_) as u8);
    v_res_2204_ =
        l_Std_Http_Method_search_elim(v_motive_2199_, v_t_boxed_2203_, v_h_2201_, v_search_2202_);
    crate::leanh::lean_dec(v_search_2202_);
    return v_res_2204_;
}
pub unsafe fn l_Std_Http_Method_trace_elim___redArg(
    mut v_trace_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_trace_2205_);
    return v_trace_2205_;
}
pub unsafe fn l_Std_Http_Method_trace_elim___redArg___boxed(
    mut v_trace_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2207_ = l_Std_Http_Method_trace_elim___redArg(v_trace_2206_);
    crate::leanh::lean_dec(v_trace_2206_);
    return v_res_2207_;
}
pub unsafe fn l_Std_Http_Method_trace_elim(
    mut v_motive_2208_: *mut crate::leanh::LeanObject,
    mut v_t_2209_: u8,
    mut v_h_2210_: *mut crate::leanh::LeanObject,
    mut v_trace_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_trace_2211_);
    return v_trace_2211_;
}
pub unsafe fn l_Std_Http_Method_trace_elim___boxed(
    mut v_motive_2212_: *mut crate::leanh::LeanObject,
    mut v_t_2213_: *mut crate::leanh::LeanObject,
    mut v_h_2214_: *mut crate::leanh::LeanObject,
    mut v_trace_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2216_: u8 = 0;
    let mut v_res_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2216_ = (crate::leanh::lean_unbox(v_t_2213_) as u8);
    v_res_2217_ =
        l_Std_Http_Method_trace_elim(v_motive_2212_, v_t_boxed_2216_, v_h_2214_, v_trace_2215_);
    crate::leanh::lean_dec(v_trace_2215_);
    return v_res_2217_;
}
pub unsafe fn l_Std_Http_Method_unbind_elim___redArg(
    mut v_unbind_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unbind_2218_);
    return v_unbind_2218_;
}
pub unsafe fn l_Std_Http_Method_unbind_elim___redArg___boxed(
    mut v_unbind_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Std_Http_Method_unbind_elim___redArg(v_unbind_2219_);
    crate::leanh::lean_dec(v_unbind_2219_);
    return v_res_2220_;
}
pub unsafe fn l_Std_Http_Method_unbind_elim(
    mut v_motive_2221_: *mut crate::leanh::LeanObject,
    mut v_t_2222_: u8,
    mut v_h_2223_: *mut crate::leanh::LeanObject,
    mut v_unbind_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unbind_2224_);
    return v_unbind_2224_;
}
pub unsafe fn l_Std_Http_Method_unbind_elim___boxed(
    mut v_motive_2225_: *mut crate::leanh::LeanObject,
    mut v_t_2226_: *mut crate::leanh::LeanObject,
    mut v_h_2227_: *mut crate::leanh::LeanObject,
    mut v_unbind_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2229_: u8 = 0;
    let mut v_res_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2229_ = (crate::leanh::lean_unbox(v_t_2226_) as u8);
    v_res_2230_ =
        l_Std_Http_Method_unbind_elim(v_motive_2225_, v_t_boxed_2229_, v_h_2227_, v_unbind_2228_);
    crate::leanh::lean_dec(v_unbind_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Std_Http_Method_uncheckout_elim___redArg(
    mut v_uncheckout_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_uncheckout_2231_);
    return v_uncheckout_2231_;
}
pub unsafe fn l_Std_Http_Method_uncheckout_elim___redArg___boxed(
    mut v_uncheckout_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_Std_Http_Method_uncheckout_elim___redArg(v_uncheckout_2232_);
    crate::leanh::lean_dec(v_uncheckout_2232_);
    return v_res_2233_;
}
pub unsafe fn l_Std_Http_Method_uncheckout_elim(
    mut v_motive_2234_: *mut crate::leanh::LeanObject,
    mut v_t_2235_: u8,
    mut v_h_2236_: *mut crate::leanh::LeanObject,
    mut v_uncheckout_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_uncheckout_2237_);
    return v_uncheckout_2237_;
}
pub unsafe fn l_Std_Http_Method_uncheckout_elim___boxed(
    mut v_motive_2238_: *mut crate::leanh::LeanObject,
    mut v_t_2239_: *mut crate::leanh::LeanObject,
    mut v_h_2240_: *mut crate::leanh::LeanObject,
    mut v_uncheckout_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2242_: u8 = 0;
    let mut v_res_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2242_ = (crate::leanh::lean_unbox(v_t_2239_) as u8);
    v_res_2243_ = l_Std_Http_Method_uncheckout_elim(
        v_motive_2238_,
        v_t_boxed_2242_,
        v_h_2240_,
        v_uncheckout_2241_,
    );
    crate::leanh::lean_dec(v_uncheckout_2241_);
    return v_res_2243_;
}
pub unsafe fn l_Std_Http_Method_unlink_elim___redArg(
    mut v_unlink_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unlink_2244_);
    return v_unlink_2244_;
}
pub unsafe fn l_Std_Http_Method_unlink_elim___redArg___boxed(
    mut v_unlink_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Std_Http_Method_unlink_elim___redArg(v_unlink_2245_);
    crate::leanh::lean_dec(v_unlink_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Std_Http_Method_unlink_elim(
    mut v_motive_2247_: *mut crate::leanh::LeanObject,
    mut v_t_2248_: u8,
    mut v_h_2249_: *mut crate::leanh::LeanObject,
    mut v_unlink_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unlink_2250_);
    return v_unlink_2250_;
}
pub unsafe fn l_Std_Http_Method_unlink_elim___boxed(
    mut v_motive_2251_: *mut crate::leanh::LeanObject,
    mut v_t_2252_: *mut crate::leanh::LeanObject,
    mut v_h_2253_: *mut crate::leanh::LeanObject,
    mut v_unlink_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2255_: u8 = 0;
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2255_ = (crate::leanh::lean_unbox(v_t_2252_) as u8);
    v_res_2256_ =
        l_Std_Http_Method_unlink_elim(v_motive_2251_, v_t_boxed_2255_, v_h_2253_, v_unlink_2254_);
    crate::leanh::lean_dec(v_unlink_2254_);
    return v_res_2256_;
}
pub unsafe fn l_Std_Http_Method_unlock_elim___redArg(
    mut v_unlock_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unlock_2257_);
    return v_unlock_2257_;
}
pub unsafe fn l_Std_Http_Method_unlock_elim___redArg___boxed(
    mut v_unlock_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2259_ = l_Std_Http_Method_unlock_elim___redArg(v_unlock_2258_);
    crate::leanh::lean_dec(v_unlock_2258_);
    return v_res_2259_;
}
pub unsafe fn l_Std_Http_Method_unlock_elim(
    mut v_motive_2260_: *mut crate::leanh::LeanObject,
    mut v_t_2261_: u8,
    mut v_h_2262_: *mut crate::leanh::LeanObject,
    mut v_unlock_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unlock_2263_);
    return v_unlock_2263_;
}
pub unsafe fn l_Std_Http_Method_unlock_elim___boxed(
    mut v_motive_2264_: *mut crate::leanh::LeanObject,
    mut v_t_2265_: *mut crate::leanh::LeanObject,
    mut v_h_2266_: *mut crate::leanh::LeanObject,
    mut v_unlock_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2268_: u8 = 0;
    let mut v_res_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2268_ = (crate::leanh::lean_unbox(v_t_2265_) as u8);
    v_res_2269_ =
        l_Std_Http_Method_unlock_elim(v_motive_2264_, v_t_boxed_2268_, v_h_2266_, v_unlock_2267_);
    crate::leanh::lean_dec(v_unlock_2267_);
    return v_res_2269_;
}
pub unsafe fn l_Std_Http_Method_update_elim___redArg(
    mut v_update_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_update_2270_);
    return v_update_2270_;
}
pub unsafe fn l_Std_Http_Method_update_elim___redArg___boxed(
    mut v_update_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Http_Method_update_elim___redArg(v_update_2271_);
    crate::leanh::lean_dec(v_update_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Http_Method_update_elim(
    mut v_motive_2273_: *mut crate::leanh::LeanObject,
    mut v_t_2274_: u8,
    mut v_h_2275_: *mut crate::leanh::LeanObject,
    mut v_update_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_update_2276_);
    return v_update_2276_;
}
pub unsafe fn l_Std_Http_Method_update_elim___boxed(
    mut v_motive_2277_: *mut crate::leanh::LeanObject,
    mut v_t_2278_: *mut crate::leanh::LeanObject,
    mut v_h_2279_: *mut crate::leanh::LeanObject,
    mut v_update_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2281_: u8 = 0;
    let mut v_res_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2281_ = (crate::leanh::lean_unbox(v_t_2278_) as u8);
    v_res_2282_ =
        l_Std_Http_Method_update_elim(v_motive_2277_, v_t_boxed_2281_, v_h_2279_, v_update_2280_);
    crate::leanh::lean_dec(v_update_2280_);
    return v_res_2282_;
}
pub unsafe fn l_Std_Http_Method_updateredirectref_elim___redArg(
    mut v_updateredirectref_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_updateredirectref_2283_);
    return v_updateredirectref_2283_;
}
pub unsafe fn l_Std_Http_Method_updateredirectref_elim___redArg___boxed(
    mut v_updateredirectref_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Std_Http_Method_updateredirectref_elim___redArg(v_updateredirectref_2284_);
    crate::leanh::lean_dec(v_updateredirectref_2284_);
    return v_res_2285_;
}
pub unsafe fn l_Std_Http_Method_updateredirectref_elim(
    mut v_motive_2286_: *mut crate::leanh::LeanObject,
    mut v_t_2287_: u8,
    mut v_h_2288_: *mut crate::leanh::LeanObject,
    mut v_updateredirectref_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_updateredirectref_2289_);
    return v_updateredirectref_2289_;
}
pub unsafe fn l_Std_Http_Method_updateredirectref_elim___boxed(
    mut v_motive_2290_: *mut crate::leanh::LeanObject,
    mut v_t_2291_: *mut crate::leanh::LeanObject,
    mut v_h_2292_: *mut crate::leanh::LeanObject,
    mut v_updateredirectref_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2294_: u8 = 0;
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2294_ = (crate::leanh::lean_unbox(v_t_2291_) as u8);
    v_res_2295_ = l_Std_Http_Method_updateredirectref_elim(
        v_motive_2290_,
        v_t_boxed_2294_,
        v_h_2292_,
        v_updateredirectref_2293_,
    );
    crate::leanh::lean_dec(v_updateredirectref_2293_);
    return v_res_2295_;
}
pub unsafe fn l_Std_Http_Method_versionControl_elim___redArg(
    mut v_versionControl_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_versionControl_2296_);
    return v_versionControl_2296_;
}
pub unsafe fn l_Std_Http_Method_versionControl_elim___redArg___boxed(
    mut v_versionControl_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Std_Http_Method_versionControl_elim___redArg(v_versionControl_2297_);
    crate::leanh::lean_dec(v_versionControl_2297_);
    return v_res_2298_;
}
pub unsafe fn l_Std_Http_Method_versionControl_elim(
    mut v_motive_2299_: *mut crate::leanh::LeanObject,
    mut v_t_2300_: u8,
    mut v_h_2301_: *mut crate::leanh::LeanObject,
    mut v_versionControl_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_versionControl_2302_);
    return v_versionControl_2302_;
}
pub unsafe fn l_Std_Http_Method_versionControl_elim___boxed(
    mut v_motive_2303_: *mut crate::leanh::LeanObject,
    mut v_t_2304_: *mut crate::leanh::LeanObject,
    mut v_h_2305_: *mut crate::leanh::LeanObject,
    mut v_versionControl_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2307_: u8 = 0;
    let mut v_res_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2307_ = (crate::leanh::lean_unbox(v_t_2304_) as u8);
    v_res_2308_ = l_Std_Http_Method_versionControl_elim(
        v_motive_2303_,
        v_t_boxed_2307_,
        v_h_2305_,
        v_versionControl_2306_,
    );
    crate::leanh::lean_dec(v_versionControl_2306_);
    return v_res_2308_;
}
pub unsafe fn _init_l_Std_Http_instReprMethod_repr___closed__80() -> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2430_ = lean_nat_to_int(v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Std_Http_instReprMethod_repr___closed__81() -> *mut crate::leanh::LeanObject {
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2432_ = lean_nat_to_int(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Std_Http_instReprMethod_repr(
    mut v_x_2433_: u8,
    mut v_prec_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: u8 = 0;
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: u8 = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u8 = 0;
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u8 = 0;
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: u8 = 0;
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: u8 = 0;
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: u8 = 0;
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: u8 = 0;
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: u8 = 0;
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2433_ {
                0 => {
                    v___x_2715_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2716_ = lean_nat_dec_le(v___x_2715_, v_prec_2434_);
                    if v___x_2716_ == 0 {
                        v___x_2717_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2436_ = v___x_2717_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2718_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2436_ = v___x_2718_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2719_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2720_ = lean_nat_dec_le(v___x_2719_, v_prec_2434_);
                    if v___x_2720_ == 0 {
                        v___x_2721_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2443_ = v___x_2721_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2722_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2443_ = v___x_2722_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_2723_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2724_ = lean_nat_dec_le(v___x_2723_, v_prec_2434_);
                    if v___x_2724_ == 0 {
                        v___x_2725_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2450_ = v___x_2725_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2726_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2450_ = v___x_2726_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_2727_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2728_ = lean_nat_dec_le(v___x_2727_, v_prec_2434_);
                    if v___x_2728_ == 0 {
                        v___x_2729_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2457_ = v___x_2729_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2730_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2457_ = v___x_2730_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2732_ = lean_nat_dec_le(v___x_2731_, v_prec_2434_);
                    if v___x_2732_ == 0 {
                        v___x_2733_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2464_ = v___x_2733_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2734_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2464_ = v___x_2734_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v___x_2735_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2736_ = lean_nat_dec_le(v___x_2735_, v_prec_2434_);
                    if v___x_2736_ == 0 {
                        v___x_2737_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2471_ = v___x_2737_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2738_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2471_ = v___x_2738_;
                        state = 6;
                        continue;
                    }
                }
                6 => {
                    v___x_2739_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2740_ = lean_nat_dec_le(v___x_2739_, v_prec_2434_);
                    if v___x_2740_ == 0 {
                        v___x_2741_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2478_ = v___x_2741_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2742_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2478_ = v___x_2742_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v___x_2743_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2744_ = lean_nat_dec_le(v___x_2743_, v_prec_2434_);
                    if v___x_2744_ == 0 {
                        v___x_2745_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2485_ = v___x_2745_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2746_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2485_ = v___x_2746_;
                        state = 8;
                        continue;
                    }
                }
                8 => {
                    v___x_2747_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2748_ = lean_nat_dec_le(v___x_2747_, v_prec_2434_);
                    if v___x_2748_ == 0 {
                        v___x_2749_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2492_ = v___x_2749_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2750_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2492_ = v___x_2750_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v___x_2751_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2752_ = lean_nat_dec_le(v___x_2751_, v_prec_2434_);
                    if v___x_2752_ == 0 {
                        v___x_2753_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2499_ = v___x_2753_;
                        state = 10;
                        continue;
                    } else {
                        v___x_2754_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2499_ = v___x_2754_;
                        state = 10;
                        continue;
                    }
                }
                10 => {
                    v___x_2755_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2756_ = lean_nat_dec_le(v___x_2755_, v_prec_2434_);
                    if v___x_2756_ == 0 {
                        v___x_2757_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2506_ = v___x_2757_;
                        state = 11;
                        continue;
                    } else {
                        v___x_2758_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2506_ = v___x_2758_;
                        state = 11;
                        continue;
                    }
                }
                11 => {
                    v___x_2759_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2760_ = lean_nat_dec_le(v___x_2759_, v_prec_2434_);
                    if v___x_2760_ == 0 {
                        v___x_2761_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2513_ = v___x_2761_;
                        state = 12;
                        continue;
                    } else {
                        v___x_2762_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2513_ = v___x_2762_;
                        state = 12;
                        continue;
                    }
                }
                12 => {
                    v___x_2763_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2764_ = lean_nat_dec_le(v___x_2763_, v_prec_2434_);
                    if v___x_2764_ == 0 {
                        v___x_2765_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2520_ = v___x_2765_;
                        state = 13;
                        continue;
                    } else {
                        v___x_2766_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2520_ = v___x_2766_;
                        state = 13;
                        continue;
                    }
                }
                13 => {
                    v___x_2767_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2768_ = lean_nat_dec_le(v___x_2767_, v_prec_2434_);
                    if v___x_2768_ == 0 {
                        v___x_2769_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2527_ = v___x_2769_;
                        state = 14;
                        continue;
                    } else {
                        v___x_2770_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2527_ = v___x_2770_;
                        state = 14;
                        continue;
                    }
                }
                14 => {
                    v___x_2771_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2772_ = lean_nat_dec_le(v___x_2771_, v_prec_2434_);
                    if v___x_2772_ == 0 {
                        v___x_2773_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2534_ = v___x_2773_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2774_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2534_ = v___x_2774_;
                        state = 15;
                        continue;
                    }
                }
                15 => {
                    v___x_2775_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2776_ = lean_nat_dec_le(v___x_2775_, v_prec_2434_);
                    if v___x_2776_ == 0 {
                        v___x_2777_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2541_ = v___x_2777_;
                        state = 16;
                        continue;
                    } else {
                        v___x_2778_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2541_ = v___x_2778_;
                        state = 16;
                        continue;
                    }
                }
                16 => {
                    v___x_2779_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2780_ = lean_nat_dec_le(v___x_2779_, v_prec_2434_);
                    if v___x_2780_ == 0 {
                        v___x_2781_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2548_ = v___x_2781_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2782_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2548_ = v___x_2782_;
                        state = 17;
                        continue;
                    }
                }
                17 => {
                    v___x_2783_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2784_ = lean_nat_dec_le(v___x_2783_, v_prec_2434_);
                    if v___x_2784_ == 0 {
                        v___x_2785_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2555_ = v___x_2785_;
                        state = 18;
                        continue;
                    } else {
                        v___x_2786_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2555_ = v___x_2786_;
                        state = 18;
                        continue;
                    }
                }
                18 => {
                    v___x_2787_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2788_ = lean_nat_dec_le(v___x_2787_, v_prec_2434_);
                    if v___x_2788_ == 0 {
                        v___x_2789_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2562_ = v___x_2789_;
                        state = 19;
                        continue;
                    } else {
                        v___x_2790_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2562_ = v___x_2790_;
                        state = 19;
                        continue;
                    }
                }
                19 => {
                    v___x_2791_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2792_ = lean_nat_dec_le(v___x_2791_, v_prec_2434_);
                    if v___x_2792_ == 0 {
                        v___x_2793_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2569_ = v___x_2793_;
                        state = 20;
                        continue;
                    } else {
                        v___x_2794_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2569_ = v___x_2794_;
                        state = 20;
                        continue;
                    }
                }
                20 => {
                    v___x_2795_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2796_ = lean_nat_dec_le(v___x_2795_, v_prec_2434_);
                    if v___x_2796_ == 0 {
                        v___x_2797_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2576_ = v___x_2797_;
                        state = 21;
                        continue;
                    } else {
                        v___x_2798_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2576_ = v___x_2798_;
                        state = 21;
                        continue;
                    }
                }
                21 => {
                    v___x_2799_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2800_ = lean_nat_dec_le(v___x_2799_, v_prec_2434_);
                    if v___x_2800_ == 0 {
                        v___x_2801_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2583_ = v___x_2801_;
                        state = 22;
                        continue;
                    } else {
                        v___x_2802_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2583_ = v___x_2802_;
                        state = 22;
                        continue;
                    }
                }
                22 => {
                    v___x_2803_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2804_ = lean_nat_dec_le(v___x_2803_, v_prec_2434_);
                    if v___x_2804_ == 0 {
                        v___x_2805_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2590_ = v___x_2805_;
                        state = 23;
                        continue;
                    } else {
                        v___x_2806_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2590_ = v___x_2806_;
                        state = 23;
                        continue;
                    }
                }
                23 => {
                    v___x_2807_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2808_ = lean_nat_dec_le(v___x_2807_, v_prec_2434_);
                    if v___x_2808_ == 0 {
                        v___x_2809_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2597_ = v___x_2809_;
                        state = 24;
                        continue;
                    } else {
                        v___x_2810_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2597_ = v___x_2810_;
                        state = 24;
                        continue;
                    }
                }
                24 => {
                    v___x_2811_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2812_ = lean_nat_dec_le(v___x_2811_, v_prec_2434_);
                    if v___x_2812_ == 0 {
                        v___x_2813_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2604_ = v___x_2813_;
                        state = 25;
                        continue;
                    } else {
                        v___x_2814_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2604_ = v___x_2814_;
                        state = 25;
                        continue;
                    }
                }
                25 => {
                    v___x_2815_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2816_ = lean_nat_dec_le(v___x_2815_, v_prec_2434_);
                    if v___x_2816_ == 0 {
                        v___x_2817_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2611_ = v___x_2817_;
                        state = 26;
                        continue;
                    } else {
                        v___x_2818_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2611_ = v___x_2818_;
                        state = 26;
                        continue;
                    }
                }
                26 => {
                    v___x_2819_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2820_ = lean_nat_dec_le(v___x_2819_, v_prec_2434_);
                    if v___x_2820_ == 0 {
                        v___x_2821_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2618_ = v___x_2821_;
                        state = 27;
                        continue;
                    } else {
                        v___x_2822_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2618_ = v___x_2822_;
                        state = 27;
                        continue;
                    }
                }
                27 => {
                    v___x_2823_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2824_ = lean_nat_dec_le(v___x_2823_, v_prec_2434_);
                    if v___x_2824_ == 0 {
                        v___x_2825_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2625_ = v___x_2825_;
                        state = 28;
                        continue;
                    } else {
                        v___x_2826_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2625_ = v___x_2826_;
                        state = 28;
                        continue;
                    }
                }
                28 => {
                    v___x_2827_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2828_ = lean_nat_dec_le(v___x_2827_, v_prec_2434_);
                    if v___x_2828_ == 0 {
                        v___x_2829_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2632_ = v___x_2829_;
                        state = 29;
                        continue;
                    } else {
                        v___x_2830_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2632_ = v___x_2830_;
                        state = 29;
                        continue;
                    }
                }
                29 => {
                    v___x_2831_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2832_ = lean_nat_dec_le(v___x_2831_, v_prec_2434_);
                    if v___x_2832_ == 0 {
                        v___x_2833_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2639_ = v___x_2833_;
                        state = 30;
                        continue;
                    } else {
                        v___x_2834_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2639_ = v___x_2834_;
                        state = 30;
                        continue;
                    }
                }
                30 => {
                    v___x_2835_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2836_ = lean_nat_dec_le(v___x_2835_, v_prec_2434_);
                    if v___x_2836_ == 0 {
                        v___x_2837_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2646_ = v___x_2837_;
                        state = 31;
                        continue;
                    } else {
                        v___x_2838_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2646_ = v___x_2838_;
                        state = 31;
                        continue;
                    }
                }
                31 => {
                    v___x_2839_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2840_ = lean_nat_dec_le(v___x_2839_, v_prec_2434_);
                    if v___x_2840_ == 0 {
                        v___x_2841_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2653_ = v___x_2841_;
                        state = 32;
                        continue;
                    } else {
                        v___x_2842_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2653_ = v___x_2842_;
                        state = 32;
                        continue;
                    }
                }
                32 => {
                    v___x_2843_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2844_ = lean_nat_dec_le(v___x_2843_, v_prec_2434_);
                    if v___x_2844_ == 0 {
                        v___x_2845_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2660_ = v___x_2845_;
                        state = 33;
                        continue;
                    } else {
                        v___x_2846_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2660_ = v___x_2846_;
                        state = 33;
                        continue;
                    }
                }
                33 => {
                    v___x_2847_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2848_ = lean_nat_dec_le(v___x_2847_, v_prec_2434_);
                    if v___x_2848_ == 0 {
                        v___x_2849_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2667_ = v___x_2849_;
                        state = 34;
                        continue;
                    } else {
                        v___x_2850_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2667_ = v___x_2850_;
                        state = 34;
                        continue;
                    }
                }
                34 => {
                    v___x_2851_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2852_ = lean_nat_dec_le(v___x_2851_, v_prec_2434_);
                    if v___x_2852_ == 0 {
                        v___x_2853_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2674_ = v___x_2853_;
                        state = 35;
                        continue;
                    } else {
                        v___x_2854_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2674_ = v___x_2854_;
                        state = 35;
                        continue;
                    }
                }
                35 => {
                    v___x_2855_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2856_ = lean_nat_dec_le(v___x_2855_, v_prec_2434_);
                    if v___x_2856_ == 0 {
                        v___x_2857_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2681_ = v___x_2857_;
                        state = 36;
                        continue;
                    } else {
                        v___x_2858_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2681_ = v___x_2858_;
                        state = 36;
                        continue;
                    }
                }
                36 => {
                    v___x_2859_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2860_ = lean_nat_dec_le(v___x_2859_, v_prec_2434_);
                    if v___x_2860_ == 0 {
                        v___x_2861_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2688_ = v___x_2861_;
                        state = 37;
                        continue;
                    } else {
                        v___x_2862_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2688_ = v___x_2862_;
                        state = 37;
                        continue;
                    }
                }
                37 => {
                    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2864_ = lean_nat_dec_le(v___x_2863_, v_prec_2434_);
                    if v___x_2864_ == 0 {
                        v___x_2865_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2695_ = v___x_2865_;
                        state = 38;
                        continue;
                    } else {
                        v___x_2866_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2695_ = v___x_2866_;
                        state = 38;
                        continue;
                    }
                }
                38 => {
                    v___x_2867_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2868_ = lean_nat_dec_le(v___x_2867_, v_prec_2434_);
                    if v___x_2868_ == 0 {
                        v___x_2869_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2702_ = v___x_2869_;
                        state = 39;
                        continue;
                    } else {
                        v___x_2870_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2702_ = v___x_2870_;
                        state = 39;
                        continue;
                    }
                }
                _ => {
                    v___x_2871_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2872_ = lean_nat_dec_le(v___x_2871_, v_prec_2434_);
                    if v___x_2872_ == 0 {
                        v___x_2873_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__80),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__80_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__80,
                        );
                        v___y_2709_ = v___x_2873_;
                        state = 40;
                        continue;
                    } else {
                        v___x_2874_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprMethod_repr___closed__81),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprMethod_repr___closed__81_once
                            ),
                            _init_l_Std_Http_instReprMethod_repr___closed__81,
                        );
                        v___y_2709_ = v___x_2874_;
                        state = 40;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2437_ = l_Std_Http_instReprMethod_repr___closed__1;
                crate::leanh::lean_inc(v___y_2436_);
                v___x_2438_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2438_, 0, v___y_2436_);
                crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2437_);
                v___x_2439_ = 0;
                v___x_2440_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2440_, 0, v___x_2438_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2440_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2439_,
                );
                v___x_2441_ = l_Repr_addAppParen(v___x_2440_, v_prec_2434_);
                return v___x_2441_;
            }
            2 => {
                v___x_2444_ = l_Std_Http_instReprMethod_repr___closed__3;
                crate::leanh::lean_inc(v___y_2443_);
                v___x_2445_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2445_, 0, v___y_2443_);
                crate::leanh::lean_ctor_set(v___x_2445_, 1, v___x_2444_);
                v___x_2446_ = 0;
                v___x_2447_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2447_, 0, v___x_2445_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2447_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2446_,
                );
                v___x_2448_ = l_Repr_addAppParen(v___x_2447_, v_prec_2434_);
                return v___x_2448_;
            }
            3 => {
                v___x_2451_ = l_Std_Http_instReprMethod_repr___closed__5;
                crate::leanh::lean_inc(v___y_2450_);
                v___x_2452_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2452_, 0, v___y_2450_);
                crate::leanh::lean_ctor_set(v___x_2452_, 1, v___x_2451_);
                v___x_2453_ = 0;
                v___x_2454_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2454_, 0, v___x_2452_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2454_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2453_,
                );
                v___x_2455_ = l_Repr_addAppParen(v___x_2454_, v_prec_2434_);
                return v___x_2455_;
            }
            4 => {
                v___x_2458_ = l_Std_Http_instReprMethod_repr___closed__7;
                crate::leanh::lean_inc(v___y_2457_);
                v___x_2459_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2459_, 0, v___y_2457_);
                crate::leanh::lean_ctor_set(v___x_2459_, 1, v___x_2458_);
                v___x_2460_ = 0;
                v___x_2461_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2461_, 0, v___x_2459_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2460_,
                );
                v___x_2462_ = l_Repr_addAppParen(v___x_2461_, v_prec_2434_);
                return v___x_2462_;
            }
            5 => {
                v___x_2465_ = l_Std_Http_instReprMethod_repr___closed__9;
                crate::leanh::lean_inc(v___y_2464_);
                v___x_2466_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2466_, 0, v___y_2464_);
                crate::leanh::lean_ctor_set(v___x_2466_, 1, v___x_2465_);
                v___x_2467_ = 0;
                v___x_2468_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2468_, 0, v___x_2466_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2468_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2467_,
                );
                v___x_2469_ = l_Repr_addAppParen(v___x_2468_, v_prec_2434_);
                return v___x_2469_;
            }
            6 => {
                v___x_2472_ = l_Std_Http_instReprMethod_repr___closed__11;
                crate::leanh::lean_inc(v___y_2471_);
                v___x_2473_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2473_, 0, v___y_2471_);
                crate::leanh::lean_ctor_set(v___x_2473_, 1, v___x_2472_);
                v___x_2474_ = 0;
                v___x_2475_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2475_, 0, v___x_2473_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2474_,
                );
                v___x_2476_ = l_Repr_addAppParen(v___x_2475_, v_prec_2434_);
                return v___x_2476_;
            }
            7 => {
                v___x_2479_ = l_Std_Http_instReprMethod_repr___closed__13;
                crate::leanh::lean_inc(v___y_2478_);
                v___x_2480_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2480_, 0, v___y_2478_);
                crate::leanh::lean_ctor_set(v___x_2480_, 1, v___x_2479_);
                v___x_2481_ = 0;
                v___x_2482_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2480_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2482_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2481_,
                );
                v___x_2483_ = l_Repr_addAppParen(v___x_2482_, v_prec_2434_);
                return v___x_2483_;
            }
            8 => {
                v___x_2486_ = l_Std_Http_instReprMethod_repr___closed__15;
                crate::leanh::lean_inc(v___y_2485_);
                v___x_2487_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2487_, 0, v___y_2485_);
                crate::leanh::lean_ctor_set(v___x_2487_, 1, v___x_2486_);
                v___x_2488_ = 0;
                v___x_2489_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2489_, 0, v___x_2487_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2489_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2488_,
                );
                v___x_2490_ = l_Repr_addAppParen(v___x_2489_, v_prec_2434_);
                return v___x_2490_;
            }
            9 => {
                v___x_2493_ = l_Std_Http_instReprMethod_repr___closed__17;
                crate::leanh::lean_inc(v___y_2492_);
                v___x_2494_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2494_, 0, v___y_2492_);
                crate::leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                v___x_2495_ = 0;
                v___x_2496_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2496_, 0, v___x_2494_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2496_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2495_,
                );
                v___x_2497_ = l_Repr_addAppParen(v___x_2496_, v_prec_2434_);
                return v___x_2497_;
            }
            10 => {
                v___x_2500_ = l_Std_Http_instReprMethod_repr___closed__19;
                crate::leanh::lean_inc(v___y_2499_);
                v___x_2501_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2501_, 0, v___y_2499_);
                crate::leanh::lean_ctor_set(v___x_2501_, 1, v___x_2500_);
                v___x_2502_ = 0;
                v___x_2503_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2503_, 0, v___x_2501_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2503_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2502_,
                );
                v___x_2504_ = l_Repr_addAppParen(v___x_2503_, v_prec_2434_);
                return v___x_2504_;
            }
            11 => {
                v___x_2507_ = l_Std_Http_instReprMethod_repr___closed__21;
                crate::leanh::lean_inc(v___y_2506_);
                v___x_2508_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2508_, 0, v___y_2506_);
                crate::leanh::lean_ctor_set(v___x_2508_, 1, v___x_2507_);
                v___x_2509_ = 0;
                v___x_2510_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2508_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2510_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2509_,
                );
                v___x_2511_ = l_Repr_addAppParen(v___x_2510_, v_prec_2434_);
                return v___x_2511_;
            }
            12 => {
                v___x_2514_ = l_Std_Http_instReprMethod_repr___closed__23;
                crate::leanh::lean_inc(v___y_2513_);
                v___x_2515_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2515_, 0, v___y_2513_);
                crate::leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
                v___x_2516_ = 0;
                v___x_2517_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2515_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2517_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2516_,
                );
                v___x_2518_ = l_Repr_addAppParen(v___x_2517_, v_prec_2434_);
                return v___x_2518_;
            }
            13 => {
                v___x_2521_ = l_Std_Http_instReprMethod_repr___closed__25;
                crate::leanh::lean_inc(v___y_2520_);
                v___x_2522_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2522_, 0, v___y_2520_);
                crate::leanh::lean_ctor_set(v___x_2522_, 1, v___x_2521_);
                v___x_2523_ = 0;
                v___x_2524_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2522_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2524_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2523_,
                );
                v___x_2525_ = l_Repr_addAppParen(v___x_2524_, v_prec_2434_);
                return v___x_2525_;
            }
            14 => {
                v___x_2528_ = l_Std_Http_instReprMethod_repr___closed__27;
                crate::leanh::lean_inc(v___y_2527_);
                v___x_2529_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v___y_2527_);
                crate::leanh::lean_ctor_set(v___x_2529_, 1, v___x_2528_);
                v___x_2530_ = 0;
                v___x_2531_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2529_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2530_,
                );
                v___x_2532_ = l_Repr_addAppParen(v___x_2531_, v_prec_2434_);
                return v___x_2532_;
            }
            15 => {
                v___x_2535_ = l_Std_Http_instReprMethod_repr___closed__29;
                crate::leanh::lean_inc(v___y_2534_);
                v___x_2536_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2536_, 0, v___y_2534_);
                crate::leanh::lean_ctor_set(v___x_2536_, 1, v___x_2535_);
                v___x_2537_ = 0;
                v___x_2538_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2538_, 0, v___x_2536_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2538_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2537_,
                );
                v___x_2539_ = l_Repr_addAppParen(v___x_2538_, v_prec_2434_);
                return v___x_2539_;
            }
            16 => {
                v___x_2542_ = l_Std_Http_instReprMethod_repr___closed__31;
                crate::leanh::lean_inc(v___y_2541_);
                v___x_2543_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2543_, 0, v___y_2541_);
                crate::leanh::lean_ctor_set(v___x_2543_, 1, v___x_2542_);
                v___x_2544_ = 0;
                v___x_2545_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2543_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2545_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2544_,
                );
                v___x_2546_ = l_Repr_addAppParen(v___x_2545_, v_prec_2434_);
                return v___x_2546_;
            }
            17 => {
                v___x_2549_ = l_Std_Http_instReprMethod_repr___closed__33;
                crate::leanh::lean_inc(v___y_2548_);
                v___x_2550_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2550_, 0, v___y_2548_);
                crate::leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
                v___x_2551_ = 0;
                v___x_2552_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2550_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2552_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2551_,
                );
                v___x_2553_ = l_Repr_addAppParen(v___x_2552_, v_prec_2434_);
                return v___x_2553_;
            }
            18 => {
                v___x_2556_ = l_Std_Http_instReprMethod_repr___closed__35;
                crate::leanh::lean_inc(v___y_2555_);
                v___x_2557_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2557_, 0, v___y_2555_);
                crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2556_);
                v___x_2558_ = 0;
                v___x_2559_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2559_, 0, v___x_2557_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2559_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2558_,
                );
                v___x_2560_ = l_Repr_addAppParen(v___x_2559_, v_prec_2434_);
                return v___x_2560_;
            }
            19 => {
                v___x_2563_ = l_Std_Http_instReprMethod_repr___closed__37;
                crate::leanh::lean_inc(v___y_2562_);
                v___x_2564_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2564_, 0, v___y_2562_);
                crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
                v___x_2565_ = 0;
                v___x_2566_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2566_, 0, v___x_2564_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2565_,
                );
                v___x_2567_ = l_Repr_addAppParen(v___x_2566_, v_prec_2434_);
                return v___x_2567_;
            }
            20 => {
                v___x_2570_ = l_Std_Http_instReprMethod_repr___closed__39;
                crate::leanh::lean_inc(v___y_2569_);
                v___x_2571_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2571_, 0, v___y_2569_);
                crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2570_);
                v___x_2572_ = 0;
                v___x_2573_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2573_, 0, v___x_2571_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2572_,
                );
                v___x_2574_ = l_Repr_addAppParen(v___x_2573_, v_prec_2434_);
                return v___x_2574_;
            }
            21 => {
                v___x_2577_ = l_Std_Http_instReprMethod_repr___closed__41;
                crate::leanh::lean_inc(v___y_2576_);
                v___x_2578_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2578_, 0, v___y_2576_);
                crate::leanh::lean_ctor_set(v___x_2578_, 1, v___x_2577_);
                v___x_2579_ = 0;
                v___x_2580_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2580_, 0, v___x_2578_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2579_,
                );
                v___x_2581_ = l_Repr_addAppParen(v___x_2580_, v_prec_2434_);
                return v___x_2581_;
            }
            22 => {
                v___x_2584_ = l_Std_Http_instReprMethod_repr___closed__43;
                crate::leanh::lean_inc(v___y_2583_);
                v___x_2585_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2585_, 0, v___y_2583_);
                crate::leanh::lean_ctor_set(v___x_2585_, 1, v___x_2584_);
                v___x_2586_ = 0;
                v___x_2587_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2587_, 0, v___x_2585_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2586_,
                );
                v___x_2588_ = l_Repr_addAppParen(v___x_2587_, v_prec_2434_);
                return v___x_2588_;
            }
            23 => {
                v___x_2591_ = l_Std_Http_instReprMethod_repr___closed__45;
                crate::leanh::lean_inc(v___y_2590_);
                v___x_2592_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2592_, 0, v___y_2590_);
                crate::leanh::lean_ctor_set(v___x_2592_, 1, v___x_2591_);
                v___x_2593_ = 0;
                v___x_2594_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2594_, 0, v___x_2592_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2593_,
                );
                v___x_2595_ = l_Repr_addAppParen(v___x_2594_, v_prec_2434_);
                return v___x_2595_;
            }
            24 => {
                v___x_2598_ = l_Std_Http_instReprMethod_repr___closed__47;
                crate::leanh::lean_inc(v___y_2597_);
                v___x_2599_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2599_, 0, v___y_2597_);
                crate::leanh::lean_ctor_set(v___x_2599_, 1, v___x_2598_);
                v___x_2600_ = 0;
                v___x_2601_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2601_, 0, v___x_2599_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2601_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2600_,
                );
                v___x_2602_ = l_Repr_addAppParen(v___x_2601_, v_prec_2434_);
                return v___x_2602_;
            }
            25 => {
                v___x_2605_ = l_Std_Http_instReprMethod_repr___closed__49;
                crate::leanh::lean_inc(v___y_2604_);
                v___x_2606_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2606_, 0, v___y_2604_);
                crate::leanh::lean_ctor_set(v___x_2606_, 1, v___x_2605_);
                v___x_2607_ = 0;
                v___x_2608_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2606_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2607_,
                );
                v___x_2609_ = l_Repr_addAppParen(v___x_2608_, v_prec_2434_);
                return v___x_2609_;
            }
            26 => {
                v___x_2612_ = l_Std_Http_instReprMethod_repr___closed__51;
                crate::leanh::lean_inc(v___y_2611_);
                v___x_2613_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2613_, 0, v___y_2611_);
                crate::leanh::lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                v___x_2614_ = 0;
                v___x_2615_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2615_, 0, v___x_2613_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2614_,
                );
                v___x_2616_ = l_Repr_addAppParen(v___x_2615_, v_prec_2434_);
                return v___x_2616_;
            }
            27 => {
                v___x_2619_ = l_Std_Http_instReprMethod_repr___closed__53;
                crate::leanh::lean_inc(v___y_2618_);
                v___x_2620_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2620_, 0, v___y_2618_);
                crate::leanh::lean_ctor_set(v___x_2620_, 1, v___x_2619_);
                v___x_2621_ = 0;
                v___x_2622_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2620_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2622_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2621_,
                );
                v___x_2623_ = l_Repr_addAppParen(v___x_2622_, v_prec_2434_);
                return v___x_2623_;
            }
            28 => {
                v___x_2626_ = l_Std_Http_instReprMethod_repr___closed__55;
                crate::leanh::lean_inc(v___y_2625_);
                v___x_2627_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v___y_2625_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = 0;
                v___x_2629_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2629_, 0, v___x_2627_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2628_,
                );
                v___x_2630_ = l_Repr_addAppParen(v___x_2629_, v_prec_2434_);
                return v___x_2630_;
            }
            29 => {
                v___x_2633_ = l_Std_Http_instReprMethod_repr___closed__57;
                crate::leanh::lean_inc(v___y_2632_);
                v___x_2634_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2634_, 0, v___y_2632_);
                crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                v___x_2635_ = 0;
                v___x_2636_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2634_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2636_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2635_,
                );
                v___x_2637_ = l_Repr_addAppParen(v___x_2636_, v_prec_2434_);
                return v___x_2637_;
            }
            30 => {
                v___x_2640_ = l_Std_Http_instReprMethod_repr___closed__59;
                crate::leanh::lean_inc(v___y_2639_);
                v___x_2641_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2641_, 0, v___y_2639_);
                crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2640_);
                v___x_2642_ = 0;
                v___x_2643_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2641_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2643_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2642_,
                );
                v___x_2644_ = l_Repr_addAppParen(v___x_2643_, v_prec_2434_);
                return v___x_2644_;
            }
            31 => {
                v___x_2647_ = l_Std_Http_instReprMethod_repr___closed__61;
                crate::leanh::lean_inc(v___y_2646_);
                v___x_2648_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2648_, 0, v___y_2646_);
                crate::leanh::lean_ctor_set(v___x_2648_, 1, v___x_2647_);
                v___x_2649_ = 0;
                v___x_2650_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2650_, 0, v___x_2648_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2650_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2649_,
                );
                v___x_2651_ = l_Repr_addAppParen(v___x_2650_, v_prec_2434_);
                return v___x_2651_;
            }
            32 => {
                v___x_2654_ = l_Std_Http_instReprMethod_repr___closed__63;
                crate::leanh::lean_inc(v___y_2653_);
                v___x_2655_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v___y_2653_);
                crate::leanh::lean_ctor_set(v___x_2655_, 1, v___x_2654_);
                v___x_2656_ = 0;
                v___x_2657_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2655_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2657_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2656_,
                );
                v___x_2658_ = l_Repr_addAppParen(v___x_2657_, v_prec_2434_);
                return v___x_2658_;
            }
            33 => {
                v___x_2661_ = l_Std_Http_instReprMethod_repr___closed__65;
                crate::leanh::lean_inc(v___y_2660_);
                v___x_2662_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2662_, 0, v___y_2660_);
                crate::leanh::lean_ctor_set(v___x_2662_, 1, v___x_2661_);
                v___x_2663_ = 0;
                v___x_2664_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2664_, 0, v___x_2662_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2664_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2663_,
                );
                v___x_2665_ = l_Repr_addAppParen(v___x_2664_, v_prec_2434_);
                return v___x_2665_;
            }
            34 => {
                v___x_2668_ = l_Std_Http_instReprMethod_repr___closed__67;
                crate::leanh::lean_inc(v___y_2667_);
                v___x_2669_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2669_, 0, v___y_2667_);
                crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2668_);
                v___x_2670_ = 0;
                v___x_2671_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2671_, 0, v___x_2669_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2670_,
                );
                v___x_2672_ = l_Repr_addAppParen(v___x_2671_, v_prec_2434_);
                return v___x_2672_;
            }
            35 => {
                v___x_2675_ = l_Std_Http_instReprMethod_repr___closed__69;
                crate::leanh::lean_inc(v___y_2674_);
                v___x_2676_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2676_, 0, v___y_2674_);
                crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
                v___x_2677_ = 0;
                v___x_2678_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2678_, 0, v___x_2676_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2678_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2677_,
                );
                v___x_2679_ = l_Repr_addAppParen(v___x_2678_, v_prec_2434_);
                return v___x_2679_;
            }
            36 => {
                v___x_2682_ = l_Std_Http_instReprMethod_repr___closed__71;
                crate::leanh::lean_inc(v___y_2681_);
                v___x_2683_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2683_, 0, v___y_2681_);
                crate::leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                v___x_2684_ = 0;
                v___x_2685_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2685_, 0, v___x_2683_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2684_,
                );
                v___x_2686_ = l_Repr_addAppParen(v___x_2685_, v_prec_2434_);
                return v___x_2686_;
            }
            37 => {
                v___x_2689_ = l_Std_Http_instReprMethod_repr___closed__73;
                crate::leanh::lean_inc(v___y_2688_);
                v___x_2690_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2690_, 0, v___y_2688_);
                crate::leanh::lean_ctor_set(v___x_2690_, 1, v___x_2689_);
                v___x_2691_ = 0;
                v___x_2692_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2692_, 0, v___x_2690_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2692_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2691_,
                );
                v___x_2693_ = l_Repr_addAppParen(v___x_2692_, v_prec_2434_);
                return v___x_2693_;
            }
            38 => {
                v___x_2696_ = l_Std_Http_instReprMethod_repr___closed__75;
                crate::leanh::lean_inc(v___y_2695_);
                v___x_2697_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2697_, 0, v___y_2695_);
                crate::leanh::lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                v___x_2698_ = 0;
                v___x_2699_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2697_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2698_,
                );
                v___x_2700_ = l_Repr_addAppParen(v___x_2699_, v_prec_2434_);
                return v___x_2700_;
            }
            39 => {
                v___x_2703_ = l_Std_Http_instReprMethod_repr___closed__77;
                crate::leanh::lean_inc(v___y_2702_);
                v___x_2704_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2704_, 0, v___y_2702_);
                crate::leanh::lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                v___x_2705_ = 0;
                v___x_2706_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2706_, 0, v___x_2704_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2706_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2705_,
                );
                v___x_2707_ = l_Repr_addAppParen(v___x_2706_, v_prec_2434_);
                return v___x_2707_;
            }
            40 => {
                v___x_2710_ = l_Std_Http_instReprMethod_repr___closed__79;
                crate::leanh::lean_inc(v___y_2709_);
                v___x_2711_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2711_, 0, v___y_2709_);
                crate::leanh::lean_ctor_set(v___x_2711_, 1, v___x_2710_);
                v___x_2712_ = 0;
                v___x_2713_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2713_, 0, v___x_2711_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2713_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2712_,
                );
                v___x_2714_ = l_Repr_addAppParen(v___x_2713_, v_prec_2434_);
                return v___x_2714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instReprMethod_repr___boxed(
    mut v_x_2875_: *mut crate::leanh::LeanObject,
    mut v_prec_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2249__boxed_2877_: u8 = 0;
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2249__boxed_2877_ = (crate::leanh::lean_unbox(v_x_2875_) as u8);
    v_res_2878_ = l_Std_Http_instReprMethod_repr(v_x_2249__boxed_2877_, v_prec_2876_);
    crate::leanh::lean_dec(v_prec_2876_);
    return v_res_2878_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedMethod_default() -> u8 {
    let mut v___x_2881_: u8 = 0;
    v___x_2881_ = 0;
    return v___x_2881_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedMethod() -> u8 {
    let mut v___x_2882_: u8 = 0;
    v___x_2882_ = 0;
    return v___x_2882_;
}
pub unsafe fn l_Std_Http_instBEqMethod_beq(mut v_x_2883_: u8, mut v_y_2884_: u8) -> u8 {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: u8 = 0;
    v___x_2885_ = l_Std_Http_Method_ctorIdx(v_x_2883_);
    v___x_2886_ = l_Std_Http_Method_ctorIdx(v_y_2884_);
    v___x_2887_ = lean_nat_dec_eq(v___x_2885_, v___x_2886_);
    crate::leanh::lean_dec(v___x_2886_);
    crate::leanh::lean_dec(v___x_2885_);
    return v___x_2887_;
}
pub unsafe fn l_Std_Http_instBEqMethod_beq___boxed(
    mut v_x_2888_: *mut crate::leanh::LeanObject,
    mut v_y_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2890_: u8 = 0;
    let mut v_y_18__boxed_2891_: u8 = 0;
    let mut v_res_2892_: u8 = 0;
    let mut v_r_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2890_ = (crate::leanh::lean_unbox(v_x_2888_) as u8);
    v_y_18__boxed_2891_ = (crate::leanh::lean_unbox(v_y_2889_) as u8);
    v_res_2892_ = l_Std_Http_instBEqMethod_beq(v_x_17__boxed_2890_, v_y_18__boxed_2891_);
    v_r_2893_ = crate::leanh::lean_box((v_res_2892_) as usize);
    return v_r_2893_;
}
pub unsafe fn l_Std_Http_Method_ofNat(mut v_n_2896_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    v___x_2897_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_2898_ = lean_nat_dec_le(v_n_2896_, v___x_2897_);
    if v___x_2898_ == 0 {
        let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: u8 = 0;
        v___x_2899_ = crate::leanh::lean_unsigned_to_nat(29);
        v___x_2900_ = lean_nat_dec_le(v_n_2896_, v___x_2899_);
        if v___x_2900_ == 0 {
            let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2902_: u8 = 0;
            v___x_2901_ = crate::leanh::lean_unsigned_to_nat(34);
            v___x_2902_ = lean_nat_dec_le(v_n_2896_, v___x_2901_);
            if v___x_2902_ == 0 {
                let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2904_: u8 = 0;
                v___x_2903_ = crate::leanh::lean_unsigned_to_nat(36);
                v___x_2904_ = lean_nat_dec_le(v_n_2896_, v___x_2903_);
                if v___x_2904_ == 0 {
                    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2906_: u8 = 0;
                    v___x_2905_ = crate::leanh::lean_unsigned_to_nat(37);
                    v___x_2906_ = lean_nat_dec_le(v_n_2896_, v___x_2905_);
                    if v___x_2906_ == 0 {
                        let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2908_: u8 = 0;
                        v___x_2907_ = crate::leanh::lean_unsigned_to_nat(38);
                        v___x_2908_ = lean_nat_dec_le(v_n_2896_, v___x_2907_);
                        if v___x_2908_ == 0 {
                            let mut v___x_2909_: u8 = 0;
                            v___x_2909_ = 39;
                            return v___x_2909_;
                        } else {
                            let mut v___x_2910_: u8 = 0;
                            v___x_2910_ = 38;
                            return v___x_2910_;
                        }
                    } else {
                        let mut v___x_2911_: u8 = 0;
                        v___x_2911_ = 37;
                        return v___x_2911_;
                    }
                } else {
                    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2913_: u8 = 0;
                    v___x_2912_ = crate::leanh::lean_unsigned_to_nat(35);
                    v___x_2913_ = lean_nat_dec_le(v_n_2896_, v___x_2912_);
                    if v___x_2913_ == 0 {
                        let mut v___x_2914_: u8 = 0;
                        v___x_2914_ = 36;
                        return v___x_2914_;
                    } else {
                        let mut v___x_2915_: u8 = 0;
                        v___x_2915_ = 35;
                        return v___x_2915_;
                    }
                }
            } else {
                let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2917_: u8 = 0;
                v___x_2916_ = crate::leanh::lean_unsigned_to_nat(31);
                v___x_2917_ = lean_nat_dec_le(v_n_2896_, v___x_2916_);
                if v___x_2917_ == 0 {
                    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2919_: u8 = 0;
                    v___x_2918_ = crate::leanh::lean_unsigned_to_nat(32);
                    v___x_2919_ = lean_nat_dec_le(v_n_2896_, v___x_2918_);
                    if v___x_2919_ == 0 {
                        let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2921_: u8 = 0;
                        v___x_2920_ = crate::leanh::lean_unsigned_to_nat(33);
                        v___x_2921_ = lean_nat_dec_le(v_n_2896_, v___x_2920_);
                        if v___x_2921_ == 0 {
                            let mut v___x_2922_: u8 = 0;
                            v___x_2922_ = 34;
                            return v___x_2922_;
                        } else {
                            let mut v___x_2923_: u8 = 0;
                            v___x_2923_ = 33;
                            return v___x_2923_;
                        }
                    } else {
                        let mut v___x_2924_: u8 = 0;
                        v___x_2924_ = 32;
                        return v___x_2924_;
                    }
                } else {
                    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2926_: u8 = 0;
                    v___x_2925_ = crate::leanh::lean_unsigned_to_nat(30);
                    v___x_2926_ = lean_nat_dec_le(v_n_2896_, v___x_2925_);
                    if v___x_2926_ == 0 {
                        let mut v___x_2927_: u8 = 0;
                        v___x_2927_ = 31;
                        return v___x_2927_;
                    } else {
                        let mut v___x_2928_: u8 = 0;
                        v___x_2928_ = 30;
                        return v___x_2928_;
                    }
                }
            }
        } else {
            let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2930_: u8 = 0;
            v___x_2929_ = crate::leanh::lean_unsigned_to_nat(24);
            v___x_2930_ = lean_nat_dec_le(v_n_2896_, v___x_2929_);
            if v___x_2930_ == 0 {
                let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2932_: u8 = 0;
                v___x_2931_ = crate::leanh::lean_unsigned_to_nat(26);
                v___x_2932_ = lean_nat_dec_le(v_n_2896_, v___x_2931_);
                if v___x_2932_ == 0 {
                    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2934_: u8 = 0;
                    v___x_2933_ = crate::leanh::lean_unsigned_to_nat(27);
                    v___x_2934_ = lean_nat_dec_le(v_n_2896_, v___x_2933_);
                    if v___x_2934_ == 0 {
                        let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2936_: u8 = 0;
                        v___x_2935_ = crate::leanh::lean_unsigned_to_nat(28);
                        v___x_2936_ = lean_nat_dec_le(v_n_2896_, v___x_2935_);
                        if v___x_2936_ == 0 {
                            let mut v___x_2937_: u8 = 0;
                            v___x_2937_ = 29;
                            return v___x_2937_;
                        } else {
                            let mut v___x_2938_: u8 = 0;
                            v___x_2938_ = 28;
                            return v___x_2938_;
                        }
                    } else {
                        let mut v___x_2939_: u8 = 0;
                        v___x_2939_ = 27;
                        return v___x_2939_;
                    }
                } else {
                    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2941_: u8 = 0;
                    v___x_2940_ = crate::leanh::lean_unsigned_to_nat(25);
                    v___x_2941_ = lean_nat_dec_le(v_n_2896_, v___x_2940_);
                    if v___x_2941_ == 0 {
                        let mut v___x_2942_: u8 = 0;
                        v___x_2942_ = 26;
                        return v___x_2942_;
                    } else {
                        let mut v___x_2943_: u8 = 0;
                        v___x_2943_ = 25;
                        return v___x_2943_;
                    }
                }
            } else {
                let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2945_: u8 = 0;
                v___x_2944_ = crate::leanh::lean_unsigned_to_nat(21);
                v___x_2945_ = lean_nat_dec_le(v_n_2896_, v___x_2944_);
                if v___x_2945_ == 0 {
                    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2947_: u8 = 0;
                    v___x_2946_ = crate::leanh::lean_unsigned_to_nat(22);
                    v___x_2947_ = lean_nat_dec_le(v_n_2896_, v___x_2946_);
                    if v___x_2947_ == 0 {
                        let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2949_: u8 = 0;
                        v___x_2948_ = crate::leanh::lean_unsigned_to_nat(23);
                        v___x_2949_ = lean_nat_dec_le(v_n_2896_, v___x_2948_);
                        if v___x_2949_ == 0 {
                            let mut v___x_2950_: u8 = 0;
                            v___x_2950_ = 24;
                            return v___x_2950_;
                        } else {
                            let mut v___x_2951_: u8 = 0;
                            v___x_2951_ = 23;
                            return v___x_2951_;
                        }
                    } else {
                        let mut v___x_2952_: u8 = 0;
                        v___x_2952_ = 22;
                        return v___x_2952_;
                    }
                } else {
                    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2954_: u8 = 0;
                    v___x_2953_ = crate::leanh::lean_unsigned_to_nat(20);
                    v___x_2954_ = lean_nat_dec_le(v_n_2896_, v___x_2953_);
                    if v___x_2954_ == 0 {
                        let mut v___x_2955_: u8 = 0;
                        v___x_2955_ = 21;
                        return v___x_2955_;
                    } else {
                        let mut v___x_2956_: u8 = 0;
                        v___x_2956_ = 20;
                        return v___x_2956_;
                    }
                }
            }
        }
    } else {
        let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2958_: u8 = 0;
        v___x_2957_ = crate::leanh::lean_unsigned_to_nat(9);
        v___x_2958_ = lean_nat_dec_le(v_n_2896_, v___x_2957_);
        if v___x_2958_ == 0 {
            let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2960_: u8 = 0;
            v___x_2959_ = crate::leanh::lean_unsigned_to_nat(14);
            v___x_2960_ = lean_nat_dec_le(v_n_2896_, v___x_2959_);
            if v___x_2960_ == 0 {
                let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2962_: u8 = 0;
                v___x_2961_ = crate::leanh::lean_unsigned_to_nat(16);
                v___x_2962_ = lean_nat_dec_le(v_n_2896_, v___x_2961_);
                if v___x_2962_ == 0 {
                    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2964_: u8 = 0;
                    v___x_2963_ = crate::leanh::lean_unsigned_to_nat(17);
                    v___x_2964_ = lean_nat_dec_le(v_n_2896_, v___x_2963_);
                    if v___x_2964_ == 0 {
                        let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2966_: u8 = 0;
                        v___x_2965_ = crate::leanh::lean_unsigned_to_nat(18);
                        v___x_2966_ = lean_nat_dec_le(v_n_2896_, v___x_2965_);
                        if v___x_2966_ == 0 {
                            let mut v___x_2967_: u8 = 0;
                            v___x_2967_ = 19;
                            return v___x_2967_;
                        } else {
                            let mut v___x_2968_: u8 = 0;
                            v___x_2968_ = 18;
                            return v___x_2968_;
                        }
                    } else {
                        let mut v___x_2969_: u8 = 0;
                        v___x_2969_ = 17;
                        return v___x_2969_;
                    }
                } else {
                    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2971_: u8 = 0;
                    v___x_2970_ = crate::leanh::lean_unsigned_to_nat(15);
                    v___x_2971_ = lean_nat_dec_le(v_n_2896_, v___x_2970_);
                    if v___x_2971_ == 0 {
                        let mut v___x_2972_: u8 = 0;
                        v___x_2972_ = 16;
                        return v___x_2972_;
                    } else {
                        let mut v___x_2973_: u8 = 0;
                        v___x_2973_ = 15;
                        return v___x_2973_;
                    }
                }
            } else {
                let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2975_: u8 = 0;
                v___x_2974_ = crate::leanh::lean_unsigned_to_nat(11);
                v___x_2975_ = lean_nat_dec_le(v_n_2896_, v___x_2974_);
                if v___x_2975_ == 0 {
                    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2977_: u8 = 0;
                    v___x_2976_ = crate::leanh::lean_unsigned_to_nat(12);
                    v___x_2977_ = lean_nat_dec_le(v_n_2896_, v___x_2976_);
                    if v___x_2977_ == 0 {
                        let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2979_: u8 = 0;
                        v___x_2978_ = crate::leanh::lean_unsigned_to_nat(13);
                        v___x_2979_ = lean_nat_dec_le(v_n_2896_, v___x_2978_);
                        if v___x_2979_ == 0 {
                            let mut v___x_2980_: u8 = 0;
                            v___x_2980_ = 14;
                            return v___x_2980_;
                        } else {
                            let mut v___x_2981_: u8 = 0;
                            v___x_2981_ = 13;
                            return v___x_2981_;
                        }
                    } else {
                        let mut v___x_2982_: u8 = 0;
                        v___x_2982_ = 12;
                        return v___x_2982_;
                    }
                } else {
                    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2984_: u8 = 0;
                    v___x_2983_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_2984_ = lean_nat_dec_le(v_n_2896_, v___x_2983_);
                    if v___x_2984_ == 0 {
                        let mut v___x_2985_: u8 = 0;
                        v___x_2985_ = 11;
                        return v___x_2985_;
                    } else {
                        let mut v___x_2986_: u8 = 0;
                        v___x_2986_ = 10;
                        return v___x_2986_;
                    }
                }
            }
        } else {
            let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2988_: u8 = 0;
            v___x_2987_ = crate::leanh::lean_unsigned_to_nat(4);
            v___x_2988_ = lean_nat_dec_le(v_n_2896_, v___x_2987_);
            if v___x_2988_ == 0 {
                let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2990_: u8 = 0;
                v___x_2989_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2990_ = lean_nat_dec_le(v_n_2896_, v___x_2989_);
                if v___x_2990_ == 0 {
                    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2992_: u8 = 0;
                    v___x_2991_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_2992_ = lean_nat_dec_le(v_n_2896_, v___x_2991_);
                    if v___x_2992_ == 0 {
                        let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2994_: u8 = 0;
                        v___x_2993_ = crate::leanh::lean_unsigned_to_nat(8);
                        v___x_2994_ = lean_nat_dec_le(v_n_2896_, v___x_2993_);
                        if v___x_2994_ == 0 {
                            let mut v___x_2995_: u8 = 0;
                            v___x_2995_ = 9;
                            return v___x_2995_;
                        } else {
                            let mut v___x_2996_: u8 = 0;
                            v___x_2996_ = 8;
                            return v___x_2996_;
                        }
                    } else {
                        let mut v___x_2997_: u8 = 0;
                        v___x_2997_ = 7;
                        return v___x_2997_;
                    }
                } else {
                    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2999_: u8 = 0;
                    v___x_2998_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_2999_ = lean_nat_dec_le(v_n_2896_, v___x_2998_);
                    if v___x_2999_ == 0 {
                        let mut v___x_3000_: u8 = 0;
                        v___x_3000_ = 6;
                        return v___x_3000_;
                    } else {
                        let mut v___x_3001_: u8 = 0;
                        v___x_3001_ = 5;
                        return v___x_3001_;
                    }
                }
            } else {
                let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3003_: u8 = 0;
                v___x_3002_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3003_ = lean_nat_dec_le(v_n_2896_, v___x_3002_);
                if v___x_3003_ == 0 {
                    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3005_: u8 = 0;
                    v___x_3004_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_3005_ = lean_nat_dec_le(v_n_2896_, v___x_3004_);
                    if v___x_3005_ == 0 {
                        let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3007_: u8 = 0;
                        v___x_3006_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3007_ = lean_nat_dec_le(v_n_2896_, v___x_3006_);
                        if v___x_3007_ == 0 {
                            let mut v___x_3008_: u8 = 0;
                            v___x_3008_ = 4;
                            return v___x_3008_;
                        } else {
                            let mut v___x_3009_: u8 = 0;
                            v___x_3009_ = 3;
                            return v___x_3009_;
                        }
                    } else {
                        let mut v___x_3010_: u8 = 0;
                        v___x_3010_ = 2;
                        return v___x_3010_;
                    }
                } else {
                    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3012_: u8 = 0;
                    v___x_3011_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3012_ = lean_nat_dec_le(v_n_2896_, v___x_3011_);
                    if v___x_3012_ == 0 {
                        let mut v___x_3013_: u8 = 0;
                        v___x_3013_ = 1;
                        return v___x_3013_;
                    } else {
                        let mut v___x_3014_: u8 = 0;
                        v___x_3014_ = 0;
                        return v___x_3014_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Http_Method_ofNat___boxed(
    mut v_n_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3016_: u8 = 0;
    let mut v_r_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Std_Http_Method_ofNat(v_n_3015_);
    crate::leanh::lean_dec(v_n_3015_);
    v_r_3017_ = crate::leanh::lean_box((v_res_3016_) as usize);
    return v_r_3017_;
}
pub unsafe fn l_Std_Http_instDecidableEqMethod(mut v_x_3018_: u8, mut v_y_3019_: u8) -> u8 {
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u8 = 0;
    v___x_3020_ = l_Std_Http_Method_ctorIdx(v_x_3018_);
    v___x_3021_ = l_Std_Http_Method_ctorIdx(v_y_3019_);
    v___x_3022_ = lean_nat_dec_eq(v___x_3020_, v___x_3021_);
    crate::leanh::lean_dec(v___x_3021_);
    crate::leanh::lean_dec(v___x_3020_);
    return v___x_3022_;
}
pub unsafe fn l_Std_Http_instDecidableEqMethod___boxed(
    mut v_x_3023_: *mut crate::leanh::LeanObject,
    mut v_y_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_3025_: u8 = 0;
    let mut v_y_14__boxed_3026_: u8 = 0;
    let mut v_res_3027_: u8 = 0;
    let mut v_r_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_3025_ = (crate::leanh::lean_unbox(v_x_3023_) as u8);
    v_y_14__boxed_3026_ = (crate::leanh::lean_unbox(v_y_3024_) as u8);
    v_res_3027_ = l_Std_Http_instDecidableEqMethod(v_x_13__boxed_3025_, v_y_14__boxed_3026_);
    v_r_3028_ = crate::leanh::lean_box((v_res_3027_) as usize);
    return v_r_3028_;
}
pub unsafe fn l_Std_Http_Method_ofString_x3f(
    mut v_x_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    v___x_3190_ = l_Std_Http_Method_ofString_x3f___closed__0;
    v___x_3191_ = lean_string_dec_eq(v_x_3189_, v___x_3190_);
    if v___x_3191_ == 0 {
        let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3193_: u8 = 0;
        v___x_3192_ = l_Std_Http_Method_ofString_x3f___closed__1;
        v___x_3193_ = lean_string_dec_eq(v_x_3189_, v___x_3192_);
        if v___x_3193_ == 0 {
            let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3195_: u8 = 0;
            v___x_3194_ = l_Std_Http_Method_ofString_x3f___closed__2;
            v___x_3195_ = lean_string_dec_eq(v_x_3189_, v___x_3194_);
            if v___x_3195_ == 0 {
                let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3197_: u8 = 0;
                v___x_3196_ = l_Std_Http_Method_ofString_x3f___closed__3;
                v___x_3197_ = lean_string_dec_eq(v_x_3189_, v___x_3196_);
                if v___x_3197_ == 0 {
                    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3199_: u8 = 0;
                    v___x_3198_ = l_Std_Http_Method_ofString_x3f___closed__4;
                    v___x_3199_ = lean_string_dec_eq(v_x_3189_, v___x_3198_);
                    if v___x_3199_ == 0 {
                        let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3201_: u8 = 0;
                        v___x_3200_ = l_Std_Http_Method_ofString_x3f___closed__5;
                        v___x_3201_ = lean_string_dec_eq(v_x_3189_, v___x_3200_);
                        if v___x_3201_ == 0 {
                            let mut v___x_3202_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3203_: u8 = 0;
                            v___x_3202_ = l_Std_Http_Method_ofString_x3f___closed__6;
                            v___x_3203_ = lean_string_dec_eq(v_x_3189_, v___x_3202_);
                            if v___x_3203_ == 0 {
                                let mut v___x_3204_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3205_: u8 = 0;
                                v___x_3204_ = l_Std_Http_Method_ofString_x3f___closed__7;
                                v___x_3205_ = lean_string_dec_eq(v_x_3189_, v___x_3204_);
                                if v___x_3205_ == 0 {
                                    let mut v___x_3206_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3207_: u8 = 0;
                                    v___x_3206_ = l_Std_Http_Method_ofString_x3f___closed__8;
                                    v___x_3207_ = lean_string_dec_eq(v_x_3189_, v___x_3206_);
                                    if v___x_3207_ == 0 {
                                        let mut v___x_3208_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3209_: u8 = 0;
                                        v___x_3208_ = l_Std_Http_Method_ofString_x3f___closed__9;
                                        v___x_3209_ = lean_string_dec_eq(v_x_3189_, v___x_3208_);
                                        if v___x_3209_ == 0 {
                                            let mut v___x_3210_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3211_: u8 = 0;
                                            v___x_3210_ =
                                                l_Std_Http_Method_ofString_x3f___closed__10;
                                            v___x_3211_ =
                                                lean_string_dec_eq(v_x_3189_, v___x_3210_);
                                            if v___x_3211_ == 0 {
                                                let mut v___x_3212_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3213_: u8 = 0;
                                                v___x_3212_ =
                                                    l_Std_Http_Method_ofString_x3f___closed__11;
                                                v___x_3213_ =
                                                    lean_string_dec_eq(v_x_3189_, v___x_3212_);
                                                if v___x_3213_ == 0 {
                                                    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3215_: u8 = 0;
                                                    v___x_3214_ =
                                                        l_Std_Http_Method_ofString_x3f___closed__12;
                                                    v___x_3215_ =
                                                        lean_string_dec_eq(v_x_3189_, v___x_3214_);
                                                    if v___x_3215_ == 0 {
                                                        let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3217_: u8 = 0;
                                                        v___x_3216_ = l_Std_Http_Method_ofString_x3f___closed__13;
                                                        v___x_3217_ = lean_string_dec_eq(
                                                            v_x_3189_,
                                                            v___x_3216_,
                                                        );
                                                        if v___x_3217_ == 0 {
                                                            let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3219_: u8 = 0;
                                                            v___x_3218_ = l_Std_Http_Method_ofString_x3f___closed__14;
                                                            v___x_3219_ = lean_string_dec_eq(
                                                                v_x_3189_,
                                                                v___x_3218_,
                                                            );
                                                            if v___x_3219_ == 0 {
                                                                let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3221_: u8 = 0;
                                                                v___x_3220_ = l_Std_Http_Method_ofString_x3f___closed__15;
                                                                v___x_3221_ = lean_string_dec_eq(
                                                                    v_x_3189_,
                                                                    v___x_3220_,
                                                                );
                                                                if v___x_3221_ == 0 {
                                                                    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3223_: u8 = 0;
                                                                    v___x_3222_ = l_Std_Http_Method_ofString_x3f___closed__16;
                                                                    v___x_3223_ =
                                                                        lean_string_dec_eq(
                                                                            v_x_3189_,
                                                                            v___x_3222_,
                                                                        );
                                                                    if v___x_3223_ == 0 {
                                                                        let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3225_: u8 = 0;
                                                                        v___x_3224_ = l_Std_Http_Method_ofString_x3f___closed__17;
                                                                        v___x_3225_ =
                                                                            lean_string_dec_eq(
                                                                                v_x_3189_,
                                                                                v___x_3224_,
                                                                            );
                                                                        if v___x_3225_ == 0 {
                                                                            let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3227_: u8 = 0;
                                                                            v___x_3226_ = l_Std_Http_Method_ofString_x3f___closed__18;
                                                                            v___x_3227_ =
                                                                                lean_string_dec_eq(
                                                                                    v_x_3189_,
                                                                                    v___x_3226_,
                                                                                );
                                                                            if v___x_3227_ == 0 {
                                                                                let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3229_: u8 = 0;
                                                                                v___x_3228_ = l_Std_Http_Method_ofString_x3f___closed__19;
                                                                                v___x_3229_ = lean_string_dec_eq(v_x_3189_, v___x_3228_);
                                                                                if v___x_3229_ == 0
                                                                                {
                                                                                    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3231_: u8 = 0;
                                                                                    v___x_3230_ = l_Std_Http_Method_ofString_x3f___closed__20;
                                                                                    v___x_3231_ = lean_string_dec_eq(v_x_3189_, v___x_3230_);
                                                                                    if v___x_3231_
                                                                                        == 0
                                                                                    {
                                                                                        let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3233_: u8 = 0;
                                                                                        v___x_3232_ = l_Std_Http_Method_ofString_x3f___closed__21;
                                                                                        v___x_3233_ = lean_string_dec_eq(v_x_3189_, v___x_3232_);
                                                                                        if v___x_3233_ == 0 {
let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3235_: u8 = 0;
v___x_3234_ = l_Std_Http_Method_ofString_x3f___closed__22;
v___x_3235_ = lean_string_dec_eq(v_x_3189_, v___x_3234_);
if v___x_3235_ == 0 {
let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3237_: u8 = 0;
v___x_3236_ = l_Std_Http_Method_ofString_x3f___closed__23;
v___x_3237_ = lean_string_dec_eq(v_x_3189_, v___x_3236_);
if v___x_3237_ == 0 {
let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3239_: u8 = 0;
v___x_3238_ = l_Std_Http_Method_ofString_x3f___closed__24;
v___x_3239_ = lean_string_dec_eq(v_x_3189_, v___x_3238_);
if v___x_3239_ == 0 {
let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3241_: u8 = 0;
v___x_3240_ = l_Std_Http_Method_ofString_x3f___closed__25;
v___x_3241_ = lean_string_dec_eq(v_x_3189_, v___x_3240_);
if v___x_3241_ == 0 {
let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3243_: u8 = 0;
v___x_3242_ = l_Std_Http_Method_ofString_x3f___closed__26;
v___x_3243_ = lean_string_dec_eq(v_x_3189_, v___x_3242_);
if v___x_3243_ == 0 {
let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3245_: u8 = 0;
v___x_3244_ = l_Std_Http_Method_ofString_x3f___closed__27;
v___x_3245_ = lean_string_dec_eq(v_x_3189_, v___x_3244_);
if v___x_3245_ == 0 {
let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3247_: u8 = 0;
v___x_3246_ = l_Std_Http_Method_ofString_x3f___closed__28;
v___x_3247_ = lean_string_dec_eq(v_x_3189_, v___x_3246_);
if v___x_3247_ == 0 {
let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3249_: u8 = 0;
v___x_3248_ = l_Std_Http_Method_ofString_x3f___closed__29;
v___x_3249_ = lean_string_dec_eq(v_x_3189_, v___x_3248_);
if v___x_3249_ == 0 {
let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3251_: u8 = 0;
v___x_3250_ = l_Std_Http_Method_ofString_x3f___closed__30;
v___x_3251_ = lean_string_dec_eq(v_x_3189_, v___x_3250_);
if v___x_3251_ == 0 {
let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3253_: u8 = 0;
v___x_3252_ = l_Std_Http_Method_ofString_x3f___closed__31;
v___x_3253_ = lean_string_dec_eq(v_x_3189_, v___x_3252_);
if v___x_3253_ == 0 {
let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3255_: u8 = 0;
v___x_3254_ = l_Std_Http_Method_ofString_x3f___closed__32;
v___x_3255_ = lean_string_dec_eq(v_x_3189_, v___x_3254_);
if v___x_3255_ == 0 {
let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3257_: u8 = 0;
v___x_3256_ = l_Std_Http_Method_ofString_x3f___closed__33;
v___x_3257_ = lean_string_dec_eq(v_x_3189_, v___x_3256_);
if v___x_3257_ == 0 {
let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3259_: u8 = 0;
v___x_3258_ = l_Std_Http_Method_ofString_x3f___closed__34;
v___x_3259_ = lean_string_dec_eq(v_x_3189_, v___x_3258_);
if v___x_3259_ == 0 {
let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3261_: u8 = 0;
v___x_3260_ = l_Std_Http_Method_ofString_x3f___closed__35;
v___x_3261_ = lean_string_dec_eq(v_x_3189_, v___x_3260_);
if v___x_3261_ == 0 {
let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3263_: u8 = 0;
v___x_3262_ = l_Std_Http_Method_ofString_x3f___closed__36;
v___x_3263_ = lean_string_dec_eq(v_x_3189_, v___x_3262_);
if v___x_3263_ == 0 {
let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3265_: u8 = 0;
v___x_3264_ = l_Std_Http_Method_ofString_x3f___closed__37;
v___x_3265_ = lean_string_dec_eq(v_x_3189_, v___x_3264_);
if v___x_3265_ == 0 {
let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3267_: u8 = 0;
v___x_3266_ = l_Std_Http_Method_ofString_x3f___closed__38;
v___x_3267_ = lean_string_dec_eq(v_x_3189_, v___x_3266_);
if v___x_3267_ == 0 {
let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3269_: u8 = 0;
v___x_3268_ = l_Std_Http_Method_ofString_x3f___closed__39;
v___x_3269_ = lean_string_dec_eq(v_x_3189_, v___x_3268_);
if v___x_3269_ == 0 {
let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3270_ = crate::leanh::lean_box(0);
return v___x_3270_;
} else {
let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3271_ = l_Std_Http_Method_ofString_x3f___closed__40;
return v___x_3271_;
}
} else {
let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3272_ = l_Std_Http_Method_ofString_x3f___closed__41;
return v___x_3272_;
}
} else {
let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3273_ = l_Std_Http_Method_ofString_x3f___closed__42;
return v___x_3273_;
}
} else {
let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3274_ = l_Std_Http_Method_ofString_x3f___closed__43;
return v___x_3274_;
}
} else {
let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3275_ = l_Std_Http_Method_ofString_x3f___closed__44;
return v___x_3275_;
}
} else {
let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3276_ = l_Std_Http_Method_ofString_x3f___closed__45;
return v___x_3276_;
}
} else {
let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3277_ = l_Std_Http_Method_ofString_x3f___closed__46;
return v___x_3277_;
}
} else {
let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3278_ = l_Std_Http_Method_ofString_x3f___closed__47;
return v___x_3278_;
}
} else {
let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3279_ = l_Std_Http_Method_ofString_x3f___closed__48;
return v___x_3279_;
}
} else {
let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3280_ = l_Std_Http_Method_ofString_x3f___closed__49;
return v___x_3280_;
}
} else {
let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3281_ = l_Std_Http_Method_ofString_x3f___closed__50;
return v___x_3281_;
}
} else {
let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3282_ = l_Std_Http_Method_ofString_x3f___closed__51;
return v___x_3282_;
}
} else {
let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3283_ = l_Std_Http_Method_ofString_x3f___closed__52;
return v___x_3283_;
}
} else {
let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3284_ = l_Std_Http_Method_ofString_x3f___closed__53;
return v___x_3284_;
}
} else {
let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3285_ = l_Std_Http_Method_ofString_x3f___closed__54;
return v___x_3285_;
}
} else {
let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3286_ = l_Std_Http_Method_ofString_x3f___closed__55;
return v___x_3286_;
}
} else {
let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3287_ = l_Std_Http_Method_ofString_x3f___closed__56;
return v___x_3287_;
}
} else {
let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3288_ = l_Std_Http_Method_ofString_x3f___closed__57;
return v___x_3288_;
}
} else {
let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v___x_3289_ = l_Std_Http_Method_ofString_x3f___closed__58;
return v___x_3289_;
}
                                                                                    } else {
                                                                                        let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                        v___x_3290_ = l_Std_Http_Method_ofString_x3f___closed__59;
                                                                                        return v___x_3290_;
                                                                                    }
                                                                                } else {
                                                                                    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                    v___x_3291_ = l_Std_Http_Method_ofString_x3f___closed__60;
                                                                                    return v___x_3291_;
                                                                                }
                                                                            } else {
                                                                                let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                                v___x_3292_ = l_Std_Http_Method_ofString_x3f___closed__61;
                                                                                return v___x_3292_;
                                                                            }
                                                                        } else {
                                                                            let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                            v___x_3293_ = l_Std_Http_Method_ofString_x3f___closed__62;
                                                                            return v___x_3293_;
                                                                        }
                                                                    } else {
                                                                        let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                        v___x_3294_ = l_Std_Http_Method_ofString_x3f___closed__63;
                                                                        return v___x_3294_;
                                                                    }
                                                                } else {
                                                                    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    v___x_3295_ = l_Std_Http_Method_ofString_x3f___closed__64;
                                                                    return v___x_3295_;
                                                                }
                                                            } else {
                                                                let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                v___x_3296_ = l_Std_Http_Method_ofString_x3f___closed__65;
                                                                return v___x_3296_;
                                                            }
                                                        } else {
                                                            let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            v___x_3297_ = l_Std_Http_Method_ofString_x3f___closed__66;
                                                            return v___x_3297_;
                                                        }
                                                    } else {
                                                        let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        v___x_3298_ = l_Std_Http_Method_ofString_x3f___closed__67;
                                                        return v___x_3298_;
                                                    }
                                                } else {
                                                    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    v___x_3299_ =
                                                        l_Std_Http_Method_ofString_x3f___closed__68;
                                                    return v___x_3299_;
                                                }
                                            } else {
                                                let mut v___x_3300_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_3300_ =
                                                    l_Std_Http_Method_ofString_x3f___closed__69;
                                                return v___x_3300_;
                                            }
                                        } else {
                                            let mut v___x_3301_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_3301_ =
                                                l_Std_Http_Method_ofString_x3f___closed__70;
                                            return v___x_3301_;
                                        }
                                    } else {
                                        let mut v___x_3302_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v___x_3302_ = l_Std_Http_Method_ofString_x3f___closed__71;
                                        return v___x_3302_;
                                    }
                                } else {
                                    let mut v___x_3303_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_3303_ = l_Std_Http_Method_ofString_x3f___closed__72;
                                    return v___x_3303_;
                                }
                            } else {
                                let mut v___x_3304_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_3304_ = l_Std_Http_Method_ofString_x3f___closed__73;
                                return v___x_3304_;
                            }
                        } else {
                            let mut v___x_3305_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3305_ = l_Std_Http_Method_ofString_x3f___closed__74;
                            return v___x_3305_;
                        }
                    } else {
                        let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_3306_ = l_Std_Http_Method_ofString_x3f___closed__75;
                        return v___x_3306_;
                    }
                } else {
                    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3307_ = l_Std_Http_Method_ofString_x3f___closed__76;
                    return v___x_3307_;
                }
            } else {
                let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3308_ = l_Std_Http_Method_ofString_x3f___closed__77;
                return v___x_3308_;
            }
        } else {
            let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3309_ = l_Std_Http_Method_ofString_x3f___closed__78;
            return v___x_3309_;
        }
    } else {
        let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3310_ = l_Std_Http_Method_ofString_x3f___closed__79;
        return v___x_3310_;
    }
}
pub unsafe fn l_Std_Http_Method_ofString_x3f___boxed(
    mut v_x_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Std_Http_Method_ofString_x3f(v_x_3311_);
    crate::leanh::lean_dec_ref(v_x_3311_);
    return v_res_3312_;
}
pub unsafe fn l_panic___at___00Std_Http_Method_ofString_x21_spec__0(
    mut v_msg_3313_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    v___x_3314_ = 0;
    v___x_3315_ = crate::leanh::lean_box((v___x_3314_) as usize);
    v___x_3316_ = lean_panic_fn_borrowed(v___x_3315_, v_msg_3313_);
    crate::leanh::lean_dec(v___x_3315_);
    v___x_3317_ = (crate::leanh::lean_unbox(v___x_3316_) as u8);
    crate::leanh::lean_dec(v___x_3316_);
    return v___x_3317_;
}
pub unsafe fn l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(
    mut v_msg_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3319_: u8 = 0;
    let mut v_r_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_3318_);
    v_r_3320_ = crate::leanh::lean_box((v_res_3319_) as usize);
    return v_r_3320_;
}
pub unsafe fn l_Std_Http_Method_ofString_x21(mut v_s_3324_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3325_ = l_Std_Http_Method_ofString_x3f(v_s_3324_);
    if crate::leanh::lean_obj_tag(v___x_3325_) == 0 {
        let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3334_: u8 = 0;
        v___x_3326_ = l_Std_Http_Method_ofString_x21___closed__0;
        v___x_3327_ = l_Std_Http_Method_ofString_x21___closed__1;
        v___x_3328_ = crate::leanh::lean_unsigned_to_nat(337);
        v___x_3329_ = crate::leanh::lean_unsigned_to_nat(12);
        v___x_3330_ = l_Std_Http_Method_ofString_x21___closed__2;
        v___x_3331_ = l_String_quote(v_s_3324_);
        v___x_3332_ = lean_string_append(v___x_3330_, v___x_3331_);
        crate::leanh::lean_dec_ref(v___x_3331_);
        v___x_3333_ = l_mkPanicMessageWithDecl(
            v___x_3326_,
            v___x_3327_,
            v___x_3328_,
            v___x_3329_,
            v___x_3332_,
        );
        crate::leanh::lean_dec_ref(v___x_3332_);
        v___x_3334_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v___x_3333_);
        return v___x_3334_;
    } else {
        let mut v_val_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3336_: u8 = 0;
        crate::leanh::lean_dec_ref(v_s_3324_);
        v_val_3335_ = crate::leanh::lean_ctor_get(v___x_3325_, 0);
        crate::leanh::lean_inc(v_val_3335_);
        crate::leanh::lean_dec_ref_known(v___x_3325_, 1);
        v___x_3336_ = (crate::leanh::lean_unbox(v_val_3335_) as u8);
        crate::leanh::lean_dec(v_val_3335_);
        return v___x_3336_;
    }
}
pub unsafe fn l_Std_Http_Method_ofString_x21___boxed(
    mut v_s_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: u8 = 0;
    let mut v_r_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_Std_Http_Method_ofString_x21(v_s_3337_);
    v_r_3339_ = crate::leanh::lean_box((v_res_3338_) as usize);
    return v_r_3339_;
}
pub unsafe fn l_Std_Http_Method_instToString___lam__0(
    mut v_x_3340_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3340_ {
        0 => {
            let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3341_ = l_Std_Http_Method_ofString_x3f___closed__0;
            return v___x_3341_;
        }
        1 => {
            let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3342_ = l_Std_Http_Method_ofString_x3f___closed__1;
            return v___x_3342_;
        }
        2 => {
            let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3343_ = l_Std_Http_Method_ofString_x3f___closed__2;
            return v___x_3343_;
        }
        3 => {
            let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3344_ = l_Std_Http_Method_ofString_x3f___closed__3;
            return v___x_3344_;
        }
        4 => {
            let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3345_ = l_Std_Http_Method_ofString_x3f___closed__4;
            return v___x_3345_;
        }
        5 => {
            let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3346_ = l_Std_Http_Method_ofString_x3f___closed__5;
            return v___x_3346_;
        }
        6 => {
            let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3347_ = l_Std_Http_Method_ofString_x3f___closed__6;
            return v___x_3347_;
        }
        7 => {
            let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3348_ = l_Std_Http_Method_ofString_x3f___closed__7;
            return v___x_3348_;
        }
        8 => {
            let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3349_ = l_Std_Http_Method_ofString_x3f___closed__8;
            return v___x_3349_;
        }
        9 => {
            let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3350_ = l_Std_Http_Method_ofString_x3f___closed__9;
            return v___x_3350_;
        }
        10 => {
            let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3351_ = l_Std_Http_Method_ofString_x3f___closed__10;
            return v___x_3351_;
        }
        11 => {
            let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3352_ = l_Std_Http_Method_ofString_x3f___closed__11;
            return v___x_3352_;
        }
        12 => {
            let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3353_ = l_Std_Http_Method_ofString_x3f___closed__12;
            return v___x_3353_;
        }
        13 => {
            let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3354_ = l_Std_Http_Method_ofString_x3f___closed__13;
            return v___x_3354_;
        }
        14 => {
            let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3355_ = l_Std_Http_Method_ofString_x3f___closed__14;
            return v___x_3355_;
        }
        15 => {
            let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3356_ = l_Std_Http_Method_ofString_x3f___closed__15;
            return v___x_3356_;
        }
        16 => {
            let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3357_ = l_Std_Http_Method_ofString_x3f___closed__16;
            return v___x_3357_;
        }
        17 => {
            let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3358_ = l_Std_Http_Method_ofString_x3f___closed__17;
            return v___x_3358_;
        }
        18 => {
            let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3359_ = l_Std_Http_Method_ofString_x3f___closed__18;
            return v___x_3359_;
        }
        19 => {
            let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3360_ = l_Std_Http_Method_ofString_x3f___closed__19;
            return v___x_3360_;
        }
        20 => {
            let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3361_ = l_Std_Http_Method_ofString_x3f___closed__20;
            return v___x_3361_;
        }
        21 => {
            let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3362_ = l_Std_Http_Method_ofString_x3f___closed__21;
            return v___x_3362_;
        }
        22 => {
            let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3363_ = l_Std_Http_Method_ofString_x3f___closed__22;
            return v___x_3363_;
        }
        23 => {
            let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3364_ = l_Std_Http_Method_ofString_x3f___closed__23;
            return v___x_3364_;
        }
        24 => {
            let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3365_ = l_Std_Http_Method_ofString_x3f___closed__24;
            return v___x_3365_;
        }
        25 => {
            let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3366_ = l_Std_Http_Method_ofString_x3f___closed__25;
            return v___x_3366_;
        }
        26 => {
            let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3367_ = l_Std_Http_Method_ofString_x3f___closed__26;
            return v___x_3367_;
        }
        27 => {
            let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3368_ = l_Std_Http_Method_ofString_x3f___closed__27;
            return v___x_3368_;
        }
        28 => {
            let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3369_ = l_Std_Http_Method_ofString_x3f___closed__28;
            return v___x_3369_;
        }
        29 => {
            let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3370_ = l_Std_Http_Method_ofString_x3f___closed__29;
            return v___x_3370_;
        }
        30 => {
            let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3371_ = l_Std_Http_Method_ofString_x3f___closed__30;
            return v___x_3371_;
        }
        31 => {
            let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3372_ = l_Std_Http_Method_ofString_x3f___closed__31;
            return v___x_3372_;
        }
        32 => {
            let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3373_ = l_Std_Http_Method_ofString_x3f___closed__32;
            return v___x_3373_;
        }
        33 => {
            let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3374_ = l_Std_Http_Method_ofString_x3f___closed__33;
            return v___x_3374_;
        }
        34 => {
            let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3375_ = l_Std_Http_Method_ofString_x3f___closed__34;
            return v___x_3375_;
        }
        35 => {
            let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3376_ = l_Std_Http_Method_ofString_x3f___closed__35;
            return v___x_3376_;
        }
        36 => {
            let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3377_ = l_Std_Http_Method_ofString_x3f___closed__36;
            return v___x_3377_;
        }
        37 => {
            let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3378_ = l_Std_Http_Method_ofString_x3f___closed__37;
            return v___x_3378_;
        }
        38 => {
            let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3379_ = l_Std_Http_Method_ofString_x3f___closed__38;
            return v___x_3379_;
        }
        _ => {
            let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3380_ = l_Std_Http_Method_ofString_x3f___closed__39;
            return v___x_3380_;
        }
    }
}
pub unsafe fn l_Std_Http_Method_instToString___lam__0___boxed(
    mut v_x_3381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_366__boxed_3382_: u8 = 0;
    let mut v_res_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_366__boxed_3382_ = (crate::leanh::lean_unbox(v_x_3381_) as u8);
    v_res_3383_ = l_Std_Http_Method_instToString___lam__0(v_x_366__boxed_3382_);
    return v_res_3383_;
}
pub unsafe fn l_Std_Http_Method_instEncodeV11___lam__0(
    mut v_buffer_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v___y_3387_ {
                0 => {
                    v___x_3403_ = l_Std_Http_Method_ofString_x3f___closed__0;
                    v___y_3389_ = v___x_3403_;
                    state = 1;
                    continue;
                }
                1 => {
                    v___x_3404_ = l_Std_Http_Method_ofString_x3f___closed__1;
                    v___y_3389_ = v___x_3404_;
                    state = 1;
                    continue;
                }
                2 => {
                    v___x_3405_ = l_Std_Http_Method_ofString_x3f___closed__2;
                    v___y_3389_ = v___x_3405_;
                    state = 1;
                    continue;
                }
                3 => {
                    v___x_3406_ = l_Std_Http_Method_ofString_x3f___closed__3;
                    v___y_3389_ = v___x_3406_;
                    state = 1;
                    continue;
                }
                4 => {
                    v___x_3407_ = l_Std_Http_Method_ofString_x3f___closed__4;
                    v___y_3389_ = v___x_3407_;
                    state = 1;
                    continue;
                }
                5 => {
                    v___x_3408_ = l_Std_Http_Method_ofString_x3f___closed__5;
                    v___y_3389_ = v___x_3408_;
                    state = 1;
                    continue;
                }
                6 => {
                    v___x_3409_ = l_Std_Http_Method_ofString_x3f___closed__6;
                    v___y_3389_ = v___x_3409_;
                    state = 1;
                    continue;
                }
                7 => {
                    v___x_3410_ = l_Std_Http_Method_ofString_x3f___closed__7;
                    v___y_3389_ = v___x_3410_;
                    state = 1;
                    continue;
                }
                8 => {
                    v___x_3411_ = l_Std_Http_Method_ofString_x3f___closed__8;
                    v___y_3389_ = v___x_3411_;
                    state = 1;
                    continue;
                }
                9 => {
                    v___x_3412_ = l_Std_Http_Method_ofString_x3f___closed__9;
                    v___y_3389_ = v___x_3412_;
                    state = 1;
                    continue;
                }
                10 => {
                    v___x_3413_ = l_Std_Http_Method_ofString_x3f___closed__10;
                    v___y_3389_ = v___x_3413_;
                    state = 1;
                    continue;
                }
                11 => {
                    v___x_3414_ = l_Std_Http_Method_ofString_x3f___closed__11;
                    v___y_3389_ = v___x_3414_;
                    state = 1;
                    continue;
                }
                12 => {
                    v___x_3415_ = l_Std_Http_Method_ofString_x3f___closed__12;
                    v___y_3389_ = v___x_3415_;
                    state = 1;
                    continue;
                }
                13 => {
                    v___x_3416_ = l_Std_Http_Method_ofString_x3f___closed__13;
                    v___y_3389_ = v___x_3416_;
                    state = 1;
                    continue;
                }
                14 => {
                    v___x_3417_ = l_Std_Http_Method_ofString_x3f___closed__14;
                    v___y_3389_ = v___x_3417_;
                    state = 1;
                    continue;
                }
                15 => {
                    v___x_3418_ = l_Std_Http_Method_ofString_x3f___closed__15;
                    v___y_3389_ = v___x_3418_;
                    state = 1;
                    continue;
                }
                16 => {
                    v___x_3419_ = l_Std_Http_Method_ofString_x3f___closed__16;
                    v___y_3389_ = v___x_3419_;
                    state = 1;
                    continue;
                }
                17 => {
                    v___x_3420_ = l_Std_Http_Method_ofString_x3f___closed__17;
                    v___y_3389_ = v___x_3420_;
                    state = 1;
                    continue;
                }
                18 => {
                    v___x_3421_ = l_Std_Http_Method_ofString_x3f___closed__18;
                    v___y_3389_ = v___x_3421_;
                    state = 1;
                    continue;
                }
                19 => {
                    v___x_3422_ = l_Std_Http_Method_ofString_x3f___closed__19;
                    v___y_3389_ = v___x_3422_;
                    state = 1;
                    continue;
                }
                20 => {
                    v___x_3423_ = l_Std_Http_Method_ofString_x3f___closed__20;
                    v___y_3389_ = v___x_3423_;
                    state = 1;
                    continue;
                }
                21 => {
                    v___x_3424_ = l_Std_Http_Method_ofString_x3f___closed__21;
                    v___y_3389_ = v___x_3424_;
                    state = 1;
                    continue;
                }
                22 => {
                    v___x_3425_ = l_Std_Http_Method_ofString_x3f___closed__22;
                    v___y_3389_ = v___x_3425_;
                    state = 1;
                    continue;
                }
                23 => {
                    v___x_3426_ = l_Std_Http_Method_ofString_x3f___closed__23;
                    v___y_3389_ = v___x_3426_;
                    state = 1;
                    continue;
                }
                24 => {
                    v___x_3427_ = l_Std_Http_Method_ofString_x3f___closed__24;
                    v___y_3389_ = v___x_3427_;
                    state = 1;
                    continue;
                }
                25 => {
                    v___x_3428_ = l_Std_Http_Method_ofString_x3f___closed__25;
                    v___y_3389_ = v___x_3428_;
                    state = 1;
                    continue;
                }
                26 => {
                    v___x_3429_ = l_Std_Http_Method_ofString_x3f___closed__26;
                    v___y_3389_ = v___x_3429_;
                    state = 1;
                    continue;
                }
                27 => {
                    v___x_3430_ = l_Std_Http_Method_ofString_x3f___closed__27;
                    v___y_3389_ = v___x_3430_;
                    state = 1;
                    continue;
                }
                28 => {
                    v___x_3431_ = l_Std_Http_Method_ofString_x3f___closed__28;
                    v___y_3389_ = v___x_3431_;
                    state = 1;
                    continue;
                }
                29 => {
                    v___x_3432_ = l_Std_Http_Method_ofString_x3f___closed__29;
                    v___y_3389_ = v___x_3432_;
                    state = 1;
                    continue;
                }
                30 => {
                    v___x_3433_ = l_Std_Http_Method_ofString_x3f___closed__30;
                    v___y_3389_ = v___x_3433_;
                    state = 1;
                    continue;
                }
                31 => {
                    v___x_3434_ = l_Std_Http_Method_ofString_x3f___closed__31;
                    v___y_3389_ = v___x_3434_;
                    state = 1;
                    continue;
                }
                32 => {
                    v___x_3435_ = l_Std_Http_Method_ofString_x3f___closed__32;
                    v___y_3389_ = v___x_3435_;
                    state = 1;
                    continue;
                }
                33 => {
                    v___x_3436_ = l_Std_Http_Method_ofString_x3f___closed__33;
                    v___y_3389_ = v___x_3436_;
                    state = 1;
                    continue;
                }
                34 => {
                    v___x_3437_ = l_Std_Http_Method_ofString_x3f___closed__34;
                    v___y_3389_ = v___x_3437_;
                    state = 1;
                    continue;
                }
                35 => {
                    v___x_3438_ = l_Std_Http_Method_ofString_x3f___closed__35;
                    v___y_3389_ = v___x_3438_;
                    state = 1;
                    continue;
                }
                36 => {
                    v___x_3439_ = l_Std_Http_Method_ofString_x3f___closed__36;
                    v___y_3389_ = v___x_3439_;
                    state = 1;
                    continue;
                }
                37 => {
                    v___x_3440_ = l_Std_Http_Method_ofString_x3f___closed__37;
                    v___y_3389_ = v___x_3440_;
                    state = 1;
                    continue;
                }
                38 => {
                    v___x_3441_ = l_Std_Http_Method_ofString_x3f___closed__38;
                    v___y_3389_ = v___x_3441_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___x_3442_ = l_Std_Http_Method_ofString_x3f___closed__39;
                    v___y_3389_ = v___x_3442_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v_data_3390_ = crate::leanh::lean_ctor_get(v_buffer_3386_, 0);
                v_size_3391_ = crate::leanh::lean_ctor_get(v_buffer_3386_, 1);
                v_isSharedCheck_3402_ = (!crate::leanh::lean_is_exclusive(v_buffer_3386_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v___x_3393_ = v_buffer_3386_;
                    v_isShared_3394_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_3391_);
                    crate::leanh::lean_inc(v_data_3390_);
                    crate::leanh::lean_dec(v_buffer_3386_);
                    v___x_3393_ = crate::leanh::lean_box(0);
                    v_isShared_3394_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3395_ = lean_string_to_utf8(v___y_3389_);
                crate::leanh::lean_inc_ref(v___x_3395_);
                v___x_3396_ = lean_array_push(v_data_3390_, v___x_3395_);
                v___x_3397_ = lean_byte_array_size(v___x_3395_);
                crate::leanh::lean_dec_ref(v___x_3395_);
                v___x_3398_ = lean_nat_add(v_size_3391_, v___x_3397_);
                crate::leanh::lean_dec(v_size_3391_);
                if v_isShared_3394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3393_, 1, v___x_3398_);
                    crate::leanh::lean_ctor_set(v___x_3393_, 0, v___x_3396_);
                    v___x_3400_ = v___x_3393_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___x_3398_);
                    v___x_3400_ = v_reuseFailAlloc_3401_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Method_instEncodeV11___lam__0___boxed(
    mut v_buffer_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_192__boxed_3445_: u8 = 0;
    let mut v_res_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_192__boxed_3445_ = (crate::leanh::lean_unbox(v___y_3444_) as u8);
    v_res_3446_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_3443_, v___y_192__boxed_3445_);
    return v_res_3446_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Method(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_instInhabitedMethod_default = _init_l_Std_Http_instInhabitedMethod_default();
    l_Std_Http_instInhabitedMethod = _init_l_Std_Http_instInhabitedMethod();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Method(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Method(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Method(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Method(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Method(builtin);
}
