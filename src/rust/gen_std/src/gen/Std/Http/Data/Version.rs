// Lean compiler output
// Module: Std.Http.Data.Version
// Imports: Init.Data.ToString Init.Data.String.Basic
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_panic_fn_borrowed, lean_string_dec_eq,
};
pub static l_Std_Http_instReprVersion_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 49,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__2_value: crate::leanh::LeanStringObject<21> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 49,
            49, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__4_value: crate::leanh::LeanStringObject<21> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 50,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__6_value: crate::leanh::LeanStringObject<21> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 51,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_instReprVersion_repr___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprVersion_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_instReprVersion_repr___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprVersion_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprVersion___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprVersion_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprVersion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instReprVersion: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedVersion_default: u8 = 0;
pub static mut l_Std_Http_instInhabitedVersion: u8 = 0;
pub static l_Std_Http_instBEqVersion___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instBEqVersion_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instBEqVersion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqVersion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instBEqVersion: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqVersion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Version_ofNumber_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Version_ofNumber_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__2_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Version_ofNumber_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Version_ofNumber_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [72, 84, 84, 80, 47, 49, 46, 48, 0],
    };
static mut l_Std_Http_Version_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [72, 84, 84, 80, 47, 49, 46, 49, 0],
    };
static mut l_Std_Http_Version_ofString_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [72, 84, 84, 80, 47, 50, 46, 48, 0],
    };
static mut l_Std_Http_Version_ofString_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__3_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [72, 84, 84, 80, 47, 51, 46, 48, 0],
    };
static mut l_Std_Http_Version_ofString_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__0_value: crate::leanh::LeanStringObject<22> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 86, 101, 114, 115, 105,
            111, 110, 0,
        ],
    };
static mut l_Std_Http_Version_ofString_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__1_value: crate::leanh::LeanStringObject<27> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 111,
            102, 83, 116, 114, 105, 110, 103, 33, 0,
        ],
    };
static mut l_Std_Http_Version_ofString_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__2_value: crate::leanh::LeanStringObject<23> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 72, 84, 84, 80, 32, 118, 101, 114, 115, 105, 111,
            110, 58, 32, 0,
        ],
    };
static mut l_Std_Http_Version_ofString_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Version_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Version_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Version_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Version_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Version_ctorIdx(mut v_x_303_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_303_ {
        0 => {
            let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_304_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_304_;
        }
        1 => {
            let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_305_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_305_;
        }
        2 => {
            let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_306_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_306_;
        }
        _ => {
            let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_307_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_307_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_ctorIdx___boxed(
    mut v_x_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_309_: u8 = 0;
    let mut v_res_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_309_ = (crate::leanh::lean_unbox(v_x_308_) as u8);
    v_res_310_ = l_Std_Http_Version_ctorIdx(v_x_boxed_309_);
    return v_res_310_;
}
pub unsafe fn l_Std_Http_Version_toCtorIdx(mut v_x_311_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Std_Http_Version_ctorIdx(v_x_311_);
    return v___x_312_;
}
pub unsafe fn l_Std_Http_Version_toCtorIdx___boxed(
    mut v_x_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_314_: u8 = 0;
    let mut v_res_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_314_ = (crate::leanh::lean_unbox(v_x_313_) as u8);
    v_res_315_ = l_Std_Http_Version_toCtorIdx(v_x_4__boxed_314_);
    return v_res_315_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___redArg(
    mut v_k_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_316_);
    return v_k_316_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___redArg___boxed(
    mut v_k_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Http_Version_ctorElim___redArg(v_k_317_);
    crate::leanh::lean_dec(v_k_317_);
    return v_res_318_;
}
pub unsafe fn l_Std_Http_Version_ctorElim(
    mut v_motive_319_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_320_: *mut crate::leanh::LeanObject,
    mut v_t_321_: u8,
    mut v_h_322_: *mut crate::leanh::LeanObject,
    mut v_k_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_323_);
    return v_k_323_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___boxed(
    mut v_motive_324_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_325_: *mut crate::leanh::LeanObject,
    mut v_t_326_: *mut crate::leanh::LeanObject,
    mut v_h_327_: *mut crate::leanh::LeanObject,
    mut v_k_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_329_: u8 = 0;
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_329_ = (crate::leanh::lean_unbox(v_t_326_) as u8);
    v_res_330_ = l_Std_Http_Version_ctorElim(
        v_motive_324_,
        v_ctorIdx_325_,
        v_t_boxed_329_,
        v_h_327_,
        v_k_328_,
    );
    crate::leanh::lean_dec(v_k_328_);
    crate::leanh::lean_dec(v_ctorIdx_325_);
    return v_res_330_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___redArg(
    mut v_v10_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v10_331_);
    return v_v10_331_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___redArg___boxed(
    mut v_v10_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_333_ = l_Std_Http_Version_v10_elim___redArg(v_v10_332_);
    crate::leanh::lean_dec(v_v10_332_);
    return v_res_333_;
}
pub unsafe fn l_Std_Http_Version_v10_elim(
    mut v_motive_334_: *mut crate::leanh::LeanObject,
    mut v_t_335_: u8,
    mut v_h_336_: *mut crate::leanh::LeanObject,
    mut v_v10_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v10_337_);
    return v_v10_337_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___boxed(
    mut v_motive_338_: *mut crate::leanh::LeanObject,
    mut v_t_339_: *mut crate::leanh::LeanObject,
    mut v_h_340_: *mut crate::leanh::LeanObject,
    mut v_v10_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_342_: u8 = 0;
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_342_ = (crate::leanh::lean_unbox(v_t_339_) as u8);
    v_res_343_ = l_Std_Http_Version_v10_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_v10_341_);
    crate::leanh::lean_dec(v_v10_341_);
    return v_res_343_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___redArg(
    mut v_v11_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v11_344_);
    return v_v11_344_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___redArg___boxed(
    mut v_v11_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l_Std_Http_Version_v11_elim___redArg(v_v11_345_);
    crate::leanh::lean_dec(v_v11_345_);
    return v_res_346_;
}
pub unsafe fn l_Std_Http_Version_v11_elim(
    mut v_motive_347_: *mut crate::leanh::LeanObject,
    mut v_t_348_: u8,
    mut v_h_349_: *mut crate::leanh::LeanObject,
    mut v_v11_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v11_350_);
    return v_v11_350_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___boxed(
    mut v_motive_351_: *mut crate::leanh::LeanObject,
    mut v_t_352_: *mut crate::leanh::LeanObject,
    mut v_h_353_: *mut crate::leanh::LeanObject,
    mut v_v11_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_355_: u8 = 0;
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_355_ = (crate::leanh::lean_unbox(v_t_352_) as u8);
    v_res_356_ = l_Std_Http_Version_v11_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_v11_354_);
    crate::leanh::lean_dec(v_v11_354_);
    return v_res_356_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___redArg(
    mut v_v20_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v20_357_);
    return v_v20_357_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___redArg___boxed(
    mut v_v20_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_Std_Http_Version_v20_elim___redArg(v_v20_358_);
    crate::leanh::lean_dec(v_v20_358_);
    return v_res_359_;
}
pub unsafe fn l_Std_Http_Version_v20_elim(
    mut v_motive_360_: *mut crate::leanh::LeanObject,
    mut v_t_361_: u8,
    mut v_h_362_: *mut crate::leanh::LeanObject,
    mut v_v20_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v20_363_);
    return v_v20_363_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___boxed(
    mut v_motive_364_: *mut crate::leanh::LeanObject,
    mut v_t_365_: *mut crate::leanh::LeanObject,
    mut v_h_366_: *mut crate::leanh::LeanObject,
    mut v_v20_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_368_: u8 = 0;
    let mut v_res_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_368_ = (crate::leanh::lean_unbox(v_t_365_) as u8);
    v_res_369_ = l_Std_Http_Version_v20_elim(v_motive_364_, v_t_boxed_368_, v_h_366_, v_v20_367_);
    crate::leanh::lean_dec(v_v20_367_);
    return v_res_369_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___redArg(
    mut v_v30_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v30_370_);
    return v_v30_370_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___redArg___boxed(
    mut v_v30_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Std_Http_Version_v30_elim___redArg(v_v30_371_);
    crate::leanh::lean_dec(v_v30_371_);
    return v_res_372_;
}
pub unsafe fn l_Std_Http_Version_v30_elim(
    mut v_motive_373_: *mut crate::leanh::LeanObject,
    mut v_t_374_: u8,
    mut v_h_375_: *mut crate::leanh::LeanObject,
    mut v_v30_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v30_376_);
    return v_v30_376_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___boxed(
    mut v_motive_377_: *mut crate::leanh::LeanObject,
    mut v_t_378_: *mut crate::leanh::LeanObject,
    mut v_h_379_: *mut crate::leanh::LeanObject,
    mut v_v30_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_381_: u8 = 0;
    let mut v_res_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_381_ = (crate::leanh::lean_unbox(v_t_378_) as u8);
    v_res_382_ = l_Std_Http_Version_v30_elim(v_motive_377_, v_t_boxed_381_, v_h_379_, v_v30_380_);
    crate::leanh::lean_dec(v_v30_380_);
    return v_res_382_;
}
pub unsafe fn _init_l_Std_Http_instReprVersion_repr___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_396_ = lean_nat_to_int(v___x_395_);
    return v___x_396_;
}
pub unsafe fn _init_l_Std_Http_instReprVersion_repr___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_398_ = lean_nat_to_int(v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_Std_Http_instReprVersion_repr(
    mut v_x_399_: u8,
    mut v_prec_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: u8 = 0;
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: u8 = 0;
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: u8 = 0;
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: u8 = 0;
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_399_ {
                0 => {
                    v___x_429_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_430_ = lean_nat_dec_le(v___x_429_, v_prec_400_);
                    if v___x_430_ == 0 {
                        v___x_431_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__8_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__8,
                        );
                        v___y_402_ = v___x_431_;
                        state = 1;
                        continue;
                    } else {
                        v___x_432_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__9_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__9,
                        );
                        v___y_402_ = v___x_432_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_433_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_434_ = lean_nat_dec_le(v___x_433_, v_prec_400_);
                    if v___x_434_ == 0 {
                        v___x_435_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__8_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__8,
                        );
                        v___y_409_ = v___x_435_;
                        state = 2;
                        continue;
                    } else {
                        v___x_436_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__9_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__9,
                        );
                        v___y_409_ = v___x_436_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_437_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_438_ = lean_nat_dec_le(v___x_437_, v_prec_400_);
                    if v___x_438_ == 0 {
                        v___x_439_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__8_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__8,
                        );
                        v___y_416_ = v___x_439_;
                        state = 3;
                        continue;
                    } else {
                        v___x_440_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__9_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__9,
                        );
                        v___y_416_ = v___x_440_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_441_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_442_ = lean_nat_dec_le(v___x_441_, v_prec_400_);
                    if v___x_442_ == 0 {
                        v___x_443_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__8_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__8,
                        );
                        v___y_423_ = v___x_443_;
                        state = 4;
                        continue;
                    } else {
                        v___x_444_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Http_instReprVersion_repr___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_instReprVersion_repr___closed__9_once
                            ),
                            _init_l_Std_Http_instReprVersion_repr___closed__9,
                        );
                        v___y_423_ = v___x_444_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_403_ = l_Std_Http_instReprVersion_repr___closed__1;
                crate::leanh::lean_inc(v___y_402_);
                v___x_404_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_404_, 0, v___y_402_);
                crate::leanh::lean_ctor_set(v___x_404_, 1, v___x_403_);
                v___x_405_ = 0;
                v___x_406_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_406_, 0, v___x_404_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_406_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_405_,
                );
                v___x_407_ = l_Repr_addAppParen(v___x_406_, v_prec_400_);
                return v___x_407_;
            }
            2 => {
                v___x_410_ = l_Std_Http_instReprVersion_repr___closed__3;
                crate::leanh::lean_inc(v___y_409_);
                v___x_411_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_411_, 0, v___y_409_);
                crate::leanh::lean_ctor_set(v___x_411_, 1, v___x_410_);
                v___x_412_ = 0;
                v___x_413_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_413_, 0, v___x_411_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_413_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_412_,
                );
                v___x_414_ = l_Repr_addAppParen(v___x_413_, v_prec_400_);
                return v___x_414_;
            }
            3 => {
                v___x_417_ = l_Std_Http_instReprVersion_repr___closed__5;
                crate::leanh::lean_inc(v___y_416_);
                v___x_418_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_418_, 0, v___y_416_);
                crate::leanh::lean_ctor_set(v___x_418_, 1, v___x_417_);
                v___x_419_ = 0;
                v___x_420_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_420_, 0, v___x_418_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_420_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_419_,
                );
                v___x_421_ = l_Repr_addAppParen(v___x_420_, v_prec_400_);
                return v___x_421_;
            }
            4 => {
                v___x_424_ = l_Std_Http_instReprVersion_repr___closed__7;
                crate::leanh::lean_inc(v___y_423_);
                v___x_425_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_425_, 0, v___y_423_);
                crate::leanh::lean_ctor_set(v___x_425_, 1, v___x_424_);
                v___x_426_ = 0;
                v___x_427_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_427_, 0, v___x_425_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_426_,
                );
                v___x_428_ = l_Repr_addAppParen(v___x_427_, v_prec_400_);
                return v___x_428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instReprVersion_repr___boxed(
    mut v_x_445_: *mut crate::leanh::LeanObject,
    mut v_prec_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_233__boxed_447_: u8 = 0;
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_447_ = (crate::leanh::lean_unbox(v_x_445_) as u8);
    v_res_448_ = l_Std_Http_instReprVersion_repr(v_x_233__boxed_447_, v_prec_446_);
    crate::leanh::lean_dec(v_prec_446_);
    return v_res_448_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedVersion_default() -> u8 {
    let mut v___x_451_: u8 = 0;
    v___x_451_ = 0;
    return v___x_451_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedVersion() -> u8 {
    let mut v___x_452_: u8 = 0;
    v___x_452_ = 0;
    return v___x_452_;
}
pub unsafe fn l_Std_Http_instBEqVersion_beq(mut v_x_453_: u8, mut v_y_454_: u8) -> u8 {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    v___x_455_ = l_Std_Http_Version_ctorIdx(v_x_453_);
    v___x_456_ = l_Std_Http_Version_ctorIdx(v_y_454_);
    v___x_457_ = lean_nat_dec_eq(v___x_455_, v___x_456_);
    crate::leanh::lean_dec(v___x_456_);
    crate::leanh::lean_dec(v___x_455_);
    return v___x_457_;
}
pub unsafe fn l_Std_Http_instBEqVersion_beq___boxed(
    mut v_x_458_: *mut crate::leanh::LeanObject,
    mut v_y_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_460_: u8 = 0;
    let mut v_y_18__boxed_461_: u8 = 0;
    let mut v_res_462_: u8 = 0;
    let mut v_r_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_460_ = (crate::leanh::lean_unbox(v_x_458_) as u8);
    v_y_18__boxed_461_ = (crate::leanh::lean_unbox(v_y_459_) as u8);
    v_res_462_ = l_Std_Http_instBEqVersion_beq(v_x_17__boxed_460_, v_y_18__boxed_461_);
    v_r_463_ = crate::leanh::lean_box((v_res_462_) as usize);
    return v_r_463_;
}
pub unsafe fn l_Std_Http_Version_ofNat(mut v_n_466_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    v___x_467_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_468_ = lean_nat_dec_le(v_n_466_, v___x_467_);
    if v___x_468_ == 0 {
        let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: u8 = 0;
        v___x_469_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_470_ = lean_nat_dec_le(v_n_466_, v___x_469_);
        if v___x_470_ == 0 {
            let mut v___x_471_: u8 = 0;
            v___x_471_ = 3;
            return v___x_471_;
        } else {
            let mut v___x_472_: u8 = 0;
            v___x_472_ = 2;
            return v___x_472_;
        }
    } else {
        let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: u8 = 0;
        v___x_473_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_474_ = lean_nat_dec_le(v_n_466_, v___x_473_);
        if v___x_474_ == 0 {
            let mut v___x_475_: u8 = 0;
            v___x_475_ = 1;
            return v___x_475_;
        } else {
            let mut v___x_476_: u8 = 0;
            v___x_476_ = 0;
            return v___x_476_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_ofNat___boxed(
    mut v_n_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Http_Version_ofNat(v_n_477_);
    crate::leanh::lean_dec(v_n_477_);
    v_r_479_ = crate::leanh::lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l_Std_Http_instDecidableEqVersion(mut v_x_480_: u8, mut v_y_481_: u8) -> u8 {
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    v___x_482_ = l_Std_Http_Version_ctorIdx(v_x_480_);
    v___x_483_ = l_Std_Http_Version_ctorIdx(v_y_481_);
    v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
    crate::leanh::lean_dec(v___x_483_);
    crate::leanh::lean_dec(v___x_482_);
    return v___x_484_;
}
pub unsafe fn l_Std_Http_instDecidableEqVersion___boxed(
    mut v_x_485_: *mut crate::leanh::LeanObject,
    mut v_y_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_487_: u8 = 0;
    let mut v_y_14__boxed_488_: u8 = 0;
    let mut v_res_489_: u8 = 0;
    let mut v_r_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_487_ = (crate::leanh::lean_unbox(v_x_485_) as u8);
    v_y_14__boxed_488_ = (crate::leanh::lean_unbox(v_y_486_) as u8);
    v_res_489_ = l_Std_Http_instDecidableEqVersion(v_x_13__boxed_487_, v_y_14__boxed_488_);
    v_r_490_ = crate::leanh::lean_box((v_res_489_) as usize);
    return v_r_490_;
}
pub unsafe fn l_Std_Http_Version_ofNumber_x3f(
    mut v_x_503_: *mut crate::leanh::LeanObject,
    mut v_x_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    v___x_505_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_506_ = lean_nat_dec_eq(v_x_503_, v___x_505_);
    if v___x_506_ == 0 {
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: u8 = 0;
        v___x_507_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_508_ = lean_nat_dec_eq(v_x_503_, v___x_507_);
        if v___x_508_ == 0 {
            let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_510_: u8 = 0;
            v___x_509_ = crate::leanh::lean_unsigned_to_nat(3);
            v___x_510_ = lean_nat_dec_eq(v_x_503_, v___x_509_);
            if v___x_510_ == 0 {
                let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_511_ = crate::leanh::lean_box(0);
                return v___x_511_;
            } else {
                let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_513_: u8 = 0;
                v___x_512_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_513_ = lean_nat_dec_eq(v_x_504_, v___x_512_);
                if v___x_513_ == 0 {
                    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_514_ = crate::leanh::lean_box(0);
                    return v___x_514_;
                } else {
                    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_515_ = l_Std_Http_Version_ofNumber_x3f___closed__0;
                    return v___x_515_;
                }
            }
        } else {
            let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_517_: u8 = 0;
            v___x_516_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_517_ = lean_nat_dec_eq(v_x_504_, v___x_516_);
            if v___x_517_ == 0 {
                let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_518_ = crate::leanh::lean_box(0);
                return v___x_518_;
            } else {
                let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_519_ = l_Std_Http_Version_ofNumber_x3f___closed__1;
                return v___x_519_;
            }
        }
    } else {
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: u8 = 0;
        v___x_520_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_521_ = lean_nat_dec_eq(v_x_504_, v___x_520_);
        if v___x_521_ == 0 {
            let mut v___x_522_: u8 = 0;
            v___x_522_ = lean_nat_dec_eq(v_x_504_, v___x_505_);
            if v___x_522_ == 0 {
                let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_523_ = crate::leanh::lean_box(0);
                return v___x_523_;
            } else {
                let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_524_ = l_Std_Http_Version_ofNumber_x3f___closed__2;
                return v___x_524_;
            }
        } else {
            let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_525_ = l_Std_Http_Version_ofNumber_x3f___closed__3;
            return v___x_525_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_ofNumber_x3f___boxed(
    mut v_x_526_: *mut crate::leanh::LeanObject,
    mut v_x_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Std_Http_Version_ofNumber_x3f(v_x_526_, v_x_527_);
    crate::leanh::lean_dec(v_x_527_);
    crate::leanh::lean_dec(v_x_526_);
    return v_res_528_;
}
pub unsafe fn l_Std_Http_Version_ofString_x3f(
    mut v_x_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_534_ = l_Std_Http_Version_ofString_x3f___closed__0;
    v___x_535_ = lean_string_dec_eq(v_x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: u8 = 0;
        v___x_536_ = l_Std_Http_Version_ofString_x3f___closed__1;
        v___x_537_ = lean_string_dec_eq(v_x_533_, v___x_536_);
        if v___x_537_ == 0 {
            let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_539_: u8 = 0;
            v___x_538_ = l_Std_Http_Version_ofString_x3f___closed__2;
            v___x_539_ = lean_string_dec_eq(v_x_533_, v___x_538_);
            if v___x_539_ == 0 {
                let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_541_: u8 = 0;
                v___x_540_ = l_Std_Http_Version_ofString_x3f___closed__3;
                v___x_541_ = lean_string_dec_eq(v_x_533_, v___x_540_);
                if v___x_541_ == 0 {
                    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_542_ = crate::leanh::lean_box(0);
                    return v___x_542_;
                } else {
                    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_543_ = l_Std_Http_Version_ofNumber_x3f___closed__0;
                    return v___x_543_;
                }
            } else {
                let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_544_ = l_Std_Http_Version_ofNumber_x3f___closed__1;
                return v___x_544_;
            }
        } else {
            let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_545_ = l_Std_Http_Version_ofNumber_x3f___closed__2;
            return v___x_545_;
        }
    } else {
        let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_546_ = l_Std_Http_Version_ofNumber_x3f___closed__3;
        return v___x_546_;
    }
}
pub unsafe fn l_Std_Http_Version_ofString_x3f___boxed(
    mut v_x_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_548_ = l_Std_Http_Version_ofString_x3f(v_x_547_);
    crate::leanh::lean_dec_ref(v_x_547_);
    return v_res_548_;
}
pub unsafe fn l_panic___at___00Std_Http_Version_ofString_x21_spec__0(
    mut v_msg_549_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    v___x_550_ = 0;
    v___x_551_ = crate::leanh::lean_box((v___x_550_) as usize);
    v___x_552_ = lean_panic_fn_borrowed(v___x_551_, v_msg_549_);
    crate::leanh::lean_dec(v___x_551_);
    v___x_553_ = (crate::leanh::lean_unbox(v___x_552_) as u8);
    crate::leanh::lean_dec(v___x_552_);
    return v___x_553_;
}
pub unsafe fn l_panic___at___00Std_Http_Version_ofString_x21_spec__0___boxed(
    mut v_msg_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_555_: u8 = 0;
    let mut v_r_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_panic___at___00Std_Http_Version_ofString_x21_spec__0(v_msg_554_);
    v_r_556_ = crate::leanh::lean_box((v_res_555_) as usize);
    return v_r_556_;
}
pub unsafe fn l_Std_Http_Version_ofString_x21(mut v_s_560_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Std_Http_Version_ofString_x3f(v_s_560_);
    if crate::leanh::lean_obj_tag(v___x_561_) == 0 {
        let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: u8 = 0;
        v___x_562_ = l_Std_Http_Version_ofString_x21___closed__0;
        v___x_563_ = l_Std_Http_Version_ofString_x21___closed__1;
        v___x_564_ = crate::leanh::lean_unsigned_to_nat(81);
        v___x_565_ = crate::leanh::lean_unsigned_to_nat(12);
        v___x_566_ = l_Std_Http_Version_ofString_x21___closed__2;
        v___x_567_ = l_String_quote(v_s_560_);
        v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
        crate::leanh::lean_dec_ref(v___x_567_);
        v___x_569_ =
            l_mkPanicMessageWithDecl(v___x_562_, v___x_563_, v___x_564_, v___x_565_, v___x_568_);
        crate::leanh::lean_dec_ref(v___x_568_);
        v___x_570_ = l_panic___at___00Std_Http_Version_ofString_x21_spec__0(v___x_569_);
        return v___x_570_;
    } else {
        let mut v_val_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_572_: u8 = 0;
        crate::leanh::lean_dec_ref(v_s_560_);
        v_val_571_ = crate::leanh::lean_ctor_get(v___x_561_, 0);
        crate::leanh::lean_inc(v_val_571_);
        crate::leanh::lean_dec_ref_known(v___x_561_, 1);
        v___x_572_ = (crate::leanh::lean_unbox(v_val_571_) as u8);
        crate::leanh::lean_dec(v_val_571_);
        return v___x_572_;
    }
}
pub unsafe fn l_Std_Http_Version_ofString_x21___boxed(
    mut v_s_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Std_Http_Version_ofString_x21(v_s_573_);
    v_r_575_ = crate::leanh::lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Std_Http_Version_toNumber(mut v_x_587_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_587_ {
        0 => {
            let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_588_ = l_Std_Http_Version_toNumber___closed__0;
            return v___x_588_;
        }
        1 => {
            let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_589_ = l_Std_Http_Version_toNumber___closed__1;
            return v___x_589_;
        }
        2 => {
            let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_590_ = l_Std_Http_Version_toNumber___closed__2;
            return v___x_590_;
        }
        _ => {
            let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_591_ = l_Std_Http_Version_toNumber___closed__3;
            return v___x_591_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_toNumber___boxed(
    mut v_x_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_91__boxed_593_: u8 = 0;
    let mut v_res_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_91__boxed_593_ = (crate::leanh::lean_unbox(v_x_592_) as u8);
    v_res_594_ = l_Std_Http_Version_toNumber(v_x_91__boxed_593_);
    return v_res_594_;
}
pub unsafe fn l_Std_Http_Version_instToString___lam__0(
    mut v_x_595_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_595_ {
        0 => {
            let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_596_ = l_Std_Http_Version_ofString_x3f___closed__0;
            return v___x_596_;
        }
        1 => {
            let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_597_ = l_Std_Http_Version_ofString_x3f___closed__1;
            return v___x_597_;
        }
        2 => {
            let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_598_ = l_Std_Http_Version_ofString_x3f___closed__2;
            return v___x_598_;
        }
        _ => {
            let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_599_ = l_Std_Http_Version_ofString_x3f___closed__3;
            return v___x_599_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_instToString___lam__0___boxed(
    mut v_x_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_601_: u8 = 0;
    let mut v_res_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_601_ = (crate::leanh::lean_unbox(v_x_600_) as u8);
    v_res_602_ = l_Std_Http_Version_instToString___lam__0(v_x_42__boxed_601_);
    return v_res_602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Version(
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
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_instInhabitedVersion_default = _init_l_Std_Http_instInhabitedVersion_default();
    l_Std_Http_instInhabitedVersion = _init_l_Std_Http_instInhabitedVersion();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Version(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Version(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Version(builtin);
}
