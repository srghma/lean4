// Lean compiler output
// Module: Std.Http.Data.Version
// Imports: Init.Data.ToString Init.Data.String.Basic
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_to_int, lean_panic_fn_borrowed, lean_string_append,
    lean_string_dec_eq,
};
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
pub static l_Std_Http_instReprVersion_repr___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 49,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__2_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 49,
            49, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__4_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 50,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__6_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 86, 101, 114, 115, 105, 111, 110, 46, 118, 51,
            48, 0,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_instReprVersion_repr___closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instReprVersion_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion_repr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_instReprVersion_repr___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprVersion_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_instReprVersion_repr___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprVersion_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprVersion___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprVersion_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprVersion___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instReprVersion: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprVersion___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instInhabitedVersion_default: u8 = 0;
pub static mut l_Std_Http_instInhabitedVersion: u8 = 0;
pub static l_Std_Http_instBEqVersion___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instBEqVersion_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instBEqVersion___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqVersion___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_instBEqVersion: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instBEqVersion___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_Version_ofNumber_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_Version_ofNumber_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_Version_ofNumber_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofNumber_x3f___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
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
static mut l_Std_Http_Version_ofNumber_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofNumber_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
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
static mut l_Std_Http_Version_ofString_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
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
static mut l_Std_Http_Version_ofString_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
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
static mut l_Std_Http_Version_ofString_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x3f___closed__3_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
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
static mut l_Std_Http_Version_ofString_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__0_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 86, 101, 114, 115, 105,
            111, 110, 0,
        ],
    };
static mut l_Std_Http_Version_ofString_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__1_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Http_Version_ofString_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_ofString_x21___closed__2_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
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
            105, 110, 118, 97, 108, 105, 100, 32, 72, 84, 84, 80, 32, 118, 101, 114, 115, 105, 111,
            110, 58, 32, 0,
        ],
    };
static mut l_Std_Http_Version_ofString_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_ofString_x21___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_toNumber___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Version_toNumber___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_toNumber___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Version_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Version_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Version_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Version_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Version_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Version_ctorIdx(mut v_x_303_: u8) -> *mut leanh::LeanObject {
    match v_x_303_ {
        0 => {
            let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_304_ = leanh::lean_unsigned_to_nat(0);
            return v___x_304_;
        }
        1 => {
            let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_305_ = leanh::lean_unsigned_to_nat(1);
            return v___x_305_;
        }
        2 => {
            let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_306_ = leanh::lean_unsigned_to_nat(2);
            return v___x_306_;
        }
        _ => {
            let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_307_ = leanh::lean_unsigned_to_nat(3);
            return v___x_307_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_ctorIdx___boxed(
    mut v_x_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_309_: u8 = 0;
    let mut v_res_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_309_ = (leanh::lean_unbox(v_x_308_) as u8);
    v_res_310_ = l_Std_Http_Version_ctorIdx(v_x_boxed_309_);
    return v_res_310_;
}
pub unsafe fn l_Std_Http_Version_toCtorIdx(mut v_x_311_: u8) -> *mut leanh::LeanObject {
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Std_Http_Version_ctorIdx(v_x_311_);
    return v___x_312_;
}
pub unsafe fn l_Std_Http_Version_toCtorIdx___boxed(
    mut v_x_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_314_: u8 = 0;
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_314_ = (leanh::lean_unbox(v_x_313_) as u8);
    v_res_315_ = l_Std_Http_Version_toCtorIdx(v_x_4__boxed_314_);
    return v_res_315_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___redArg(
    mut v_k_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_316_);
    return v_k_316_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___redArg___boxed(
    mut v_k_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Http_Version_ctorElim___redArg(v_k_317_);
    leanh::lean_dec(v_k_317_);
    return v_res_318_;
}
pub unsafe fn l_Std_Http_Version_ctorElim(
    mut v_motive_319_: *mut leanh::LeanObject,
    mut v_ctorIdx_320_: *mut leanh::LeanObject,
    mut v_t_321_: u8,
    mut v_h_322_: *mut leanh::LeanObject,
    mut v_k_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_323_);
    return v_k_323_;
}
pub unsafe fn l_Std_Http_Version_ctorElim___boxed(
    mut v_motive_324_: *mut leanh::LeanObject,
    mut v_ctorIdx_325_: *mut leanh::LeanObject,
    mut v_t_326_: *mut leanh::LeanObject,
    mut v_h_327_: *mut leanh::LeanObject,
    mut v_k_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_329_: u8 = 0;
    let mut v_res_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_329_ = (leanh::lean_unbox(v_t_326_) as u8);
    v_res_330_ = l_Std_Http_Version_ctorElim(
        v_motive_324_,
        v_ctorIdx_325_,
        v_t_boxed_329_,
        v_h_327_,
        v_k_328_,
    );
    leanh::lean_dec(v_k_328_);
    leanh::lean_dec(v_ctorIdx_325_);
    return v_res_330_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___redArg(
    mut v_v10_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v10_331_);
    return v_v10_331_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___redArg___boxed(
    mut v_v10_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_333_ = l_Std_Http_Version_v10_elim___redArg(v_v10_332_);
    leanh::lean_dec(v_v10_332_);
    return v_res_333_;
}
pub unsafe fn l_Std_Http_Version_v10_elim(
    mut v_motive_334_: *mut leanh::LeanObject,
    mut v_t_335_: u8,
    mut v_h_336_: *mut leanh::LeanObject,
    mut v_v10_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v10_337_);
    return v_v10_337_;
}
pub unsafe fn l_Std_Http_Version_v10_elim___boxed(
    mut v_motive_338_: *mut leanh::LeanObject,
    mut v_t_339_: *mut leanh::LeanObject,
    mut v_h_340_: *mut leanh::LeanObject,
    mut v_v10_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_342_: u8 = 0;
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_342_ = (leanh::lean_unbox(v_t_339_) as u8);
    v_res_343_ = l_Std_Http_Version_v10_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_v10_341_);
    leanh::lean_dec(v_v10_341_);
    return v_res_343_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___redArg(
    mut v_v11_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v11_344_);
    return v_v11_344_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___redArg___boxed(
    mut v_v11_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l_Std_Http_Version_v11_elim___redArg(v_v11_345_);
    leanh::lean_dec(v_v11_345_);
    return v_res_346_;
}
pub unsafe fn l_Std_Http_Version_v11_elim(
    mut v_motive_347_: *mut leanh::LeanObject,
    mut v_t_348_: u8,
    mut v_h_349_: *mut leanh::LeanObject,
    mut v_v11_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v11_350_);
    return v_v11_350_;
}
pub unsafe fn l_Std_Http_Version_v11_elim___boxed(
    mut v_motive_351_: *mut leanh::LeanObject,
    mut v_t_352_: *mut leanh::LeanObject,
    mut v_h_353_: *mut leanh::LeanObject,
    mut v_v11_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_355_: u8 = 0;
    let mut v_res_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_355_ = (leanh::lean_unbox(v_t_352_) as u8);
    v_res_356_ = l_Std_Http_Version_v11_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_v11_354_);
    leanh::lean_dec(v_v11_354_);
    return v_res_356_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___redArg(
    mut v_v20_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v20_357_);
    return v_v20_357_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___redArg___boxed(
    mut v_v20_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_Std_Http_Version_v20_elim___redArg(v_v20_358_);
    leanh::lean_dec(v_v20_358_);
    return v_res_359_;
}
pub unsafe fn l_Std_Http_Version_v20_elim(
    mut v_motive_360_: *mut leanh::LeanObject,
    mut v_t_361_: u8,
    mut v_h_362_: *mut leanh::LeanObject,
    mut v_v20_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v20_363_);
    return v_v20_363_;
}
pub unsafe fn l_Std_Http_Version_v20_elim___boxed(
    mut v_motive_364_: *mut leanh::LeanObject,
    mut v_t_365_: *mut leanh::LeanObject,
    mut v_h_366_: *mut leanh::LeanObject,
    mut v_v20_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_368_: u8 = 0;
    let mut v_res_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_368_ = (leanh::lean_unbox(v_t_365_) as u8);
    v_res_369_ = l_Std_Http_Version_v20_elim(v_motive_364_, v_t_boxed_368_, v_h_366_, v_v20_367_);
    leanh::lean_dec(v_v20_367_);
    return v_res_369_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___redArg(
    mut v_v30_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v30_370_);
    return v_v30_370_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___redArg___boxed(
    mut v_v30_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Std_Http_Version_v30_elim___redArg(v_v30_371_);
    leanh::lean_dec(v_v30_371_);
    return v_res_372_;
}
pub unsafe fn l_Std_Http_Version_v30_elim(
    mut v_motive_373_: *mut leanh::LeanObject,
    mut v_t_374_: u8,
    mut v_h_375_: *mut leanh::LeanObject,
    mut v_v30_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v30_376_);
    return v_v30_376_;
}
pub unsafe fn l_Std_Http_Version_v30_elim___boxed(
    mut v_motive_377_: *mut leanh::LeanObject,
    mut v_t_378_: *mut leanh::LeanObject,
    mut v_h_379_: *mut leanh::LeanObject,
    mut v_v30_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_381_: u8 = 0;
    let mut v_res_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_381_ = (leanh::lean_unbox(v_t_378_) as u8);
    v_res_382_ = l_Std_Http_Version_v30_elim(v_motive_377_, v_t_boxed_381_, v_h_379_, v_v30_380_);
    leanh::lean_dec(v_v30_380_);
    return v_res_382_;
}
pub unsafe fn _init_l_Std_Http_instReprVersion_repr___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = leanh::lean_unsigned_to_nat(2);
    v___x_396_ = lean_nat_to_int(v___x_395_);
    return v___x_396_;
}
pub unsafe fn _init_l_Std_Http_instReprVersion_repr___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = leanh::lean_unsigned_to_nat(1);
    v___x_398_ = lean_nat_to_int(v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_Std_Http_instReprVersion_repr(
    mut v_x_399_: u8,
    mut v_prec_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: u8 = 0;
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: u8 = 0;
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: u8 = 0;
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: u8 = 0;
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_399_ {
                0 => {
                    v___x_429_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_430_ = lean_nat_dec_le(v___x_429_, v_prec_400_);
                    if v___x_430_ == 0 {
                        v___x_431_ = leanh::lean_obj_once(
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
                        v___x_432_ = leanh::lean_obj_once(
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
                    v___x_433_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_434_ = lean_nat_dec_le(v___x_433_, v_prec_400_);
                    if v___x_434_ == 0 {
                        v___x_435_ = leanh::lean_obj_once(
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
                        v___x_436_ = leanh::lean_obj_once(
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
                    v___x_437_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_438_ = lean_nat_dec_le(v___x_437_, v_prec_400_);
                    if v___x_438_ == 0 {
                        v___x_439_ = leanh::lean_obj_once(
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
                        v___x_440_ = leanh::lean_obj_once(
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
                    v___x_441_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_442_ = lean_nat_dec_le(v___x_441_, v_prec_400_);
                    if v___x_442_ == 0 {
                        v___x_443_ = leanh::lean_obj_once(
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
                        v___x_444_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_402_);
                v___x_404_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_404_, 0, v___y_402_);
                leanh::lean_ctor_set(v___x_404_, 1, v___x_403_);
                v___x_405_ = 0;
                v___x_406_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_406_, 0, v___x_404_);
                leanh::lean_ctor_set_uint8(
                    v___x_406_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_405_,
                );
                v___x_407_ = l_Repr_addAppParen(v___x_406_, v_prec_400_);
                return v___x_407_;
            }
            2 => {
                v___x_410_ = l_Std_Http_instReprVersion_repr___closed__3;
                leanh::lean_inc(v___y_409_);
                v___x_411_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_411_, 0, v___y_409_);
                leanh::lean_ctor_set(v___x_411_, 1, v___x_410_);
                v___x_412_ = 0;
                v___x_413_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_413_, 0, v___x_411_);
                leanh::lean_ctor_set_uint8(
                    v___x_413_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_412_,
                );
                v___x_414_ = l_Repr_addAppParen(v___x_413_, v_prec_400_);
                return v___x_414_;
            }
            3 => {
                v___x_417_ = l_Std_Http_instReprVersion_repr___closed__5;
                leanh::lean_inc(v___y_416_);
                v___x_418_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_418_, 0, v___y_416_);
                leanh::lean_ctor_set(v___x_418_, 1, v___x_417_);
                v___x_419_ = 0;
                v___x_420_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_420_, 0, v___x_418_);
                leanh::lean_ctor_set_uint8(
                    v___x_420_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_419_,
                );
                v___x_421_ = l_Repr_addAppParen(v___x_420_, v_prec_400_);
                return v___x_421_;
            }
            4 => {
                v___x_424_ = l_Std_Http_instReprVersion_repr___closed__7;
                leanh::lean_inc(v___y_423_);
                v___x_425_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_425_, 0, v___y_423_);
                leanh::lean_ctor_set(v___x_425_, 1, v___x_424_);
                v___x_426_ = 0;
                v___x_427_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_427_, 0, v___x_425_);
                leanh::lean_ctor_set_uint8(
                    v___x_427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_445_: *mut leanh::LeanObject,
    mut v_prec_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_233__boxed_447_: u8 = 0;
    let mut v_res_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_447_ = (leanh::lean_unbox(v_x_445_) as u8);
    v_res_448_ = l_Std_Http_instReprVersion_repr(v_x_233__boxed_447_, v_prec_446_);
    leanh::lean_dec(v_prec_446_);
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
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    v___x_455_ = l_Std_Http_Version_ctorIdx(v_x_453_);
    v___x_456_ = l_Std_Http_Version_ctorIdx(v_y_454_);
    v___x_457_ = lean_nat_dec_eq(v___x_455_, v___x_456_);
    leanh::lean_dec(v___x_456_);
    leanh::lean_dec(v___x_455_);
    return v___x_457_;
}
pub unsafe fn l_Std_Http_instBEqVersion_beq___boxed(
    mut v_x_458_: *mut leanh::LeanObject,
    mut v_y_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_460_: u8 = 0;
    let mut v_y_18__boxed_461_: u8 = 0;
    let mut v_res_462_: u8 = 0;
    let mut v_r_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_460_ = (leanh::lean_unbox(v_x_458_) as u8);
    v_y_18__boxed_461_ = (leanh::lean_unbox(v_y_459_) as u8);
    v_res_462_ = l_Std_Http_instBEqVersion_beq(v_x_17__boxed_460_, v_y_18__boxed_461_);
    v_r_463_ = leanh::lean_box((v_res_462_) as usize);
    return v_r_463_;
}
pub unsafe fn l_Std_Http_Version_ofNat(mut v_n_466_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    v___x_467_ = leanh::lean_unsigned_to_nat(1);
    v___x_468_ = lean_nat_dec_le(v_n_466_, v___x_467_);
    if v___x_468_ == 0 {
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: u8 = 0;
        v___x_469_ = leanh::lean_unsigned_to_nat(2);
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
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: u8 = 0;
        v___x_473_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_n_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Http_Version_ofNat(v_n_477_);
    leanh::lean_dec(v_n_477_);
    v_r_479_ = leanh::lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l_Std_Http_instDecidableEqVersion(mut v_x_480_: u8, mut v_y_481_: u8) -> u8 {
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    v___x_482_ = l_Std_Http_Version_ctorIdx(v_x_480_);
    v___x_483_ = l_Std_Http_Version_ctorIdx(v_y_481_);
    v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
    leanh::lean_dec(v___x_483_);
    leanh::lean_dec(v___x_482_);
    return v___x_484_;
}
pub unsafe fn l_Std_Http_instDecidableEqVersion___boxed(
    mut v_x_485_: *mut leanh::LeanObject,
    mut v_y_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_487_: u8 = 0;
    let mut v_y_14__boxed_488_: u8 = 0;
    let mut v_res_489_: u8 = 0;
    let mut v_r_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_487_ = (leanh::lean_unbox(v_x_485_) as u8);
    v_y_14__boxed_488_ = (leanh::lean_unbox(v_y_486_) as u8);
    v_res_489_ = l_Std_Http_instDecidableEqVersion(v_x_13__boxed_487_, v_y_14__boxed_488_);
    v_r_490_ = leanh::lean_box((v_res_489_) as usize);
    return v_r_490_;
}
pub unsafe fn l_Std_Http_Version_ofNumber_x3f(
    mut v_x_503_: *mut leanh::LeanObject,
    mut v_x_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    v___x_505_ = leanh::lean_unsigned_to_nat(1);
    v___x_506_ = lean_nat_dec_eq(v_x_503_, v___x_505_);
    if v___x_506_ == 0 {
        let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: u8 = 0;
        v___x_507_ = leanh::lean_unsigned_to_nat(2);
        v___x_508_ = lean_nat_dec_eq(v_x_503_, v___x_507_);
        if v___x_508_ == 0 {
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_510_: u8 = 0;
            v___x_509_ = leanh::lean_unsigned_to_nat(3);
            v___x_510_ = lean_nat_dec_eq(v_x_503_, v___x_509_);
            if v___x_510_ == 0 {
                let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_511_ = leanh::lean_box(0);
                return v___x_511_;
            } else {
                let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_513_: u8 = 0;
                v___x_512_ = leanh::lean_unsigned_to_nat(0);
                v___x_513_ = lean_nat_dec_eq(v_x_504_, v___x_512_);
                if v___x_513_ == 0 {
                    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_514_ = leanh::lean_box(0);
                    return v___x_514_;
                } else {
                    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_515_ = l_Std_Http_Version_ofNumber_x3f___closed__0;
                    return v___x_515_;
                }
            }
        } else {
            let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_517_: u8 = 0;
            v___x_516_ = leanh::lean_unsigned_to_nat(0);
            v___x_517_ = lean_nat_dec_eq(v_x_504_, v___x_516_);
            if v___x_517_ == 0 {
                let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_518_ = leanh::lean_box(0);
                return v___x_518_;
            } else {
                let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_519_ = l_Std_Http_Version_ofNumber_x3f___closed__1;
                return v___x_519_;
            }
        }
    } else {
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: u8 = 0;
        v___x_520_ = leanh::lean_unsigned_to_nat(0);
        v___x_521_ = lean_nat_dec_eq(v_x_504_, v___x_520_);
        if v___x_521_ == 0 {
            let mut v___x_522_: u8 = 0;
            v___x_522_ = lean_nat_dec_eq(v_x_504_, v___x_505_);
            if v___x_522_ == 0 {
                let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_523_ = leanh::lean_box(0);
                return v___x_523_;
            } else {
                let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_524_ = l_Std_Http_Version_ofNumber_x3f___closed__2;
                return v___x_524_;
            }
        } else {
            let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_525_ = l_Std_Http_Version_ofNumber_x3f___closed__3;
            return v___x_525_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_ofNumber_x3f___boxed(
    mut v_x_526_: *mut leanh::LeanObject,
    mut v_x_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Std_Http_Version_ofNumber_x3f(v_x_526_, v_x_527_);
    leanh::lean_dec(v_x_527_);
    leanh::lean_dec(v_x_526_);
    return v_res_528_;
}
pub unsafe fn l_Std_Http_Version_ofString_x3f(
    mut v_x_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_534_ = l_Std_Http_Version_ofString_x3f___closed__0;
    v___x_535_ = lean_string_dec_eq(v_x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: u8 = 0;
        v___x_536_ = l_Std_Http_Version_ofString_x3f___closed__1;
        v___x_537_ = lean_string_dec_eq(v_x_533_, v___x_536_);
        if v___x_537_ == 0 {
            let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_539_: u8 = 0;
            v___x_538_ = l_Std_Http_Version_ofString_x3f___closed__2;
            v___x_539_ = lean_string_dec_eq(v_x_533_, v___x_538_);
            if v___x_539_ == 0 {
                let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_541_: u8 = 0;
                v___x_540_ = l_Std_Http_Version_ofString_x3f___closed__3;
                v___x_541_ = lean_string_dec_eq(v_x_533_, v___x_540_);
                if v___x_541_ == 0 {
                    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_542_ = leanh::lean_box(0);
                    return v___x_542_;
                } else {
                    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_543_ = l_Std_Http_Version_ofNumber_x3f___closed__0;
                    return v___x_543_;
                }
            } else {
                let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_544_ = l_Std_Http_Version_ofNumber_x3f___closed__1;
                return v___x_544_;
            }
        } else {
            let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_545_ = l_Std_Http_Version_ofNumber_x3f___closed__2;
            return v___x_545_;
        }
    } else {
        let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_546_ = l_Std_Http_Version_ofNumber_x3f___closed__3;
        return v___x_546_;
    }
}
pub unsafe fn l_Std_Http_Version_ofString_x3f___boxed(
    mut v_x_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_548_ = l_Std_Http_Version_ofString_x3f(v_x_547_);
    leanh::lean_dec_ref(v_x_547_);
    return v_res_548_;
}
pub unsafe fn l_panic___at___00Std_Http_Version_ofString_x21_spec__0(
    mut v_msg_549_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    v___x_550_ = 0;
    v___x_551_ = leanh::lean_box((v___x_550_) as usize);
    v___x_552_ = lean_panic_fn_borrowed(v___x_551_, v_msg_549_);
    leanh::lean_dec(v___x_551_);
    v___x_553_ = (leanh::lean_unbox(v___x_552_) as u8);
    leanh::lean_dec(v___x_552_);
    return v___x_553_;
}
pub unsafe fn l_panic___at___00Std_Http_Version_ofString_x21_spec__0___boxed(
    mut v_msg_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_555_: u8 = 0;
    let mut v_r_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_panic___at___00Std_Http_Version_ofString_x21_spec__0(v_msg_554_);
    v_r_556_ = leanh::lean_box((v_res_555_) as usize);
    return v_r_556_;
}
pub unsafe fn l_Std_Http_Version_ofString_x21(mut v_s_560_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Std_Http_Version_ofString_x3f(v_s_560_);
    if leanh::lean_obj_tag(v___x_561_) == 0 {
        let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: u8 = 0;
        v___x_562_ = l_Std_Http_Version_ofString_x21___closed__0;
        v___x_563_ = l_Std_Http_Version_ofString_x21___closed__1;
        v___x_564_ = leanh::lean_unsigned_to_nat(81);
        v___x_565_ = leanh::lean_unsigned_to_nat(12);
        v___x_566_ = l_Std_Http_Version_ofString_x21___closed__2;
        v___x_567_ = l_String_quote(v_s_560_);
        v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
        leanh::lean_dec_ref(v___x_567_);
        v___x_569_ =
            l_mkPanicMessageWithDecl(v___x_562_, v___x_563_, v___x_564_, v___x_565_, v___x_568_);
        leanh::lean_dec_ref(v___x_568_);
        v___x_570_ = l_panic___at___00Std_Http_Version_ofString_x21_spec__0(v___x_569_);
        return v___x_570_;
    } else {
        let mut v_val_571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_572_: u8 = 0;
        leanh::lean_dec_ref(v_s_560_);
        v_val_571_ = leanh::lean_ctor_get(v___x_561_, 0);
        leanh::lean_inc(v_val_571_);
        leanh::lean_dec_ref_known(v___x_561_, 1);
        v___x_572_ = (leanh::lean_unbox(v_val_571_) as u8);
        leanh::lean_dec(v_val_571_);
        return v___x_572_;
    }
}
pub unsafe fn l_Std_Http_Version_ofString_x21___boxed(
    mut v_s_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Std_Http_Version_ofString_x21(v_s_573_);
    v_r_575_ = leanh::lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Std_Http_Version_toNumber(mut v_x_587_: u8) -> *mut leanh::LeanObject {
    match v_x_587_ {
        0 => {
            let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_588_ = l_Std_Http_Version_toNumber___closed__0;
            return v___x_588_;
        }
        1 => {
            let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_589_ = l_Std_Http_Version_toNumber___closed__1;
            return v___x_589_;
        }
        2 => {
            let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_590_ = l_Std_Http_Version_toNumber___closed__2;
            return v___x_590_;
        }
        _ => {
            let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_591_ = l_Std_Http_Version_toNumber___closed__3;
            return v___x_591_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_toNumber___boxed(
    mut v_x_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_91__boxed_593_: u8 = 0;
    let mut v_res_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_91__boxed_593_ = (leanh::lean_unbox(v_x_592_) as u8);
    v_res_594_ = l_Std_Http_Version_toNumber(v_x_91__boxed_593_);
    return v_res_594_;
}
pub unsafe fn l_Std_Http_Version_instToString___lam__0(
    mut v_x_595_: u8,
) -> *mut leanh::LeanObject {
    match v_x_595_ {
        0 => {
            let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_596_ = l_Std_Http_Version_ofString_x3f___closed__0;
            return v___x_596_;
        }
        1 => {
            let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_597_ = l_Std_Http_Version_ofString_x3f___closed__1;
            return v___x_597_;
        }
        2 => {
            let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_598_ = l_Std_Http_Version_ofString_x3f___closed__2;
            return v___x_598_;
        }
        _ => {
            let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_599_ = l_Std_Http_Version_ofString_x3f___closed__3;
            return v___x_599_;
        }
    }
}
pub unsafe fn l_Std_Http_Version_instToString___lam__0___boxed(
    mut v_x_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42__boxed_601_: u8 = 0;
    let mut v_res_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_601_ = (leanh::lean_unbox(v_x_600_) as u8);
    v_res_602_ = l_Std_Http_Version_instToString___lam__0(v_x_42__boxed_601_);
    return v_res_602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Version(
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
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Http_instInhabitedVersion_default = _init_l_Std_Http_instInhabitedVersion_default();
    l_Std_Http_instInhabitedVersion = _init_l_Std_Http_instInhabitedVersion();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Version(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Version(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Version(builtin);
}