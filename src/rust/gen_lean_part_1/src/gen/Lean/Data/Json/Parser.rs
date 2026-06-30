// Lean compiler output
// Module: Lean.Data.Json.Parser
// Imports: Lean.Data.Json.Basic Std.Internal.Parsec
use crate::ffi::{
    lean_array_push, lean_int_add, lean_int_mul, lean_int_neg, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_pow, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_string_append, lean_string_compare, lean_string_push,
    lean_string_utf8_byte_size, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint16_dec_lt, lean_uint16_lor, lean_uint16_shift_left, lean_uint16_to_uint32,
    lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_land, lean_uint32_lor,
    lean_uint32_shift_left, lean_uint32_sub, lean_uint32_to_nat, lean_uint32_to_uint16,
};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::{
    initialize_Lean_Data_Json_Basic, l_Lean_JsonNumber_fromInt, l_Lean_JsonNumber_shiftl,
    l_Lean_JsonNumber_shiftr, runtime_initialize_Lean_Data_Json_Basic,
};
use crate::r#gen::Std::Internal::Parsec::String::{
    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs,
    l_Std_Internal_Parsec_String_Parser_run___redArg, l_Std_Internal_Parsec_String_pstring,
};
use crate::r#gen::Std::Internal::Parsec::{
    initialize_Std_Internal_Parsec, runtime_initialize_Std_Internal_Parsec,
};
pub static l_Lean_Json_Parser_hexChar___closed__0_value: leanh::LeanStringObject<22> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 104, 101, 120, 32, 99, 104, 97, 114, 97, 99, 116,
            101, 114, 0,
        ],
    };
static mut l_Lean_Json_Parser_hexChar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_hexChar___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_hexChar___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_hexChar___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_hexChar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_hexChar___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_finishSurrogatePair___closed__0_value:
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
static mut l_Lean_Json_Parser_finishSurrogatePair___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_finishSurrogatePair___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_finishSurrogatePair___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Json_Parser_finishSurrogatePair___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Json_Parser_finishSurrogatePair___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_finishSurrogatePair___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_escapedChar___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            105, 108, 108, 101, 103, 97, 108, 32, 92, 117, 32, 101, 115, 99, 97, 112, 101, 0,
        ],
    };
static mut l_Lean_Json_Parser_escapedChar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_escapedChar___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_escapedChar___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_escapedChar___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_escapedChar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_escapedChar___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Json_Parser_escapedChar___boxed__const__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Json_Parser_strCore___closed__0_value: leanh::LeanStringObject<31> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 104, 97, 114, 97, 99, 116,
            101, 114, 32, 105, 110, 32, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Json_Parser_strCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_strCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_strCore___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_strCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_strCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_strCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_lookahead___redArg___closed__0_value: leanh::LeanStringObject<
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
    m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 0],
};
static mut l_Lean_Json_Parser_lookahead___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_lookahead___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natNonZero___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 49, 45, 57, 0],
    };
static mut l_Lean_Json_Parser_natNonZero___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natNonZero___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natNonZero___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_natNonZero___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_natNonZero___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natNonZero___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natNumDigits___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 105, 103, 105, 116, 0,
        ],
    };
static mut l_Lean_Json_Parser_natNumDigits___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natNumDigits___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natNumDigits___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_natNumDigits___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_natNumDigits___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natNumDigits___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natMaybeZero___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 48, 45, 57, 0],
    };
static mut l_Lean_Json_Parser_natMaybeZero___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natMaybeZero___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_natMaybeZero___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_natMaybeZero___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_natMaybeZero___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_natMaybeZero___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Json_Parser_numSign___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_Parser_numSign___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Json_Parser_numSign___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_Parser_numSign___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Json_Parser_numWithDecimals___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_Parser_numWithDecimals___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Json_Parser_numWithDecimals___closed__1_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 111, 111, 32, 109, 97, 110, 121, 32, 100, 101, 99, 105, 109, 97, 108, 115, 0,
    ],
};
static mut l_Lean_Json_Parser_numWithDecimals___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_numWithDecimals___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_numWithDecimals___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_numWithDecimals___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_numWithDecimals___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_numWithDecimals___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_exponent___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            101, 120, 112, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 0,
        ],
    };
static mut l_Lean_Json_Parser_exponent___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_exponent___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_exponent___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_exponent___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_exponent___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_exponent___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_Parser_arrayCore___closed__0_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
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
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 104, 97, 114, 97, 99, 116,
            101, 114, 32, 105, 110, 32, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Json_Parser_arrayCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_arrayCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_arrayCore___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_arrayCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_arrayCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_arrayCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 112, 117, 116, 0,
        ],
    };
static mut l_Lean_Json_Parser_anyCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_anyCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Json_Parser_anyCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__3_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Json_Parser_anyCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__4_value: leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Json_Parser_anyCore___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 34, 0],
    };
static mut l_Lean_Json_Parser_objectCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_objectCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__2_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 58, 0],
    };
static mut l_Lean_Json_Parser_objectCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_objectCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__4_value: leanh::LeanStringObject<31> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 104, 97, 114, 97, 99, 116,
            101, 114, 32, 105, 110, 32, 111, 98, 106, 101, 99, 116, 0,
        ],
    };
static mut l_Lean_Json_Parser_objectCore___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_objectCore___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_objectCore___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_objectCore___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Json_Parser_anyCore___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__6_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Json_Parser_anyCore___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_anyCore___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_anyCore___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_anyCore___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_any___closed__0_value: leanh::LeanStringObject<22> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105, 110,
            112, 117, 116, 0,
        ],
    };
static mut l_Lean_Json_Parser_any___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_any___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_Parser_any___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_Parser_any___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_Parser_any___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Parser_any___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Json_Parser_hexChar(
    mut v_a_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v_c_2156_: u32 = 0;
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: u32 = 0;
    let mut v___y_2162_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u32 = 0;
    let mut v___x_2166_: u32 = 0;
    let mut v___x_2167_: u32 = 0;
    let mut v___x_2168_: u16 = 0;
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: u32 = 0;
    let mut v___y_2173_: u8 = 0;
    let mut v___x_2174_: u32 = 0;
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: u32 = 0;
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: u32 = 0;
    let mut v___x_2179_: u32 = 0;
    let mut v___x_2180_: u32 = 0;
    let mut v___x_2181_: u16 = 0;
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u32 = 0;
    let mut v___y_2186_: u8 = 0;
    let mut v___x_2187_: u32 = 0;
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: u32 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u32 = 0;
    let mut v___x_2192_: u16 = 0;
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: u32 = 0;
    let mut v___x_2197_: u8 = 0;
    let mut v_reuseFailAlloc_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut v_unused_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2149_ = leanh::lean_ctor_get(v_a_2148_, 0);
                v_snd_2150_ = leanh::lean_ctor_get(v_a_2148_, 1);
                v___x_2151_ = lean_string_utf8_byte_size(v_fst_2149_);
                v___x_2152_ = lean_nat_dec_eq(v_snd_2150_, v___x_2151_);
                if v___x_2152_ == 0 {
                    leanh::lean_inc(v_snd_2150_);
                    leanh::lean_inc(v_fst_2149_);
                    v_isSharedCheck_2199_ = (!leanh::lean_is_exclusive(v_a_2148_)) as u8;
                    if v_isSharedCheck_2199_ == 0 {
                        v_unused_2200_ = leanh::lean_ctor_get(v_a_2148_, 1);
                        leanh::lean_dec(v_unused_2200_);
                        v_unused_2201_ = leanh::lean_ctor_get(v_a_2148_, 0);
                        leanh::lean_dec(v_unused_2201_);
                        v___x_2154_ = v_a_2148_;
                        v_isShared_2155_ = v_isSharedCheck_2199_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2148_);
                        v___x_2154_ = leanh::lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2199_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2202_ = leanh::lean_box(0);
                    v___x_2203_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2203_, 0, v_a_2148_);
                    leanh::lean_ctor_set(v___x_2203_, 1, v___x_2202_);
                    return v___x_2203_;
                }
            }
            1 => {
                v_c_2156_ = lean_string_utf8_get_fast(v_fst_2149_, v_snd_2150_);
                v___x_2157_ = lean_string_utf8_next_fast(v_fst_2149_, v_snd_2150_);
                leanh::lean_dec(v_snd_2150_);
                if v_isShared_2155_ == 0 {
                    leanh::lean_ctor_set(v___x_2154_, 1, v___x_2157_);
                    v_it_x27_2159_ = v___x_2154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_fst_2149_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2157_);
                    v_it_x27_2159_ = v_reuseFailAlloc_2198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2184_ = 48;
                v___x_2195_ = lean_uint32_dec_le(v___x_2184_, v_c_2156_);
                if v___x_2195_ == 0 {
                    v___y_2186_ = v___x_2195_;
                    state = 5;
                    continue;
                } else {
                    v___x_2196_ = 57;
                    v___x_2197_ = lean_uint32_dec_le(v_c_2156_, v___x_2196_);
                    v___y_2186_ = v___x_2197_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                if v___y_2162_ == 0 {
                    v___x_2163_ = l_Lean_Json_Parser_hexChar___closed__1;
                    v___x_2164_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2164_, 0, v_it_x27_2159_);
                    leanh::lean_ctor_set(v___x_2164_, 1, v___x_2163_);
                    return v___x_2164_;
                } else {
                    v___x_2165_ = lean_uint32_sub(v_c_2156_, v___y_2161_);
                    v___x_2166_ = 10;
                    v___x_2167_ = lean_uint32_add(v___x_2165_, v___x_2166_);
                    v___x_2168_ = lean_uint32_to_uint16(v___x_2167_);
                    v___x_2169_ = leanh::lean_box((v___x_2168_) as usize);
                    v___x_2170_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2170_, 0, v_it_x27_2159_);
                    leanh::lean_ctor_set(v___x_2170_, 1, v___x_2169_);
                    return v___x_2170_;
                }
            }
            4 => {
                if v___y_2173_ == 0 {
                    v___x_2174_ = 65;
                    v___x_2175_ = lean_uint32_dec_le(v___x_2174_, v_c_2156_);
                    if v___x_2175_ == 0 {
                        v___y_2161_ = v___x_2174_;
                        v___y_2162_ = v___x_2175_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2176_ = 70;
                        v___x_2177_ = lean_uint32_dec_le(v_c_2156_, v___x_2176_);
                        v___y_2161_ = v___x_2174_;
                        v___y_2162_ = v___x_2177_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2178_ = lean_uint32_sub(v_c_2156_, v___y_2172_);
                    v___x_2179_ = 10;
                    v___x_2180_ = lean_uint32_add(v___x_2178_, v___x_2179_);
                    v___x_2181_ = lean_uint32_to_uint16(v___x_2180_);
                    v___x_2182_ = leanh::lean_box((v___x_2181_) as usize);
                    v___x_2183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2183_, 0, v_it_x27_2159_);
                    leanh::lean_ctor_set(v___x_2183_, 1, v___x_2182_);
                    return v___x_2183_;
                }
            }
            5 => {
                if v___y_2186_ == 0 {
                    v___x_2187_ = 97;
                    v___x_2188_ = lean_uint32_dec_le(v___x_2187_, v_c_2156_);
                    if v___x_2188_ == 0 {
                        v___y_2172_ = v___x_2187_;
                        v___y_2173_ = v___x_2188_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2189_ = 102;
                        v___x_2190_ = lean_uint32_dec_le(v_c_2156_, v___x_2189_);
                        v___y_2172_ = v___x_2187_;
                        v___y_2173_ = v___x_2190_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2191_ = lean_uint32_sub(v_c_2156_, v___x_2184_);
                    v___x_2192_ = lean_uint32_to_uint16(v___x_2191_);
                    v___x_2193_ = leanh::lean_box((v___x_2192_) as usize);
                    v___x_2194_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2194_, 0, v_it_x27_2159_);
                    leanh::lean_ctor_set(v___x_2194_, 1, v___x_2193_);
                    return v___x_2194_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_finishSurrogatePair(
    mut v_low_2207_: u16,
    mut v_a_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v_c_2220_: u32 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: u32 = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: u32 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u32 = 0;
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u32 = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: u16 = 0;
    let mut v___x_2254_: u16 = 0;
    let mut v___x_2255_: u16 = 0;
    let mut v___x_2256_: u16 = 0;
    let mut v___x_2257_: u16 = 0;
    let mut v___x_2258_: u16 = 0;
    let mut v___x_2259_: u16 = 0;
    let mut v___x_2260_: u16 = 0;
    let mut v___x_2261_: u16 = 0;
    let mut v___x_2262_: u16 = 0;
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: u32 = 0;
    let mut v___x_2265_: u32 = 0;
    let mut v___x_2266_: u32 = 0;
    let mut v___x_2267_: u32 = 0;
    let mut v___x_2268_: u32 = 0;
    let mut v___x_2269_: u32 = 0;
    let mut v___x_2270_: u32 = 0;
    let mut v___x_2271_: u32 = 0;
    let mut v___x_2272_: u32 = 0;
    let mut v___x_2273_: u32 = 0;
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2293_: u8 = 0;
    let mut v_pos_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_pos_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut v_pos_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v___x_2321_: u32 = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u32 = 0;
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut v_unused_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2213_ = leanh::lean_ctor_get(v_a_2208_, 0);
                v_snd_2214_ = leanh::lean_ctor_get(v_a_2208_, 1);
                v___x_2215_ = lean_string_utf8_byte_size(v_fst_2213_);
                v___x_2216_ = lean_nat_dec_eq(v_snd_2214_, v___x_2215_);
                if v___x_2216_ == 0 {
                    leanh::lean_inc(v_snd_2214_);
                    leanh::lean_inc(v_fst_2213_);
                    v_isSharedCheck_2332_ = (!leanh::lean_is_exclusive(v_a_2208_)) as u8;
                    if v_isSharedCheck_2332_ == 0 {
                        v_unused_2333_ = leanh::lean_ctor_get(v_a_2208_, 1);
                        leanh::lean_dec(v_unused_2333_);
                        v_unused_2334_ = leanh::lean_ctor_get(v_a_2208_, 0);
                        leanh::lean_dec(v_unused_2334_);
                        v___x_2218_ = v_a_2208_;
                        v_isShared_2219_ = v_isSharedCheck_2332_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2208_);
                        v___x_2218_ = leanh::lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2332_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2335_ = leanh::lean_box(0);
                    v___x_2336_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2336_, 0, v_a_2208_);
                    leanh::lean_ctor_set(v___x_2336_, 1, v___x_2335_);
                    return v___x_2336_;
                }
            }
            1 => {
                v___x_2211_ = l_Lean_Json_Parser_finishSurrogatePair___closed__1;
                v___x_2212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2212_, 0, v___y_2210_);
                leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
                return v___x_2212_;
            }
            2 => {
                v_c_2220_ = lean_string_utf8_get_fast(v_fst_2213_, v_snd_2214_);
                v___x_2221_ = lean_string_utf8_next_fast(v_fst_2213_, v_snd_2214_);
                leanh::lean_dec(v_snd_2214_);
                leanh::lean_inc(v_fst_2213_);
                if v_isShared_2219_ == 0 {
                    leanh::lean_ctor_set(v___x_2218_, 1, v___x_2221_);
                    v_it_x27_2223_ = v___x_2218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2221_);
                    v_it_x27_2223_ = v_reuseFailAlloc_2331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2224_ = 92;
                v___x_2225_ = lean_uint32_dec_eq(v_c_2220_, v___x_2224_);
                if v___x_2225_ == 0 {
                    leanh::lean_dec(v_fst_2213_);
                    v___x_2226_ = l_Lean_Json_Parser_finishSurrogatePair___closed__1;
                    v___x_2227_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2227_, 0, v_it_x27_2223_);
                    leanh::lean_ctor_set(v___x_2227_, 1, v___x_2226_);
                    return v___x_2227_;
                } else {
                    v___x_2228_ = lean_nat_dec_eq(v___x_2221_, v___x_2215_);
                    if v___x_2228_ == 0 {
                        leanh::lean_dec_ref(v_it_x27_2223_);
                        v___x_2229_ = lean_string_utf8_get_fast(v_fst_2213_, v___x_2221_);
                        v___x_2230_ = lean_string_utf8_next_fast(v_fst_2213_, v___x_2221_);
                        leanh::lean_inc(v_fst_2213_);
                        v___x_2231_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2231_, 0, v_fst_2213_);
                        leanh::lean_ctor_set(v___x_2231_, 1, v___x_2230_);
                        v___x_2232_ = 117;
                        v___x_2233_ = lean_uint32_dec_eq(v___x_2229_, v___x_2232_);
                        if v___x_2233_ == 0 {
                            leanh::lean_dec(v_fst_2213_);
                            v___x_2234_ = l_Lean_Json_Parser_finishSurrogatePair___closed__1;
                            v___x_2235_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2235_, 0, v___x_2231_);
                            leanh::lean_ctor_set(v___x_2235_, 1, v___x_2234_);
                            return v___x_2235_;
                        } else {
                            v___x_2236_ = lean_nat_dec_eq(v___x_2230_, v___x_2215_);
                            if v___x_2236_ == 0 {
                                leanh::lean_dec_ref_known(v___x_2231_, 2);
                                v___x_2237_ = lean_string_utf8_get_fast(v_fst_2213_, v___x_2230_);
                                v___x_2238_ = lean_string_utf8_next_fast(v_fst_2213_, v___x_2230_);
                                v___x_2239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2239_, 0, v_fst_2213_);
                                leanh::lean_ctor_set(v___x_2239_, 1, v___x_2238_);
                                v___x_2321_ = 100;
                                v___x_2322_ = lean_uint32_dec_eq(v___x_2237_, v___x_2321_);
                                if v___x_2322_ == 0 {
                                    v___x_2323_ = 68;
                                    v___x_2324_ = lean_uint32_dec_eq(v___x_2237_, v___x_2323_);
                                    if v___x_2324_ == 0 {
                                        v___x_2325_ =
                                            l_Lean_Json_Parser_finishSurrogatePair___closed__1;
                                        v___x_2326_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2326_, 0, v___x_2239_);
                                        leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
                                        return v___x_2326_;
                                    } else {
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_fst_2213_);
                                v___x_2327_ = leanh::lean_box(0);
                                v___x_2328_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2328_, 0, v___x_2231_);
                                leanh::lean_ctor_set(v___x_2328_, 1, v___x_2327_);
                                return v___x_2328_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fst_2213_);
                        v___x_2329_ = leanh::lean_box(0);
                        v___x_2330_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2330_, 0, v_it_x27_2223_);
                        leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
                        return v___x_2330_;
                    }
                }
            }
            4 => {
                v___x_2241_ = l_Lean_Json_Parser_hexChar(v___x_2239_);
                if leanh::lean_obj_tag(v___x_2241_) == 0 {
                    v_pos_2242_ = leanh::lean_ctor_get(v___x_2241_, 0);
                    leanh::lean_inc(v_pos_2242_);
                    v_res_2243_ = leanh::lean_ctor_get(v___x_2241_, 1);
                    leanh::lean_inc(v_res_2243_);
                    leanh::lean_dec_ref_known(v___x_2241_, 2);
                    v___x_2244_ = l_Lean_Json_Parser_hexChar(v_pos_2242_);
                    if leanh::lean_obj_tag(v___x_2244_) == 0 {
                        v_pos_2245_ = leanh::lean_ctor_get(v___x_2244_, 0);
                        leanh::lean_inc(v_pos_2245_);
                        v_res_2246_ = leanh::lean_ctor_get(v___x_2244_, 1);
                        leanh::lean_inc(v_res_2246_);
                        leanh::lean_dec_ref_known(v___x_2244_, 2);
                        v___x_2247_ = l_Lean_Json_Parser_hexChar(v_pos_2245_);
                        if leanh::lean_obj_tag(v___x_2247_) == 0 {
                            v_pos_2248_ = leanh::lean_ctor_get(v___x_2247_, 0);
                            v_res_2249_ = leanh::lean_ctor_get(v___x_2247_, 1);
                            v_isSharedCheck_2293_ =
                                (!leanh::lean_is_exclusive(v___x_2247_)) as u8;
                            if v_isSharedCheck_2293_ == 0 {
                                v___x_2251_ = v___x_2247_;
                                v_isShared_2252_ = v_isSharedCheck_2293_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_res_2249_);
                                leanh::lean_inc(v_pos_2248_);
                                leanh::lean_dec(v___x_2247_);
                                v___x_2251_ = leanh::lean_box(0);
                                v_isShared_2252_ = v_isSharedCheck_2293_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_res_2246_);
                            leanh::lean_dec(v_res_2243_);
                            v_pos_2294_ = leanh::lean_ctor_get(v___x_2247_, 0);
                            v_err_2295_ = leanh::lean_ctor_get(v___x_2247_, 1);
                            v_isSharedCheck_2302_ =
                                (!leanh::lean_is_exclusive(v___x_2247_)) as u8;
                            if v_isSharedCheck_2302_ == 0 {
                                v___x_2297_ = v___x_2247_;
                                v_isShared_2298_ = v_isSharedCheck_2302_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_2295_);
                                leanh::lean_inc(v_pos_2294_);
                                leanh::lean_dec(v___x_2247_);
                                v___x_2297_ = leanh::lean_box(0);
                                v_isShared_2298_ = v_isSharedCheck_2302_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_res_2243_);
                        v_pos_2303_ = leanh::lean_ctor_get(v___x_2244_, 0);
                        v_err_2304_ = leanh::lean_ctor_get(v___x_2244_, 1);
                        v_isSharedCheck_2311_ =
                            (!leanh::lean_is_exclusive(v___x_2244_)) as u8;
                        if v_isSharedCheck_2311_ == 0 {
                            v___x_2306_ = v___x_2244_;
                            v_isShared_2307_ = v_isSharedCheck_2311_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_2304_);
                            leanh::lean_inc(v_pos_2303_);
                            leanh::lean_dec(v___x_2244_);
                            v___x_2306_ = leanh::lean_box(0);
                            v_isShared_2307_ = v_isSharedCheck_2311_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_pos_2312_ = leanh::lean_ctor_get(v___x_2241_, 0);
                    v_err_2313_ = leanh::lean_ctor_get(v___x_2241_, 1);
                    v_isSharedCheck_2320_ = (!leanh::lean_is_exclusive(v___x_2241_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2315_ = v___x_2241_;
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2313_);
                        leanh::lean_inc(v_pos_2312_);
                        leanh::lean_dec(v___x_2241_);
                        v___x_2315_ = leanh::lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2253_ = 8;
                v___x_2254_ = (leanh::lean_unbox(v_res_2243_) as u16);
                leanh::lean_dec(v_res_2243_);
                v___x_2255_ = lean_uint16_shift_left(v___x_2254_, v___x_2253_);
                v___x_2256_ = 4;
                v___x_2257_ = (leanh::lean_unbox(v_res_2246_) as u16);
                leanh::lean_dec(v_res_2246_);
                v___x_2258_ = lean_uint16_shift_left(v___x_2257_, v___x_2256_);
                v___x_2259_ = lean_uint16_lor(v___x_2255_, v___x_2258_);
                v___x_2260_ = (leanh::lean_unbox(v_res_2249_) as u16);
                leanh::lean_dec(v_res_2249_);
                v___x_2261_ = lean_uint16_lor(v___x_2259_, v___x_2260_);
                v___x_2262_ = 3072;
                v___x_2263_ = lean_uint16_dec_lt(v___x_2261_, v___x_2262_);
                if v___x_2263_ == 0 {
                    v___x_2264_ = lean_uint16_to_uint32(v_low_2207_);
                    v___x_2265_ = 1023;
                    v___x_2266_ = lean_uint32_land(v___x_2264_, v___x_2265_);
                    v___x_2267_ = 10;
                    v___x_2268_ = lean_uint32_shift_left(v___x_2266_, v___x_2267_);
                    v___x_2269_ = lean_uint16_to_uint32(v___x_2261_);
                    v___x_2270_ = lean_uint32_land(v___x_2269_, v___x_2265_);
                    v___x_2271_ = lean_uint32_lor(v___x_2268_, v___x_2270_);
                    v___x_2272_ = 65536;
                    v___x_2273_ = lean_uint32_add(v___x_2271_, v___x_2272_);
                    v___x_2274_ = lean_uint32_to_nat(v___x_2273_);
                    v___x_2275_ = leanh::lean_unsigned_to_nat(55296);
                    v___x_2276_ = lean_nat_dec_lt(v___x_2274_, v___x_2275_);
                    if v___x_2276_ == 0 {
                        v___x_2277_ = leanh::lean_unsigned_to_nat(57343);
                        v___x_2278_ = lean_nat_dec_lt(v___x_2277_, v___x_2274_);
                        if v___x_2278_ == 0 {
                            leanh::lean_dec(v___x_2274_);
                            leanh::lean_del_object(v___x_2251_);
                            v___y_2210_ = v_pos_2248_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2279_ = leanh::lean_unsigned_to_nat(1114112);
                            v___x_2280_ = lean_nat_dec_lt(v___x_2274_, v___x_2279_);
                            leanh::lean_dec(v___x_2274_);
                            if v___x_2280_ == 0 {
                                leanh::lean_del_object(v___x_2251_);
                                v___y_2210_ = v_pos_2248_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2281_ = leanh::lean_box_uint32(v___x_2273_);
                                if v_isShared_2252_ == 0 {
                                    leanh::lean_ctor_set(v___x_2251_, 1, v___x_2281_);
                                    v___x_2283_ = v___x_2251_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2284_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2284_,
                                        0,
                                        v_pos_2248_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2284_,
                                        1,
                                        v___x_2281_,
                                    );
                                    v___x_2283_ = v_reuseFailAlloc_2284_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2274_);
                        v___x_2285_ = leanh::lean_box_uint32(v___x_2273_);
                        if v_isShared_2252_ == 0 {
                            leanh::lean_ctor_set(v___x_2251_, 1, v___x_2285_);
                            v___x_2287_ = v___x_2251_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2288_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_pos_2248_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2285_);
                            v___x_2287_ = v_reuseFailAlloc_2288_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2289_ = l_Lean_Json_Parser_finishSurrogatePair___closed__1;
                    if v_isShared_2252_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2251_, 1);
                        leanh::lean_ctor_set(v___x_2251_, 1, v___x_2289_);
                        v___x_2291_ = v___x_2251_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2292_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_pos_2248_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 1, v___x_2289_);
                        v___x_2291_ = v_reuseFailAlloc_2292_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2283_;
            }
            7 => {
                return v___x_2287_;
            }
            8 => {
                return v___x_2291_;
            }
            9 => {
                if v_isShared_2298_ == 0 {
                    v___x_2300_ = v___x_2297_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_pos_2294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_err_2295_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2300_;
            }
            11 => {
                if v_isShared_2307_ == 0 {
                    v___x_2309_ = v___x_2306_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_pos_2303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_err_2304_);
                    v___x_2309_ = v_reuseFailAlloc_2310_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2309_;
            }
            13 => {
                if v_isShared_2316_ == 0 {
                    v___x_2318_ = v___x_2315_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_pos_2312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_err_2313_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_finishSurrogatePair___boxed(
    mut v_low_2337_: *mut leanh::LeanObject,
    mut v_a_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_low_boxed_2339_: u16 = 0;
    let mut v_res_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_low_boxed_2339_ = (leanh::lean_unbox(v_low_2337_) as u16);
    v_res_2340_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_2339_, v_a_2338_);
    return v_res_2340_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_2344_: u32 = 0;
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = 65533;
    v___x_2345_ = leanh::lean_box_uint32(v___x_2344_);
    return v___x_2345_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__2()
-> *mut leanh::LeanObject {
    let mut v___x_2346_: u32 = 0;
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ = 9;
    v___x_2347_ = leanh::lean_box_uint32(v___x_2346_);
    return v___x_2347_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__3()
-> *mut leanh::LeanObject {
    let mut v___x_2348_: u32 = 0;
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = 13;
    v___x_2349_ = leanh::lean_box_uint32(v___x_2348_);
    return v___x_2349_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__4()
-> *mut leanh::LeanObject {
    let mut v___x_2350_: u32 = 0;
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ = 10;
    v___x_2351_ = leanh::lean_box_uint32(v___x_2350_);
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__5()
-> *mut leanh::LeanObject {
    let mut v___x_2352_: u32 = 0;
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = 12;
    v___x_2353_ = leanh::lean_box_uint32(v___x_2352_);
    return v___x_2353_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__6()
-> *mut leanh::LeanObject {
    let mut v___x_2354_: u32 = 0;
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2354_ = 8;
    v___x_2355_ = leanh::lean_box_uint32(v___x_2354_);
    return v___x_2355_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__7()
-> *mut leanh::LeanObject {
    let mut v___x_2356_: u32 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2356_ = 47;
    v___x_2357_ = leanh::lean_box_uint32(v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__8()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: u32 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = 34;
    v___x_2359_ = leanh::lean_box_uint32(v___x_2358_);
    return v___x_2359_;
}
pub unsafe fn _init_l_Lean_Json_Parser_escapedChar___boxed__const__9()
-> *mut leanh::LeanObject {
    let mut v___x_2360_: u32 = 0;
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = 92;
    v___x_2361_ = leanh::lean_box_uint32(v___x_2360_);
    return v___x_2361_;
}
pub unsafe fn l_Lean_Json_Parser_escapedChar(
    mut v_a_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v_c_2370_: u32 = 0;
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u32 = 0;
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: u32 = 0;
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: u32 = 0;
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: u32 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: u32 = 0;
    let mut v___x_2383_: u8 = 0;
    let mut v___x_2384_: u32 = 0;
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: u32 = 0;
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: u32 = 0;
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: u32 = 0;
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___y_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u16 = 0;
    let mut v___x_2423_: u16 = 0;
    let mut v___x_2424_: u16 = 0;
    let mut v___x_2425_: u16 = 0;
    let mut v___x_2426_: u16 = 0;
    let mut v___x_2427_: u16 = 0;
    let mut v___x_2428_: u16 = 0;
    let mut v___x_2429_: u16 = 0;
    let mut v___x_2430_: u16 = 0;
    let mut v___x_2431_: u16 = 0;
    let mut v___x_2432_: u16 = 0;
    let mut v___x_2433_: u16 = 0;
    let mut v___x_2434_: u16 = 0;
    let mut v___x_2435_: u16 = 0;
    let mut v___x_2436_: u8 = 0;
    let mut v___x_2437_: u16 = 0;
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: u32 = 0;
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u16 = 0;
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_unused_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u32 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2466_: u8 = 0;
    let mut v_pos_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_pos_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_pos_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2494_: u8 = 0;
    let mut v_pos_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_unused_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2363_ = leanh::lean_ctor_get(v_a_2362_, 0);
                v_snd_2364_ = leanh::lean_ctor_get(v_a_2362_, 1);
                v___x_2365_ = lean_string_utf8_byte_size(v_fst_2363_);
                v___x_2366_ = lean_nat_dec_eq(v_snd_2364_, v___x_2365_);
                if v___x_2366_ == 0 {
                    leanh::lean_inc(v_snd_2364_);
                    leanh::lean_inc(v_fst_2363_);
                    v_isSharedCheck_2521_ = (!leanh::lean_is_exclusive(v_a_2362_)) as u8;
                    if v_isSharedCheck_2521_ == 0 {
                        v_unused_2522_ = leanh::lean_ctor_get(v_a_2362_, 1);
                        leanh::lean_dec(v_unused_2522_);
                        v_unused_2523_ = leanh::lean_ctor_get(v_a_2362_, 0);
                        leanh::lean_dec(v_unused_2523_);
                        v___x_2368_ = v_a_2362_;
                        v_isShared_2369_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2362_);
                        v___x_2368_ = leanh::lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2524_ = leanh::lean_box(0);
                    v___x_2525_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2525_, 0, v_a_2362_);
                    leanh::lean_ctor_set(v___x_2525_, 1, v___x_2524_);
                    return v___x_2525_;
                }
            }
            1 => {
                v_c_2370_ = lean_string_utf8_get_fast(v_fst_2363_, v_snd_2364_);
                v___x_2371_ = lean_string_utf8_next_fast(v_fst_2363_, v_snd_2364_);
                leanh::lean_dec(v_snd_2364_);
                if v_isShared_2369_ == 0 {
                    leanh::lean_ctor_set(v___x_2368_, 1, v___x_2371_);
                    v_it_x27_2373_ = v___x_2368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_fst_2363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2371_);
                    v_it_x27_2373_ = v_reuseFailAlloc_2520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2374_ = 92;
                v___x_2375_ = lean_uint32_dec_eq(v_c_2370_, v___x_2374_);
                if v___x_2375_ == 0 {
                    v___x_2376_ = 34;
                    v___x_2377_ = lean_uint32_dec_eq(v_c_2370_, v___x_2376_);
                    if v___x_2377_ == 0 {
                        v___x_2378_ = 47;
                        v___x_2379_ = lean_uint32_dec_eq(v_c_2370_, v___x_2378_);
                        if v___x_2379_ == 0 {
                            v___x_2380_ = 98;
                            v___x_2381_ = lean_uint32_dec_eq(v_c_2370_, v___x_2380_);
                            if v___x_2381_ == 0 {
                                v___x_2382_ = 102;
                                v___x_2383_ = lean_uint32_dec_eq(v_c_2370_, v___x_2382_);
                                if v___x_2383_ == 0 {
                                    v___x_2384_ = 110;
                                    v___x_2385_ = lean_uint32_dec_eq(v_c_2370_, v___x_2384_);
                                    if v___x_2385_ == 0 {
                                        v___x_2386_ = 114;
                                        v___x_2387_ = lean_uint32_dec_eq(v_c_2370_, v___x_2386_);
                                        if v___x_2387_ == 0 {
                                            v___x_2388_ = 116;
                                            v___x_2389_ =
                                                lean_uint32_dec_eq(v_c_2370_, v___x_2388_);
                                            if v___x_2389_ == 0 {
                                                v___x_2390_ = 117;
                                                v___x_2391_ =
                                                    lean_uint32_dec_eq(v_c_2370_, v___x_2390_);
                                                if v___x_2391_ == 0 {
                                                    v___x_2392_ =
                                                        l_Lean_Json_Parser_escapedChar___closed__1;
                                                    v___x_2393_ = leanh::lean_alloc_ctor(
                                                        1,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_2393_,
                                                        0,
                                                        v_it_x27_2373_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_2393_,
                                                        1,
                                                        v___x_2392_,
                                                    );
                                                    return v___x_2393_;
                                                } else {
                                                    v___x_2394_ =
                                                        l_Lean_Json_Parser_hexChar(v_it_x27_2373_);
                                                    if leanh::lean_obj_tag(v___x_2394_) == 0
                                                    {
                                                        v_pos_2395_ = leanh::lean_ctor_get(
                                                            v___x_2394_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_pos_2395_);
                                                        v_res_2396_ = leanh::lean_ctor_get(
                                                            v___x_2394_,
                                                            1,
                                                        );
                                                        leanh::lean_inc(v_res_2396_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_2394_,
                                                            2,
                                                        );
                                                        v___x_2397_ =
                                                            l_Lean_Json_Parser_hexChar(v_pos_2395_);
                                                        if leanh::lean_obj_tag(v___x_2397_)
                                                            == 0
                                                        {
                                                            v_pos_2398_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2397_,
                                                                    0,
                                                                );
                                                            leanh::lean_inc(v_pos_2398_);
                                                            v_res_2399_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2397_,
                                                                    1,
                                                                );
                                                            leanh::lean_inc(v_res_2399_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_2397_,
                                                                2,
                                                            );
                                                            v___x_2400_ =
                                                                l_Lean_Json_Parser_hexChar(
                                                                    v_pos_2398_,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v___x_2400_,
                                                            ) == 0
                                                            {
                                                                v_pos_2401_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2400_,
                                                                        0,
                                                                    );
                                                                v_res_2402_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2400_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_2476_ = (!leanh::lean_is_exclusive(v___x_2400_)) as u8;
                                                                if v_isSharedCheck_2476_ == 0 {
                                                                    v___x_2404_ = v___x_2400_;
                                                                    v_isShared_2405_ =
                                                                        v_isSharedCheck_2476_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_res_2402_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_pos_2401_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2400_,
                                                                    );
                                                                    v___x_2404_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2405_ =
                                                                        v_isSharedCheck_2476_;
                                                                    state = 3;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(v_res_2399_);
                                                                leanh::lean_dec(v_res_2396_);
                                                                v_pos_2477_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2400_,
                                                                        0,
                                                                    );
                                                                v_err_2478_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2400_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_2485_ = (!leanh::lean_is_exclusive(v___x_2400_)) as u8;
                                                                if v_isSharedCheck_2485_ == 0 {
                                                                    v___x_2480_ = v___x_2400_;
                                                                    v_isShared_2481_ =
                                                                        v_isSharedCheck_2485_;
                                                                    state = 14;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_err_2478_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_pos_2477_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2400_,
                                                                    );
                                                                    v___x_2480_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2481_ =
                                                                        v_isSharedCheck_2485_;
                                                                    state = 14;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_res_2396_);
                                                            v_pos_2486_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2397_,
                                                                    0,
                                                                );
                                                            v_err_2487_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2397_,
                                                                    1,
                                                                );
                                                            v_isSharedCheck_2494_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_2397_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2494_ == 0 {
                                                                v___x_2489_ = v___x_2397_;
                                                                v_isShared_2490_ =
                                                                    v_isSharedCheck_2494_;
                                                                state = 16;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_err_2487_);
                                                                leanh::lean_inc(v_pos_2486_);
                                                                leanh::lean_dec(v___x_2397_);
                                                                v___x_2489_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_2490_ =
                                                                    v_isSharedCheck_2494_;
                                                                state = 16;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        v_pos_2495_ = leanh::lean_ctor_get(
                                                            v___x_2394_,
                                                            0,
                                                        );
                                                        v_err_2496_ = leanh::lean_ctor_get(
                                                            v___x_2394_,
                                                            1,
                                                        );
                                                        v_isSharedCheck_2503_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_2394_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2503_ == 0 {
                                                            v___x_2498_ = v___x_2394_;
                                                            v_isShared_2499_ =
                                                                v_isSharedCheck_2503_;
                                                            state = 18;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_err_2496_);
                                                            leanh::lean_inc(v_pos_2495_);
                                                            leanh::lean_dec(v___x_2394_);
                                                            v___x_2498_ = leanh::lean_box(0);
                                                            v_isShared_2499_ =
                                                                v_isSharedCheck_2503_;
                                                            state = 18;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                v___x_2504_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
                                                v___x_2505_ =
                                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_2505_,
                                                    0,
                                                    v_it_x27_2373_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_2505_,
                                                    1,
                                                    v___x_2504_,
                                                );
                                                return v___x_2505_;
                                            }
                                        } else {
                                            v___x_2506_ =
                                                l_Lean_Json_Parser_escapedChar___boxed__const__3;
                                            v___x_2507_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_2507_,
                                                0,
                                                v_it_x27_2373_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_2507_,
                                                1,
                                                v___x_2506_,
                                            );
                                            return v___x_2507_;
                                        }
                                    } else {
                                        v___x_2508_ =
                                            l_Lean_Json_Parser_escapedChar___boxed__const__4;
                                        v___x_2509_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2509_, 0, v_it_x27_2373_);
                                        leanh::lean_ctor_set(v___x_2509_, 1, v___x_2508_);
                                        return v___x_2509_;
                                    }
                                } else {
                                    v___x_2510_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
                                    v___x_2511_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2511_, 0, v_it_x27_2373_);
                                    leanh::lean_ctor_set(v___x_2511_, 1, v___x_2510_);
                                    return v___x_2511_;
                                }
                            } else {
                                v___x_2512_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
                                v___x_2513_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2513_, 0, v_it_x27_2373_);
                                leanh::lean_ctor_set(v___x_2513_, 1, v___x_2512_);
                                return v___x_2513_;
                            }
                        } else {
                            v___x_2514_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
                            v___x_2515_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2515_, 0, v_it_x27_2373_);
                            leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
                            return v___x_2515_;
                        }
                    } else {
                        v___x_2516_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
                        v___x_2517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2517_, 0, v_it_x27_2373_);
                        leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
                        return v___x_2517_;
                    }
                } else {
                    v___x_2518_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
                    v___x_2519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2519_, 0, v_it_x27_2373_);
                    leanh::lean_ctor_set(v___x_2519_, 1, v___x_2518_);
                    return v___x_2519_;
                }
            }
            3 => {
                v___x_2406_ = l_Lean_Json_Parser_hexChar(v_pos_2401_);
                if leanh::lean_obj_tag(v___x_2406_) == 0 {
                    v_pos_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    v_res_2408_ = leanh::lean_ctor_get(v___x_2406_, 1);
                    v_isSharedCheck_2466_ = (!leanh::lean_is_exclusive(v___x_2406_)) as u8;
                    if v_isSharedCheck_2466_ == 0 {
                        v___x_2410_ = v___x_2406_;
                        v_isShared_2411_ = v_isSharedCheck_2466_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_2408_);
                        leanh::lean_inc(v_pos_2407_);
                        leanh::lean_dec(v___x_2406_);
                        v___x_2410_ = leanh::lean_box(0);
                        v_isShared_2411_ = v_isSharedCheck_2466_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2404_);
                    leanh::lean_dec(v_res_2402_);
                    leanh::lean_dec(v_res_2399_);
                    leanh::lean_dec(v_res_2396_);
                    v_pos_2467_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    v_err_2468_ = leanh::lean_ctor_get(v___x_2406_, 1);
                    v_isSharedCheck_2475_ = (!leanh::lean_is_exclusive(v___x_2406_)) as u8;
                    if v_isSharedCheck_2475_ == 0 {
                        v___x_2470_ = v___x_2406_;
                        v_isShared_2471_ = v_isSharedCheck_2475_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2468_);
                        leanh::lean_inc(v_pos_2467_);
                        leanh::lean_dec(v___x_2406_);
                        v___x_2470_ = leanh::lean_box(0);
                        v_isShared_2471_ = v_isSharedCheck_2475_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2422_ = 12;
                v___x_2423_ = (leanh::lean_unbox(v_res_2396_) as u16);
                leanh::lean_dec(v_res_2396_);
                v___x_2424_ = lean_uint16_shift_left(v___x_2423_, v___x_2422_);
                v___x_2425_ = 8;
                v___x_2426_ = (leanh::lean_unbox(v_res_2399_) as u16);
                leanh::lean_dec(v_res_2399_);
                v___x_2427_ = lean_uint16_shift_left(v___x_2426_, v___x_2425_);
                v___x_2428_ = lean_uint16_lor(v___x_2424_, v___x_2427_);
                v___x_2429_ = 4;
                v___x_2430_ = (leanh::lean_unbox(v_res_2402_) as u16);
                leanh::lean_dec(v_res_2402_);
                v___x_2431_ = lean_uint16_shift_left(v___x_2430_, v___x_2429_);
                v___x_2432_ = lean_uint16_lor(v___x_2428_, v___x_2431_);
                v___x_2433_ = (leanh::lean_unbox(v_res_2408_) as u16);
                leanh::lean_dec(v_res_2408_);
                v___x_2434_ = lean_uint16_lor(v___x_2432_, v___x_2433_);
                v___x_2435_ = 55296;
                v___x_2436_ = lean_uint16_dec_lt(v___x_2434_, v___x_2435_);
                if v___x_2436_ == 0 {
                    v___x_2437_ = 57344;
                    v___x_2438_ = lean_uint16_dec_lt(v___x_2434_, v___x_2437_);
                    if v___x_2438_ == 0 {
                        leanh::lean_del_object(v___x_2410_);
                        v___x_2439_ = lean_uint16_to_uint32(v___x_2434_);
                        v___x_2440_ = leanh::lean_box_uint32(v___x_2439_);
                        if v_isShared_2405_ == 0 {
                            leanh::lean_ctor_set(v___x_2404_, 1, v___x_2440_);
                            leanh::lean_ctor_set(v___x_2404_, 0, v_pos_2407_);
                            v___x_2442_ = v___x_2404_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2443_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_pos_2407_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2440_);
                            v___x_2442_ = v_reuseFailAlloc_2443_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_2444_ = 56320;
                        v___x_2445_ = lean_uint16_dec_lt(v___x_2434_, v___x_2444_);
                        if v___x_2445_ == 0 {
                            leanh::lean_del_object(v___x_2410_);
                            v___x_2446_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
                            if v_isShared_2405_ == 0 {
                                leanh::lean_ctor_set(v___x_2404_, 1, v___x_2446_);
                                leanh::lean_ctor_set(v___x_2404_, 0, v_pos_2407_);
                                v___x_2448_ = v___x_2404_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_2449_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_pos_2407_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2446_);
                                v___x_2448_ = v_reuseFailAlloc_2449_;
                                state = 8;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2404_);
                            leanh::lean_inc(v_pos_2407_);
                            v___x_2450_ =
                                l_Lean_Json_Parser_finishSurrogatePair(v___x_2434_, v_pos_2407_);
                            if leanh::lean_obj_tag(v___x_2450_) == 0 {
                                if leanh::lean_obj_tag(v___x_2450_) == 0 {
                                    leanh::lean_del_object(v___x_2410_);
                                    leanh::lean_dec(v_pos_2407_);
                                    return v___x_2450_;
                                } else {
                                    v_pos_2451_ = leanh::lean_ctor_get(v___x_2450_, 0);
                                    leanh::lean_inc(v_pos_2451_);
                                    v___y_2413_ = v___x_2450_;
                                    v_pos_2414_ = v_pos_2451_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_err_2452_ = leanh::lean_ctor_get(v___x_2450_, 1);
                                v_isSharedCheck_2459_ =
                                    (!leanh::lean_is_exclusive(v___x_2450_)) as u8;
                                if v_isSharedCheck_2459_ == 0 {
                                    v_unused_2460_ = leanh::lean_ctor_get(v___x_2450_, 0);
                                    leanh::lean_dec(v_unused_2460_);
                                    v___x_2454_ = v___x_2450_;
                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_err_2452_);
                                    leanh::lean_dec(v___x_2450_);
                                    v___x_2454_ = leanh::lean_box(0);
                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2410_);
                    v___x_2461_ = lean_uint16_to_uint32(v___x_2434_);
                    v___x_2462_ = leanh::lean_box_uint32(v___x_2461_);
                    if v_isShared_2405_ == 0 {
                        leanh::lean_ctor_set(v___x_2404_, 1, v___x_2462_);
                        leanh::lean_ctor_set(v___x_2404_, 0, v_pos_2407_);
                        v___x_2464_ = v___x_2404_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2465_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_pos_2407_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2462_);
                        v___x_2464_ = v_reuseFailAlloc_2465_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_2415_ = leanh::lean_ctor_get(v_pos_2407_, 1);
                leanh::lean_inc(v_snd_2415_);
                leanh::lean_dec(v_pos_2407_);
                v_snd_2416_ = leanh::lean_ctor_get(v_pos_2414_, 1);
                v___x_2417_ = lean_nat_dec_eq(v_snd_2415_, v_snd_2416_);
                leanh::lean_dec(v_snd_2415_);
                if v___x_2417_ == 0 {
                    leanh::lean_dec_ref(v_pos_2414_);
                    leanh::lean_del_object(v___x_2410_);
                    return v___y_2413_;
                } else {
                    leanh::lean_dec_ref(v___y_2413_);
                    v___x_2418_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
                    if v_isShared_2411_ == 0 {
                        leanh::lean_ctor_set(v___x_2410_, 1, v___x_2418_);
                        leanh::lean_ctor_set(v___x_2410_, 0, v_pos_2414_);
                        v___x_2420_ = v___x_2410_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_pos_2414_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2421_, 1, v___x_2418_);
                        v___x_2420_ = v_reuseFailAlloc_2421_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2420_;
            }
            7 => {
                return v___x_2442_;
            }
            8 => {
                return v___x_2448_;
            }
            9 => {
                leanh::lean_inc(v_pos_2407_);
                if v_isShared_2455_ == 0 {
                    leanh::lean_ctor_set(v___x_2454_, 0, v_pos_2407_);
                    v___x_2457_ = v___x_2454_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_pos_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_err_2452_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc(v_pos_2407_);
                v___y_2413_ = v___x_2457_;
                v_pos_2414_ = v_pos_2407_;
                state = 5;
                continue;
            }
            11 => {
                return v___x_2464_;
            }
            12 => {
                if v_isShared_2471_ == 0 {
                    v___x_2473_ = v___x_2470_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_pos_2467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_err_2468_);
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2473_;
            }
            14 => {
                if v_isShared_2481_ == 0 {
                    v___x_2483_ = v___x_2480_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_pos_2477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_err_2478_);
                    v___x_2483_ = v_reuseFailAlloc_2484_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2483_;
            }
            16 => {
                if v_isShared_2490_ == 0 {
                    v___x_2492_ = v___x_2489_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_pos_2486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_err_2487_);
                    v___x_2492_ = v_reuseFailAlloc_2493_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2492_;
            }
            18 => {
                if v_isShared_2499_ == 0 {
                    v___x_2501_ = v___x_2498_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_pos_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_err_2496_);
                    v___x_2501_ = v_reuseFailAlloc_2502_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_strCore(
    mut v_acc_2529_: *mut leanh::LeanObject,
    mut v_a_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2538_: u32 = 0;
    let mut v___x_2539_: u32 = 0;
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u32 = 0;
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: u32 = 0;
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: u32 = 0;
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u32 = 0;
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_reuseFailAlloc_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_unused_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2531_ = leanh::lean_ctor_get(v_a_2530_, 0);
                v_snd_2532_ = leanh::lean_ctor_get(v_a_2530_, 1);
                v___x_2533_ = lean_string_utf8_byte_size(v_fst_2531_);
                v___x_2534_ = lean_nat_dec_eq(v_snd_2532_, v___x_2533_);
                if v___x_2534_ == 0 {
                    leanh::lean_inc(v_snd_2532_);
                    leanh::lean_inc(v_fst_2531_);
                    v_isSharedCheck_2577_ = (!leanh::lean_is_exclusive(v_a_2530_)) as u8;
                    if v_isSharedCheck_2577_ == 0 {
                        v_unused_2578_ = leanh::lean_ctor_get(v_a_2530_, 1);
                        leanh::lean_dec(v_unused_2578_);
                        v_unused_2579_ = leanh::lean_ctor_get(v_a_2530_, 0);
                        leanh::lean_dec(v_unused_2579_);
                        v___x_2536_ = v_a_2530_;
                        v_isShared_2537_ = v_isSharedCheck_2577_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2530_);
                        v___x_2536_ = leanh::lean_box(0);
                        v_isShared_2537_ = v_isSharedCheck_2577_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_acc_2529_);
                    v___x_2580_ = leanh::lean_box(0);
                    v___x_2581_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2581_, 0, v_a_2530_);
                    leanh::lean_ctor_set(v___x_2581_, 1, v___x_2580_);
                    return v___x_2581_;
                }
            }
            1 => {
                v___x_2538_ = lean_string_utf8_get_fast(v_fst_2531_, v_snd_2532_);
                v___x_2539_ = 34;
                v___x_2540_ = lean_uint32_dec_eq(v___x_2538_, v___x_2539_);
                if v___x_2540_ == 0 {
                    v___x_2541_ = lean_string_utf8_next_fast(v_fst_2531_, v_snd_2532_);
                    leanh::lean_dec(v_snd_2532_);
                    if v_isShared_2537_ == 0 {
                        leanh::lean_ctor_set(v___x_2536_, 1, v___x_2541_);
                        v___x_2543_ = v___x_2536_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_fst_2531_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 1, v___x_2541_);
                        v___x_2543_ = v_reuseFailAlloc_2571_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2572_ = lean_string_utf8_next_fast(v_fst_2531_, v_snd_2532_);
                    leanh::lean_dec(v_snd_2532_);
                    if v_isShared_2537_ == 0 {
                        leanh::lean_ctor_set(v___x_2536_, 1, v___x_2572_);
                        v___x_2574_ = v___x_2536_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2531_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2572_);
                        v___x_2574_ = v_reuseFailAlloc_2576_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2550_ = 92;
                v___x_2551_ = lean_uint32_dec_eq(v___x_2538_, v___x_2550_);
                if v___x_2551_ == 0 {
                    v___x_2552_ = 32;
                    v___x_2553_ = lean_uint32_dec_le(v___x_2552_, v___x_2538_);
                    if v___x_2553_ == 0 {
                        v___y_2545_ = v___x_2553_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2554_ = 1114111;
                        v___x_2555_ = lean_uint32_dec_le(v___x_2538_, v___x_2554_);
                        v___y_2545_ = v___x_2555_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2556_ = l_Lean_Json_Parser_escapedChar(v___x_2543_);
                    if leanh::lean_obj_tag(v___x_2556_) == 0 {
                        v_pos_2557_ = leanh::lean_ctor_get(v___x_2556_, 0);
                        leanh::lean_inc(v_pos_2557_);
                        v_res_2558_ = leanh::lean_ctor_get(v___x_2556_, 1);
                        leanh::lean_inc(v_res_2558_);
                        leanh::lean_dec_ref_known(v___x_2556_, 2);
                        v___x_2559_ = leanh::lean_unbox_uint32(v_res_2558_);
                        leanh::lean_dec(v_res_2558_);
                        v___x_2560_ = lean_string_push(v_acc_2529_, v___x_2559_);
                        v_acc_2529_ = v___x_2560_;
                        v_a_2530_ = v_pos_2557_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_acc_2529_);
                        v_pos_2562_ = leanh::lean_ctor_get(v___x_2556_, 0);
                        v_err_2563_ = leanh::lean_ctor_get(v___x_2556_, 1);
                        v_isSharedCheck_2570_ =
                            (!leanh::lean_is_exclusive(v___x_2556_)) as u8;
                        if v_isSharedCheck_2570_ == 0 {
                            v___x_2565_ = v___x_2556_;
                            v_isShared_2566_ = v_isSharedCheck_2570_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_2563_);
                            leanh::lean_inc(v_pos_2562_);
                            leanh::lean_dec(v___x_2556_);
                            v___x_2565_ = leanh::lean_box(0);
                            v_isShared_2566_ = v_isSharedCheck_2570_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v___y_2545_ == 0 {
                    leanh::lean_dec_ref(v_acc_2529_);
                    v___x_2546_ = l_Lean_Json_Parser_strCore___closed__1;
                    v___x_2547_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2547_, 0, v___x_2543_);
                    leanh::lean_ctor_set(v___x_2547_, 1, v___x_2546_);
                    return v___x_2547_;
                } else {
                    v___x_2548_ = lean_string_push(v_acc_2529_, v___x_2538_);
                    v_acc_2529_ = v___x_2548_;
                    v_a_2530_ = v___x_2543_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_pos_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_err_2563_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2568_;
            }
            6 => {
                v___x_2575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                leanh::lean_ctor_set(v___x_2575_, 1, v_acc_2529_);
                return v___x_2575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_str(
    mut v_a_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2583_ = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
    v___x_2584_ = l_Lean_Json_Parser_strCore(v___x_2583_, v_a_2582_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_Json_Parser_natCore(
    mut v_acc_2585_: *mut leanh::LeanObject,
    mut v_a_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: u32 = 0;
    let mut v___x_2592_: u32 = 0;
    let mut v___y_2594_: u8 = 0;
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u32 = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_unused_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: u32 = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2587_ = leanh::lean_ctor_get(v_a_2586_, 0);
                v_snd_2588_ = leanh::lean_ctor_get(v_a_2586_, 1);
                v___x_2589_ = lean_string_utf8_byte_size(v_fst_2587_);
                v___x_2590_ = lean_nat_dec_eq(v_snd_2588_, v___x_2589_);
                if v___x_2590_ == 0 {
                    v___x_2591_ = lean_string_utf8_get_fast(v_fst_2587_, v_snd_2588_);
                    v___x_2592_ = 48;
                    v___x_2612_ = lean_uint32_dec_le(v___x_2592_, v___x_2591_);
                    if v___x_2612_ == 0 {
                        v___y_2594_ = v___x_2612_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2613_ = 57;
                        v___x_2614_ = lean_uint32_dec_le(v___x_2591_, v___x_2613_);
                        v___y_2594_ = v___x_2614_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2615_, 0, v_a_2586_);
                    leanh::lean_ctor_set(v___x_2615_, 1, v_acc_2585_);
                    return v___x_2615_;
                }
            }
            1 => {
                if v___y_2594_ == 0 {
                    v___x_2595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2595_, 0, v_a_2586_);
                    leanh::lean_ctor_set(v___x_2595_, 1, v_acc_2585_);
                    return v___x_2595_;
                } else {
                    leanh::lean_inc(v_snd_2588_);
                    leanh::lean_inc(v_fst_2587_);
                    v_isSharedCheck_2609_ = (!leanh::lean_is_exclusive(v_a_2586_)) as u8;
                    if v_isSharedCheck_2609_ == 0 {
                        v_unused_2610_ = leanh::lean_ctor_get(v_a_2586_, 1);
                        leanh::lean_dec(v_unused_2610_);
                        v_unused_2611_ = leanh::lean_ctor_get(v_a_2586_, 0);
                        leanh::lean_dec(v_unused_2611_);
                        v___x_2597_ = v_a_2586_;
                        v_isShared_2598_ = v_isSharedCheck_2609_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2586_);
                        v___x_2597_ = leanh::lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2609_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2599_ = lean_string_utf8_next_fast(v_fst_2587_, v_snd_2588_);
                leanh::lean_dec(v_snd_2588_);
                if v_isShared_2598_ == 0 {
                    leanh::lean_ctor_set(v___x_2597_, 1, v___x_2599_);
                    v___x_2601_ = v___x_2597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_fst_2587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2599_);
                    v___x_2601_ = v_reuseFailAlloc_2608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2602_ = leanh::lean_unsigned_to_nat(10);
                v___x_2603_ = lean_nat_mul(v___x_2602_, v_acc_2585_);
                leanh::lean_dec(v_acc_2585_);
                v___x_2604_ = lean_uint32_sub(v___x_2591_, v___x_2592_);
                v___x_2605_ = lean_uint32_to_nat(v___x_2604_);
                v___x_2606_ = lean_nat_add(v___x_2603_, v___x_2605_);
                leanh::lean_dec(v___x_2605_);
                leanh::lean_dec(v___x_2603_);
                v_acc_2585_ = v___x_2606_;
                v_a_2586_ = v___x_2601_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_natCoreNumDigits(
    mut v_acc_2616_: *mut leanh::LeanObject,
    mut v_digits_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: u32 = 0;
    let mut v___x_2624_: u32 = 0;
    let mut v___y_2626_: u8 = 0;
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u32 = 0;
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_unused_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: u32 = 0;
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2619_ = leanh::lean_ctor_get(v_a_2618_, 0);
                v_snd_2620_ = leanh::lean_ctor_get(v_a_2618_, 1);
                v___x_2621_ = lean_string_utf8_byte_size(v_fst_2619_);
                v___x_2622_ = lean_nat_dec_eq(v_snd_2620_, v___x_2621_);
                if v___x_2622_ == 0 {
                    v___x_2623_ = lean_string_utf8_get_fast(v_fst_2619_, v_snd_2620_);
                    v___x_2624_ = 48;
                    v___x_2647_ = lean_uint32_dec_le(v___x_2624_, v___x_2623_);
                    if v___x_2647_ == 0 {
                        v___y_2626_ = v___x_2647_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2648_ = 57;
                        v___x_2649_ = lean_uint32_dec_le(v___x_2623_, v___x_2648_);
                        v___y_2626_ = v___x_2649_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2650_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2650_, 0, v_acc_2616_);
                    leanh::lean_ctor_set(v___x_2650_, 1, v_digits_2617_);
                    v___x_2651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2651_, 0, v_a_2618_);
                    leanh::lean_ctor_set(v___x_2651_, 1, v___x_2650_);
                    return v___x_2651_;
                }
            }
            1 => {
                if v___y_2626_ == 0 {
                    v___x_2627_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2627_, 0, v_acc_2616_);
                    leanh::lean_ctor_set(v___x_2627_, 1, v_digits_2617_);
                    v___x_2628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2628_, 0, v_a_2618_);
                    leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                    return v___x_2628_;
                } else {
                    leanh::lean_inc(v_snd_2620_);
                    leanh::lean_inc(v_fst_2619_);
                    v_isSharedCheck_2644_ = (!leanh::lean_is_exclusive(v_a_2618_)) as u8;
                    if v_isSharedCheck_2644_ == 0 {
                        v_unused_2645_ = leanh::lean_ctor_get(v_a_2618_, 1);
                        leanh::lean_dec(v_unused_2645_);
                        v_unused_2646_ = leanh::lean_ctor_get(v_a_2618_, 0);
                        leanh::lean_dec(v_unused_2646_);
                        v___x_2630_ = v_a_2618_;
                        v_isShared_2631_ = v_isSharedCheck_2644_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2618_);
                        v___x_2630_ = leanh::lean_box(0);
                        v_isShared_2631_ = v_isSharedCheck_2644_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2632_ = lean_string_utf8_next_fast(v_fst_2619_, v_snd_2620_);
                leanh::lean_dec(v_snd_2620_);
                if v_isShared_2631_ == 0 {
                    leanh::lean_ctor_set(v___x_2630_, 1, v___x_2632_);
                    v___x_2634_ = v___x_2630_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_fst_2619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2632_);
                    v___x_2634_ = v_reuseFailAlloc_2643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2635_ = leanh::lean_unsigned_to_nat(10);
                v___x_2636_ = lean_nat_mul(v___x_2635_, v_acc_2616_);
                leanh::lean_dec(v_acc_2616_);
                v___x_2637_ = lean_uint32_sub(v___x_2623_, v___x_2624_);
                v___x_2638_ = lean_uint32_to_nat(v___x_2637_);
                v___x_2639_ = lean_nat_add(v___x_2636_, v___x_2638_);
                leanh::lean_dec(v___x_2638_);
                leanh::lean_dec(v___x_2636_);
                v___x_2640_ = leanh::lean_unsigned_to_nat(1);
                v___x_2641_ = lean_nat_add(v_digits_2617_, v___x_2640_);
                leanh::lean_dec(v_digits_2617_);
                v_acc_2616_ = v___x_2639_;
                v_digits_2617_ = v___x_2641_;
                v_a_2618_ = v___x_2634_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_lookahead___redArg(
    mut v_desc_2653_: *mut leanh::LeanObject,
    mut v_inst_2654_: *mut leanh::LeanObject,
    mut v_a_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    v_fst_2656_ = leanh::lean_ctor_get(v_a_2655_, 0);
    v_snd_2657_ = leanh::lean_ctor_get(v_a_2655_, 1);
    v___x_2658_ = lean_string_utf8_byte_size(v_fst_2656_);
    v___x_2659_ = lean_nat_dec_eq(v_snd_2657_, v___x_2658_);
    if v___x_2659_ == 0 {
        let mut v___x_2660_: u32 = 0;
        let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2663_: u8 = 0;
        v___x_2660_ = lean_string_utf8_get_fast(v_fst_2656_, v_snd_2657_);
        v___x_2661_ = leanh::lean_box_uint32(v___x_2660_);
        v___x_2662_ = leanh::lean_apply_1(v_inst_2654_, v___x_2661_);
        v___x_2663_ = (leanh::lean_unbox(v___x_2662_) as u8);
        if v___x_2663_ == 0 {
            let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2664_ = l_Lean_Json_Parser_lookahead___redArg___closed__0;
            v___x_2665_ = lean_string_append(v___x_2664_, v_desc_2653_);
            v___x_2666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2666_, 0, v___x_2665_);
            v___x_2667_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2667_, 0, v_a_2655_);
            leanh::lean_ctor_set(v___x_2667_, 1, v___x_2666_);
            return v___x_2667_;
        } else {
            let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2668_ = leanh::lean_box(0);
            v___x_2669_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2669_, 0, v_a_2655_);
            leanh::lean_ctor_set(v___x_2669_, 1, v___x_2668_);
            return v___x_2669_;
        }
    } else {
        let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2654_);
        v___x_2670_ = leanh::lean_box(0);
        v___x_2671_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2671_, 0, v_a_2655_);
        leanh::lean_ctor_set(v___x_2671_, 1, v___x_2670_);
        return v___x_2671_;
    }
}
pub unsafe fn l_Lean_Json_Parser_lookahead___redArg___boxed(
    mut v_desc_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_2672_, v_inst_2673_, v_a_2674_);
    leanh::lean_dec_ref(v_desc_2672_);
    return v_res_2675_;
}
pub unsafe fn l_Lean_Json_Parser_lookahead(
    mut v_p_2676_: *mut leanh::LeanObject,
    mut v_desc_2677_: *mut leanh::LeanObject,
    mut v_inst_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    v_fst_2680_ = leanh::lean_ctor_get(v_a_2679_, 0);
    v_snd_2681_ = leanh::lean_ctor_get(v_a_2679_, 1);
    v___x_2682_ = lean_string_utf8_byte_size(v_fst_2680_);
    v___x_2683_ = lean_nat_dec_eq(v_snd_2681_, v___x_2682_);
    if v___x_2683_ == 0 {
        let mut v___x_2684_: u32 = 0;
        let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2687_: u8 = 0;
        v___x_2684_ = lean_string_utf8_get_fast(v_fst_2680_, v_snd_2681_);
        v___x_2685_ = leanh::lean_box_uint32(v___x_2684_);
        v___x_2686_ = leanh::lean_apply_1(v_inst_2678_, v___x_2685_);
        v___x_2687_ = (leanh::lean_unbox(v___x_2686_) as u8);
        if v___x_2687_ == 0 {
            let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2688_ = l_Lean_Json_Parser_lookahead___redArg___closed__0;
            v___x_2689_ = lean_string_append(v___x_2688_, v_desc_2677_);
            v___x_2690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2690_, 0, v___x_2689_);
            v___x_2691_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2691_, 0, v_a_2679_);
            leanh::lean_ctor_set(v___x_2691_, 1, v___x_2690_);
            return v___x_2691_;
        } else {
            let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2692_ = leanh::lean_box(0);
            v___x_2693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2693_, 0, v_a_2679_);
            leanh::lean_ctor_set(v___x_2693_, 1, v___x_2692_);
            return v___x_2693_;
        }
    } else {
        let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2678_);
        v___x_2694_ = leanh::lean_box(0);
        v___x_2695_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2695_, 0, v_a_2679_);
        leanh::lean_ctor_set(v___x_2695_, 1, v___x_2694_);
        return v___x_2695_;
    }
}
pub unsafe fn l_Lean_Json_Parser_lookahead___boxed(
    mut v_p_2696_: *mut leanh::LeanObject,
    mut v_desc_2697_: *mut leanh::LeanObject,
    mut v_inst_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2700_ = l_Lean_Json_Parser_lookahead(v_p_2696_, v_desc_2697_, v_inst_2698_, v_a_2699_);
    leanh::lean_dec_ref(v_desc_2697_);
    return v_res_2700_;
}
pub unsafe fn l_Lean_Json_Parser_natNonZero(
    mut v_a_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2706_: u8 = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: u32 = 0;
    let mut v___x_2716_: u32 = 0;
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: u32 = 0;
    let mut v___x_2719_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2711_ = leanh::lean_ctor_get(v_a_2704_, 0);
                v_snd_2712_ = leanh::lean_ctor_get(v_a_2704_, 1);
                v___x_2713_ = lean_string_utf8_byte_size(v_fst_2711_);
                v___x_2714_ = lean_nat_dec_eq(v_snd_2712_, v___x_2713_);
                if v___x_2714_ == 0 {
                    v___x_2715_ = lean_string_utf8_get_fast(v_fst_2711_, v_snd_2712_);
                    v___x_2716_ = 49;
                    v___x_2717_ = lean_uint32_dec_le(v___x_2716_, v___x_2715_);
                    if v___x_2717_ == 0 {
                        v___y_2706_ = v___x_2717_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2718_ = 57;
                        v___x_2719_ = lean_uint32_dec_le(v___x_2715_, v___x_2718_);
                        v___y_2706_ = v___x_2719_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2720_ = leanh::lean_box(0);
                    v___x_2721_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2721_, 0, v_a_2704_);
                    leanh::lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                    return v___x_2721_;
                }
            }
            1 => {
                if v___y_2706_ == 0 {
                    v___x_2707_ = l_Lean_Json_Parser_natNonZero___closed__1;
                    v___x_2708_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2708_, 0, v_a_2704_);
                    leanh::lean_ctor_set(v___x_2708_, 1, v___x_2707_);
                    return v___x_2708_;
                } else {
                    v___x_2709_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2710_ = l_Lean_Json_Parser_natCore(v___x_2709_, v_a_2704_);
                    return v___x_2710_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_natNumDigits(
    mut v_a_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2727_: u8 = 0;
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: u32 = 0;
    let mut v___x_2737_: u32 = 0;
    let mut v___x_2738_: u8 = 0;
    let mut v___x_2739_: u32 = 0;
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2732_ = leanh::lean_ctor_get(v_a_2725_, 0);
                v_snd_2733_ = leanh::lean_ctor_get(v_a_2725_, 1);
                v___x_2734_ = lean_string_utf8_byte_size(v_fst_2732_);
                v___x_2735_ = lean_nat_dec_eq(v_snd_2733_, v___x_2734_);
                if v___x_2735_ == 0 {
                    v___x_2736_ = lean_string_utf8_get_fast(v_fst_2732_, v_snd_2733_);
                    v___x_2737_ = 48;
                    v___x_2738_ = lean_uint32_dec_le(v___x_2737_, v___x_2736_);
                    if v___x_2738_ == 0 {
                        v___y_2727_ = v___x_2738_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2739_ = 57;
                        v___x_2740_ = lean_uint32_dec_le(v___x_2736_, v___x_2739_);
                        v___y_2727_ = v___x_2740_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2741_ = leanh::lean_box(0);
                    v___x_2742_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2742_, 0, v_a_2725_);
                    leanh::lean_ctor_set(v___x_2742_, 1, v___x_2741_);
                    return v___x_2742_;
                }
            }
            1 => {
                if v___y_2727_ == 0 {
                    v___x_2728_ = l_Lean_Json_Parser_natNumDigits___closed__1;
                    v___x_2729_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2729_, 0, v_a_2725_);
                    leanh::lean_ctor_set(v___x_2729_, 1, v___x_2728_);
                    return v___x_2729_;
                } else {
                    v___x_2730_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2731_ =
                        l_Lean_Json_Parser_natCoreNumDigits(v___x_2730_, v___x_2730_, v_a_2725_);
                    return v___x_2731_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_natMaybeZero(
    mut v_a_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2748_: u8 = 0;
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: u32 = 0;
    let mut v___x_2758_: u32 = 0;
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: u32 = 0;
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2753_ = leanh::lean_ctor_get(v_a_2746_, 0);
                v_snd_2754_ = leanh::lean_ctor_get(v_a_2746_, 1);
                v___x_2755_ = lean_string_utf8_byte_size(v_fst_2753_);
                v___x_2756_ = lean_nat_dec_eq(v_snd_2754_, v___x_2755_);
                if v___x_2756_ == 0 {
                    v___x_2757_ = lean_string_utf8_get_fast(v_fst_2753_, v_snd_2754_);
                    v___x_2758_ = 48;
                    v___x_2759_ = lean_uint32_dec_le(v___x_2758_, v___x_2757_);
                    if v___x_2759_ == 0 {
                        v___y_2748_ = v___x_2759_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2760_ = 57;
                        v___x_2761_ = lean_uint32_dec_le(v___x_2757_, v___x_2760_);
                        v___y_2748_ = v___x_2761_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2762_ = leanh::lean_box(0);
                    v___x_2763_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2763_, 0, v_a_2746_);
                    leanh::lean_ctor_set(v___x_2763_, 1, v___x_2762_);
                    return v___x_2763_;
                }
            }
            1 => {
                if v___y_2748_ == 0 {
                    v___x_2749_ = l_Lean_Json_Parser_natMaybeZero___closed__1;
                    v___x_2750_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2750_, 0, v_a_2746_);
                    leanh::lean_ctor_set(v___x_2750_, 1, v___x_2749_);
                    return v___x_2750_;
                } else {
                    v___x_2751_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2752_ = l_Lean_Json_Parser_natCore(v___x_2751_, v_a_2746_);
                    return v___x_2752_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Json_Parser_numSign___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = leanh::lean_unsigned_to_nat(1);
    v___x_2765_ = lean_nat_to_int(v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn _init_l_Lean_Json_Parser_numSign___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0_once),
        _init_l_Lean_Json_Parser_numSign___closed__0,
    );
    v___x_2767_ = lean_int_neg(v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_Lean_Json_Parser_numSign(
    mut v_a_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: u32 = 0;
    let mut v___x_2774_: u32 = 0;
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2769_ = leanh::lean_ctor_get(v_a_2768_, 0);
                v_snd_2770_ = leanh::lean_ctor_get(v_a_2768_, 1);
                v___x_2771_ = lean_string_utf8_byte_size(v_fst_2769_);
                v___x_2772_ = lean_nat_dec_eq(v_snd_2770_, v___x_2771_);
                if v___x_2772_ == 0 {
                    v___x_2773_ = lean_string_utf8_get_fast(v_fst_2769_, v_snd_2770_);
                    v___x_2774_ = 45;
                    v___x_2775_ = lean_uint32_dec_eq(v___x_2773_, v___x_2774_);
                    if v___x_2775_ == 0 {
                        v___x_2776_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0_once),
                            _init_l_Lean_Json_Parser_numSign___closed__0,
                        );
                        v___x_2777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2777_, 0, v_a_2768_);
                        leanh::lean_ctor_set(v___x_2777_, 1, v___x_2776_);
                        return v___x_2777_;
                    } else {
                        leanh::lean_inc(v_snd_2770_);
                        leanh::lean_inc(v_fst_2769_);
                        v_isSharedCheck_2787_ = (!leanh::lean_is_exclusive(v_a_2768_)) as u8;
                        if v_isSharedCheck_2787_ == 0 {
                            v_unused_2788_ = leanh::lean_ctor_get(v_a_2768_, 1);
                            leanh::lean_dec(v_unused_2788_);
                            v_unused_2789_ = leanh::lean_ctor_get(v_a_2768_, 0);
                            leanh::lean_dec(v_unused_2789_);
                            v___x_2779_ = v_a_2768_;
                            v_isShared_2780_ = v_isSharedCheck_2787_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2768_);
                            v___x_2779_ = leanh::lean_box(0);
                            v_isShared_2780_ = v_isSharedCheck_2787_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2790_ = leanh::lean_box(0);
                    v___x_2791_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2791_, 0, v_a_2768_);
                    leanh::lean_ctor_set(v___x_2791_, 1, v___x_2790_);
                    return v___x_2791_;
                }
            }
            1 => {
                v___x_2781_ = lean_string_utf8_next_fast(v_fst_2769_, v_snd_2770_);
                leanh::lean_dec(v_snd_2770_);
                if v_isShared_2780_ == 0 {
                    leanh::lean_ctor_set(v___x_2779_, 1, v___x_2781_);
                    v___x_2783_ = v___x_2779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_fst_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2781_);
                    v___x_2783_ = v_reuseFailAlloc_2786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2784_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1_once),
                    _init_l_Lean_Json_Parser_numSign___closed__1,
                );
                v___x_2785_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2785_, 0, v___x_2783_);
                leanh::lean_ctor_set(v___x_2785_, 1, v___x_2784_);
                return v___x_2785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_nat(
    mut v_a_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2794_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: u32 = 0;
    let mut v___x_2804_: u32 = 0;
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: u32 = 0;
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: u32 = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut v_unused_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2799_ = leanh::lean_ctor_get(v_a_2792_, 0);
                v_snd_2800_ = leanh::lean_ctor_get(v_a_2792_, 1);
                v___x_2801_ = lean_string_utf8_byte_size(v_fst_2799_);
                v___x_2802_ = lean_nat_dec_eq(v_snd_2800_, v___x_2801_);
                if v___x_2802_ == 0 {
                    v___x_2803_ = lean_string_utf8_get_fast(v_fst_2799_, v_snd_2800_);
                    v___x_2804_ = 48;
                    v___x_2805_ = lean_uint32_dec_eq(v___x_2803_, v___x_2804_);
                    if v___x_2805_ == 0 {
                        v___x_2806_ = 49;
                        v___x_2807_ = lean_uint32_dec_le(v___x_2806_, v___x_2803_);
                        if v___x_2807_ == 0 {
                            v___y_2794_ = v___x_2807_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2808_ = 57;
                            v___x_2809_ = lean_uint32_dec_le(v___x_2803_, v___x_2808_);
                            v___y_2794_ = v___x_2809_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_snd_2800_);
                        leanh::lean_inc(v_fst_2799_);
                        v_isSharedCheck_2819_ = (!leanh::lean_is_exclusive(v_a_2792_)) as u8;
                        if v_isSharedCheck_2819_ == 0 {
                            v_unused_2820_ = leanh::lean_ctor_get(v_a_2792_, 1);
                            leanh::lean_dec(v_unused_2820_);
                            v_unused_2821_ = leanh::lean_ctor_get(v_a_2792_, 0);
                            leanh::lean_dec(v_unused_2821_);
                            v___x_2811_ = v_a_2792_;
                            v_isShared_2812_ = v_isSharedCheck_2819_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2792_);
                            v___x_2811_ = leanh::lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2819_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2822_ = leanh::lean_box(0);
                    v___x_2823_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2823_, 0, v_a_2792_);
                    leanh::lean_ctor_set(v___x_2823_, 1, v___x_2822_);
                    return v___x_2823_;
                }
            }
            1 => {
                if v___y_2794_ == 0 {
                    v___x_2795_ = l_Lean_Json_Parser_natNonZero___closed__1;
                    v___x_2796_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2796_, 0, v_a_2792_);
                    leanh::lean_ctor_set(v___x_2796_, 1, v___x_2795_);
                    return v___x_2796_;
                } else {
                    v___x_2797_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2798_ = l_Lean_Json_Parser_natCore(v___x_2797_, v_a_2792_);
                    return v___x_2798_;
                }
            }
            2 => {
                v___x_2813_ = lean_string_utf8_next_fast(v_fst_2799_, v_snd_2800_);
                leanh::lean_dec(v_snd_2800_);
                if v_isShared_2812_ == 0 {
                    leanh::lean_ctor_set(v___x_2811_, 1, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_fst_2799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2813_);
                    v___x_2815_ = v_reuseFailAlloc_2818_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2816_ = leanh::lean_unsigned_to_nat(0);
                v___x_2817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2817_, 0, v___x_2815_);
                leanh::lean_ctor_set(v___x_2817_, 1, v___x_2816_);
                return v___x_2817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Json_Parser_numWithDecimals___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_System_Platform_numBits;
    v___x_2825_ = leanh::lean_unsigned_to_nat(2);
    v___x_2826_ = lean_nat_pow(v___x_2825_, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn l_Lean_Json_Parser_numWithDecimals(
    mut v_a_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v_fst_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2849_: u8 = 0;
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_pos_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v___y_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: u32 = 0;
    let mut v___x_2894_: u32 = 0;
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: u32 = 0;
    let mut v___x_2904_: u32 = 0;
    let mut v___x_2905_: u8 = 0;
    let mut v___x_2906_: u32 = 0;
    let mut v___x_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_pos_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v___x_2940_: u32 = 0;
    let mut v___x_2941_: u32 = 0;
    let mut v___x_2942_: u8 = 0;
    let mut v___x_2943_: u32 = 0;
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: u32 = 0;
    let mut v___x_2946_: u8 = 0;
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2956_: u32 = 0;
    let mut v___x_2957_: u32 = 0;
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2962_: u8 = 0;
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2952_ = leanh::lean_ctor_get(v_a_2830_, 0);
                v_snd_2953_ = leanh::lean_ctor_get(v_a_2830_, 1);
                v___x_2954_ = lean_string_utf8_byte_size(v_fst_2952_);
                v___x_2955_ = lean_nat_dec_eq(v_snd_2953_, v___x_2954_);
                if v___x_2955_ == 0 {
                    leanh::lean_inc(v_snd_2953_);
                    leanh::lean_inc(v_fst_2952_);
                    v___x_2956_ = lean_string_utf8_get_fast(v_fst_2952_, v_snd_2953_);
                    v___x_2957_ = 45;
                    v___x_2958_ = lean_uint32_dec_eq(v___x_2956_, v___x_2957_);
                    if v___x_2958_ == 0 {
                        v___x_2959_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0_once),
                            _init_l_Lean_Json_Parser_numSign___closed__0,
                        );
                        v_pos_2934_ = v_a_2830_;
                        v_fst_2935_ = v_fst_2952_;
                        v_snd_2936_ = v_snd_2953_;
                        v_res_2937_ = v___x_2959_;
                        state = 14;
                        continue;
                    } else {
                        v_isSharedCheck_2968_ = (!leanh::lean_is_exclusive(v_a_2830_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v_unused_2969_ = leanh::lean_ctor_get(v_a_2830_, 1);
                            leanh::lean_dec(v_unused_2969_);
                            v_unused_2970_ = leanh::lean_ctor_get(v_a_2830_, 0);
                            leanh::lean_dec(v_unused_2970_);
                            v___x_2961_ = v_a_2830_;
                            v_isShared_2962_ = v_isSharedCheck_2968_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2830_);
                            v___x_2961_ = leanh::lean_box(0);
                            v_isShared_2962_ = v_isSharedCheck_2968_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v___x_2971_ = leanh::lean_box(0);
                    v___x_2972_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2972_, 0, v_a_2830_);
                    leanh::lean_ctor_set(v___x_2972_, 1, v___x_2971_);
                    return v___x_2972_;
                }
            }
            1 => {
                if v___y_2835_ == 0 {
                    leanh::lean_dec(v___y_2832_);
                    v___x_2836_ = l_Lean_Json_Parser_natNumDigits___closed__1;
                    v___x_2837_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2837_, 0, v___y_2833_);
                    leanh::lean_ctor_set(v___x_2837_, 1, v___x_2836_);
                    return v___x_2837_;
                } else {
                    v___x_2838_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2839_ =
                        l_Lean_Json_Parser_natCoreNumDigits(v___x_2838_, v___x_2838_, v___y_2833_);
                    if leanh::lean_obj_tag(v___x_2839_) == 0 {
                        v_res_2840_ = leanh::lean_ctor_get(v___x_2839_, 1);
                        v_pos_2841_ = leanh::lean_ctor_get(v___x_2839_, 0);
                        v_isSharedCheck_2871_ =
                            (!leanh::lean_is_exclusive(v___x_2839_)) as u8;
                        if v_isSharedCheck_2871_ == 0 {
                            v___x_2843_ = v___x_2839_;
                            v_isShared_2844_ = v_isSharedCheck_2871_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_2840_);
                            leanh::lean_inc(v_pos_2841_);
                            leanh::lean_dec(v___x_2839_);
                            v___x_2843_ = leanh::lean_box(0);
                            v_isShared_2844_ = v_isSharedCheck_2871_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_2832_);
                        v_pos_2872_ = leanh::lean_ctor_get(v___x_2839_, 0);
                        v_err_2873_ = leanh::lean_ctor_get(v___x_2839_, 1);
                        v_isSharedCheck_2880_ =
                            (!leanh::lean_is_exclusive(v___x_2839_)) as u8;
                        if v_isSharedCheck_2880_ == 0 {
                            v___x_2875_ = v___x_2839_;
                            v_isShared_2876_ = v_isSharedCheck_2880_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_2873_);
                            leanh::lean_inc(v_pos_2872_);
                            leanh::lean_dec(v___x_2839_);
                            v___x_2875_ = leanh::lean_box(0);
                            v_isShared_2876_ = v_isSharedCheck_2880_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_fst_2845_ = leanh::lean_ctor_get(v_res_2840_, 0);
                v_snd_2846_ = leanh::lean_ctor_get(v_res_2840_, 1);
                v_isSharedCheck_2870_ = (!leanh::lean_is_exclusive(v_res_2840_)) as u8;
                if v_isSharedCheck_2870_ == 0 {
                    v___x_2848_ = v_res_2840_;
                    v_isShared_2849_ = v_isSharedCheck_2870_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2846_);
                    leanh::lean_inc(v_fst_2845_);
                    leanh::lean_dec(v_res_2840_);
                    v___x_2848_ = leanh::lean_box(0);
                    v_isShared_2849_ = v_isSharedCheck_2870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2850_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0_once),
                    _init_l_Lean_Json_Parser_numWithDecimals___closed__0,
                );
                v___x_2851_ = lean_nat_dec_lt(v___x_2850_, v_snd_2846_);
                if v___x_2851_ == 0 {
                    v___x_2852_ = lean_nat_to_int(v___y_2832_);
                    v___x_2853_ = leanh::lean_unsigned_to_nat(10);
                    v___x_2854_ = lean_nat_pow(v___x_2853_, v_snd_2846_);
                    v___x_2855_ = lean_nat_to_int(v___x_2854_);
                    v___x_2856_ = lean_int_mul(v___x_2852_, v___x_2855_);
                    leanh::lean_dec(v___x_2855_);
                    leanh::lean_dec(v___x_2852_);
                    v___x_2857_ = lean_nat_to_int(v_fst_2845_);
                    v___x_2858_ = lean_int_add(v___x_2856_, v___x_2857_);
                    leanh::lean_dec(v___x_2857_);
                    leanh::lean_dec(v___x_2856_);
                    v___x_2859_ = lean_int_mul(v___y_2834_, v___x_2858_);
                    leanh::lean_dec(v___x_2858_);
                    if v_isShared_2849_ == 0 {
                        leanh::lean_ctor_set(v___x_2848_, 0, v___x_2859_);
                        v___x_2861_ = v___x_2848_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2865_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2859_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_snd_2846_);
                        v___x_2861_ = v_reuseFailAlloc_2865_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2848_);
                    leanh::lean_dec(v_snd_2846_);
                    leanh::lean_dec(v_fst_2845_);
                    leanh::lean_dec(v___y_2832_);
                    v___x_2866_ = l_Lean_Json_Parser_numWithDecimals___closed__2;
                    if v_isShared_2844_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2843_, 1);
                        leanh::lean_ctor_set(v___x_2843_, 1, v___x_2866_);
                        v___x_2868_ = v___x_2843_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2869_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_pos_2841_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___x_2866_);
                        v___x_2868_ = v_reuseFailAlloc_2869_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2844_ == 0 {
                    leanh::lean_ctor_set(v___x_2843_, 1, v___x_2861_);
                    v___x_2863_ = v___x_2843_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_pos_2841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2863_;
            }
            6 => {
                return v___x_2868_;
            }
            7 => {
                if v_isShared_2876_ == 0 {
                    v___x_2878_ = v___x_2875_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2879_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_pos_2872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_err_2873_);
                    v___x_2878_ = v_reuseFailAlloc_2879_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2878_;
            }
            9 => {
                v___x_2883_ = leanh::lean_box(0);
                v___x_2884_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2884_, 0, v___y_2882_);
                leanh::lean_ctor_set(v___x_2884_, 1, v___x_2883_);
                return v___x_2884_;
            }
            10 => {
                v___x_2891_ = lean_string_utf8_byte_size(v_fst_2888_);
                v___x_2892_ = lean_nat_dec_eq(v_snd_2889_, v___x_2891_);
                if v___x_2892_ == 0 {
                    v___x_2893_ = lean_string_utf8_get_fast(v_fst_2888_, v_snd_2889_);
                    v___x_2894_ = 46;
                    v___x_2895_ = lean_uint32_dec_eq(v___x_2893_, v___x_2894_);
                    if v___x_2895_ == 0 {
                        leanh::lean_dec(v_snd_2889_);
                        leanh::lean_dec(v_fst_2888_);
                        v___x_2896_ = lean_nat_to_int(v_res_2890_);
                        v___x_2897_ = lean_int_mul(v___y_2886_, v___x_2896_);
                        leanh::lean_dec(v___x_2896_);
                        v___x_2898_ = l_Lean_JsonNumber_fromInt(v___x_2897_);
                        v___x_2899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2899_, 0, v_pos_2887_);
                        leanh::lean_ctor_set(v___x_2899_, 1, v___x_2898_);
                        return v___x_2899_;
                    } else {
                        leanh::lean_dec_ref(v_pos_2887_);
                        v___x_2900_ = lean_string_utf8_next_fast(v_fst_2888_, v_snd_2889_);
                        leanh::lean_dec(v_snd_2889_);
                        leanh::lean_inc(v_fst_2888_);
                        v___x_2901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2901_, 0, v_fst_2888_);
                        leanh::lean_ctor_set(v___x_2901_, 1, v___x_2900_);
                        v___x_2902_ = lean_nat_dec_eq(v___x_2900_, v___x_2891_);
                        if v___x_2902_ == 0 {
                            if v___x_2895_ == 0 {
                                leanh::lean_dec(v_res_2890_);
                                leanh::lean_dec(v_fst_2888_);
                                v___y_2882_ = v___x_2901_;
                                state = 9;
                                continue;
                            } else {
                                v___x_2903_ = lean_string_utf8_get_fast(v_fst_2888_, v___x_2900_);
                                leanh::lean_dec(v_fst_2888_);
                                v___x_2904_ = 48;
                                v___x_2905_ = lean_uint32_dec_le(v___x_2904_, v___x_2903_);
                                if v___x_2905_ == 0 {
                                    v___y_2832_ = v_res_2890_;
                                    v___y_2833_ = v___x_2901_;
                                    v___y_2834_ = v___y_2886_;
                                    v___y_2835_ = v___x_2905_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2906_ = 57;
                                    v___x_2907_ = lean_uint32_dec_le(v___x_2903_, v___x_2906_);
                                    v___y_2832_ = v_res_2890_;
                                    v___y_2833_ = v___x_2901_;
                                    v___y_2834_ = v___y_2886_;
                                    v___y_2835_ = v___x_2907_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_res_2890_);
                            leanh::lean_dec(v_fst_2888_);
                            v___y_2882_ = v___x_2901_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_2889_);
                    leanh::lean_dec(v_fst_2888_);
                    v___x_2908_ = lean_nat_to_int(v_res_2890_);
                    v___x_2909_ = lean_int_mul(v___y_2886_, v___x_2908_);
                    leanh::lean_dec(v___x_2908_);
                    v___x_2910_ = l_Lean_JsonNumber_fromInt(v___x_2909_);
                    v___x_2911_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2911_, 0, v_pos_2887_);
                    leanh::lean_ctor_set(v___x_2911_, 1, v___x_2910_);
                    return v___x_2911_;
                }
            }
            11 => {
                if v___y_2915_ == 0 {
                    v___x_2916_ = l_Lean_Json_Parser_natNonZero___closed__1;
                    v___x_2917_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2917_, 0, v___y_2913_);
                    leanh::lean_ctor_set(v___x_2917_, 1, v___x_2916_);
                    return v___x_2917_;
                } else {
                    v___x_2918_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2919_ = l_Lean_Json_Parser_natCore(v___x_2918_, v___y_2913_);
                    if leanh::lean_obj_tag(v___x_2919_) == 0 {
                        v_pos_2920_ = leanh::lean_ctor_get(v___x_2919_, 0);
                        leanh::lean_inc(v_pos_2920_);
                        v_res_2921_ = leanh::lean_ctor_get(v___x_2919_, 1);
                        leanh::lean_inc(v_res_2921_);
                        leanh::lean_dec_ref_known(v___x_2919_, 2);
                        v_fst_2922_ = leanh::lean_ctor_get(v_pos_2920_, 0);
                        leanh::lean_inc(v_fst_2922_);
                        v_snd_2923_ = leanh::lean_ctor_get(v_pos_2920_, 1);
                        leanh::lean_inc(v_snd_2923_);
                        v___y_2886_ = v___y_2914_;
                        v_pos_2887_ = v_pos_2920_;
                        v_fst_2888_ = v_fst_2922_;
                        v_snd_2889_ = v_snd_2923_;
                        v_res_2890_ = v_res_2921_;
                        state = 10;
                        continue;
                    } else {
                        v_pos_2924_ = leanh::lean_ctor_get(v___x_2919_, 0);
                        v_err_2925_ = leanh::lean_ctor_get(v___x_2919_, 1);
                        v_isSharedCheck_2932_ =
                            (!leanh::lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2932_ == 0 {
                            v___x_2927_ = v___x_2919_;
                            v_isShared_2928_ = v_isSharedCheck_2932_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_2925_);
                            leanh::lean_inc(v_pos_2924_);
                            leanh::lean_dec(v___x_2919_);
                            v___x_2927_ = leanh::lean_box(0);
                            v_isShared_2928_ = v_isSharedCheck_2932_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_2928_ == 0 {
                    v___x_2930_ = v___x_2927_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_pos_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_err_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2930_;
            }
            14 => {
                v___x_2938_ = lean_string_utf8_byte_size(v_fst_2935_);
                v___x_2939_ = lean_nat_dec_eq(v_snd_2936_, v___x_2938_);
                if v___x_2939_ == 0 {
                    v___x_2940_ = lean_string_utf8_get_fast(v_fst_2935_, v_snd_2936_);
                    v___x_2941_ = 48;
                    v___x_2942_ = lean_uint32_dec_eq(v___x_2940_, v___x_2941_);
                    if v___x_2942_ == 0 {
                        leanh::lean_dec(v_snd_2936_);
                        leanh::lean_dec(v_fst_2935_);
                        v___x_2943_ = 49;
                        v___x_2944_ = lean_uint32_dec_le(v___x_2943_, v___x_2940_);
                        if v___x_2944_ == 0 {
                            v___y_2913_ = v_pos_2934_;
                            v___y_2914_ = v_res_2937_;
                            v___y_2915_ = v___x_2944_;
                            state = 11;
                            continue;
                        } else {
                            v___x_2945_ = 57;
                            v___x_2946_ = lean_uint32_dec_le(v___x_2940_, v___x_2945_);
                            v___y_2913_ = v_pos_2934_;
                            v___y_2914_ = v_res_2937_;
                            v___y_2915_ = v___x_2946_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_pos_2934_);
                        v___x_2947_ = lean_string_utf8_next_fast(v_fst_2935_, v_snd_2936_);
                        leanh::lean_dec(v_snd_2936_);
                        leanh::lean_inc(v_fst_2935_);
                        v___x_2948_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2948_, 0, v_fst_2935_);
                        leanh::lean_ctor_set(v___x_2948_, 1, v___x_2947_);
                        v___x_2949_ = leanh::lean_unsigned_to_nat(0);
                        v___y_2886_ = v_res_2937_;
                        v_pos_2887_ = v___x_2948_;
                        v_fst_2888_ = v_fst_2935_;
                        v_snd_2889_ = v___x_2947_;
                        v_res_2890_ = v___x_2949_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_2936_);
                    leanh::lean_dec(v_fst_2935_);
                    v___x_2950_ = leanh::lean_box(0);
                    v___x_2951_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2951_, 0, v_pos_2934_);
                    leanh::lean_ctor_set(v___x_2951_, 1, v___x_2950_);
                    return v___x_2951_;
                }
            }
            15 => {
                v___x_2963_ = lean_string_utf8_next_fast(v_fst_2952_, v_snd_2953_);
                leanh::lean_dec(v_snd_2953_);
                leanh::lean_inc(v_fst_2952_);
                if v_isShared_2962_ == 0 {
                    leanh::lean_ctor_set(v___x_2961_, 1, v___x_2963_);
                    v___x_2965_ = v___x_2961_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_fst_2952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2963_);
                    v___x_2965_ = v_reuseFailAlloc_2967_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2966_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1_once),
                    _init_l_Lean_Json_Parser_numSign___closed__1,
                );
                v_pos_2934_ = v___x_2965_;
                v_fst_2935_ = v_fst_2952_;
                v_snd_2936_ = v___x_2963_;
                v_res_2937_ = v___x_2966_;
                state = 14;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_exponent(
    mut v_value_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2984_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_pos_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v___y_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v_pos_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v___y_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: u32 = 0;
    let mut v___x_3047_: u32 = 0;
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3049_: u32 = 0;
    let mut v___x_3050_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u8 = 0;
    let mut v___x_3065_: u32 = 0;
    let mut v___x_3066_: u32 = 0;
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: u32 = 0;
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3075_: u32 = 0;
    let mut v___x_3076_: u32 = 0;
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: u32 = 0;
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_unused_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3090_: u32 = 0;
    let mut v___x_3091_: u32 = 0;
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: u32 = 0;
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3053_ = leanh::lean_ctor_get(v_a_2977_, 0);
                v_snd_3054_ = leanh::lean_ctor_get(v_a_2977_, 1);
                v___x_3088_ = lean_string_utf8_byte_size(v_fst_3053_);
                v___x_3089_ = lean_nat_dec_eq(v_snd_3054_, v___x_3088_);
                if v___x_3089_ == 0 {
                    v___x_3090_ = lean_string_utf8_get_fast(v_fst_3053_, v_snd_3054_);
                    v___x_3091_ = 101;
                    v___x_3092_ = lean_uint32_dec_eq(v___x_3090_, v___x_3091_);
                    if v___x_3092_ == 0 {
                        v___x_3093_ = 69;
                        v___x_3094_ = lean_uint32_dec_eq(v___x_3090_, v___x_3093_);
                        if v___x_3094_ == 0 {
                            v___x_3095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3095_, 0, v_a_2977_);
                            leanh::lean_ctor_set(v___x_3095_, 1, v_value_2976_);
                            return v___x_3095_;
                        } else {
                            state = 14;
                            continue;
                        }
                    } else {
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_3096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3096_, 0, v_a_2977_);
                    leanh::lean_ctor_set(v___x_3096_, 1, v_value_2976_);
                    return v___x_3096_;
                }
            }
            1 => {
                v___x_2980_ = leanh::lean_box(0);
                v___x_2981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2981_, 0, v___y_2979_);
                leanh::lean_ctor_set(v___x_2981_, 1, v___x_2980_);
                return v___x_2981_;
            }
            2 => {
                if v___y_2984_ == 0 {
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_2985_ = l_Lean_Json_Parser_natMaybeZero___closed__1;
                    v___x_2986_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2986_, 0, v___y_2983_);
                    leanh::lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                    return v___x_2986_;
                } else {
                    v___x_2987_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2988_ = l_Lean_Json_Parser_natCore(v___x_2987_, v___y_2983_);
                    if leanh::lean_obj_tag(v___x_2988_) == 0 {
                        v_pos_2989_ = leanh::lean_ctor_get(v___x_2988_, 0);
                        v_res_2990_ = leanh::lean_ctor_get(v___x_2988_, 1);
                        v_isSharedCheck_2998_ =
                            (!leanh::lean_is_exclusive(v___x_2988_)) as u8;
                        if v_isSharedCheck_2998_ == 0 {
                            v___x_2992_ = v___x_2988_;
                            v_isShared_2993_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_2990_);
                            leanh::lean_inc(v_pos_2989_);
                            leanh::lean_dec(v___x_2988_);
                            v___x_2992_ = leanh::lean_box(0);
                            v_isShared_2993_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_value_2976_);
                        v_pos_2999_ = leanh::lean_ctor_get(v___x_2988_, 0);
                        v_err_3000_ = leanh::lean_ctor_get(v___x_2988_, 1);
                        v_isSharedCheck_3007_ =
                            (!leanh::lean_is_exclusive(v___x_2988_)) as u8;
                        if v_isSharedCheck_3007_ == 0 {
                            v___x_3002_ = v___x_2988_;
                            v_isShared_3003_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3000_);
                            leanh::lean_inc(v_pos_2999_);
                            leanh::lean_dec(v___x_2988_);
                            v___x_3002_ = leanh::lean_box(0);
                            v_isShared_3003_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2994_ = l_Lean_JsonNumber_shiftr(v_value_2976_, v_res_2990_);
                leanh::lean_dec(v_res_2990_);
                if v_isShared_2993_ == 0 {
                    leanh::lean_ctor_set(v___x_2992_, 1, v___x_2994_);
                    v___x_2996_ = v___x_2992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2997_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_pos_2989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2994_);
                    v___x_2996_ = v_reuseFailAlloc_2997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2996_;
            }
            5 => {
                if v_isShared_3003_ == 0 {
                    v___x_3005_ = v___x_3002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_pos_2999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_err_3000_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3005_;
            }
            7 => {
                if v___y_3010_ == 0 {
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_3011_ = l_Lean_Json_Parser_natMaybeZero___closed__1;
                    v___x_3012_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3012_, 0, v___y_3009_);
                    leanh::lean_ctor_set(v___x_3012_, 1, v___x_3011_);
                    return v___x_3012_;
                } else {
                    v___x_3013_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3014_ = l_Lean_Json_Parser_natCore(v___x_3013_, v___y_3009_);
                    if leanh::lean_obj_tag(v___x_3014_) == 0 {
                        v_pos_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        v_res_3016_ = leanh::lean_ctor_get(v___x_3014_, 1);
                        v_isSharedCheck_3030_ =
                            (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                        if v_isSharedCheck_3030_ == 0 {
                            v___x_3018_ = v___x_3014_;
                            v_isShared_3019_ = v_isSharedCheck_3030_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_3016_);
                            leanh::lean_inc(v_pos_3015_);
                            leanh::lean_dec(v___x_3014_);
                            v___x_3018_ = leanh::lean_box(0);
                            v_isShared_3019_ = v_isSharedCheck_3030_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_value_2976_);
                        v_pos_3031_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        v_err_3032_ = leanh::lean_ctor_get(v___x_3014_, 1);
                        v_isSharedCheck_3039_ =
                            (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                        if v_isSharedCheck_3039_ == 0 {
                            v___x_3034_ = v___x_3014_;
                            v_isShared_3035_ = v_isSharedCheck_3039_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3032_);
                            leanh::lean_inc(v_pos_3031_);
                            leanh::lean_dec(v___x_3014_);
                            v___x_3034_ = leanh::lean_box(0);
                            v_isShared_3035_ = v_isSharedCheck_3039_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_3020_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0_once),
                    _init_l_Lean_Json_Parser_numWithDecimals___closed__0,
                );
                v___x_3021_ = lean_nat_dec_lt(v___x_3020_, v_res_3016_);
                if v___x_3021_ == 0 {
                    v___x_3022_ = l_Lean_JsonNumber_shiftl(v_value_2976_, v_res_3016_);
                    leanh::lean_dec(v_res_3016_);
                    if v_isShared_3019_ == 0 {
                        leanh::lean_ctor_set(v___x_3018_, 1, v___x_3022_);
                        v___x_3024_ = v___x_3018_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_pos_3015_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3022_);
                        v___x_3024_ = v_reuseFailAlloc_3025_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_res_3016_);
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_3026_ = l_Lean_Json_Parser_exponent___closed__1;
                    if v_isShared_3019_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3018_, 1);
                        leanh::lean_ctor_set(v___x_3018_, 1, v___x_3026_);
                        v___x_3028_ = v___x_3018_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3029_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_pos_3015_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3026_);
                        v___x_3028_ = v_reuseFailAlloc_3029_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_3024_;
            }
            10 => {
                return v___x_3028_;
            }
            11 => {
                if v_isShared_3035_ == 0 {
                    v___x_3037_ = v___x_3034_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_pos_3031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_err_3032_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3037_;
            }
            13 => {
                v___x_3044_ = lean_string_utf8_byte_size(v_fst_3042_);
                v___x_3045_ = lean_nat_dec_eq(v_snd_3043_, v___x_3044_);
                if v___x_3045_ == 0 {
                    v___x_3046_ = lean_string_utf8_get_fast(v_fst_3042_, v_snd_3043_);
                    leanh::lean_dec(v_snd_3043_);
                    leanh::lean_dec(v_fst_3042_);
                    v___x_3047_ = 48;
                    v___x_3048_ = lean_uint32_dec_le(v___x_3047_, v___x_3046_);
                    if v___x_3048_ == 0 {
                        v___y_3009_ = v___y_3041_;
                        v___y_3010_ = v___x_3048_;
                        state = 7;
                        continue;
                    } else {
                        v___x_3049_ = 57;
                        v___x_3050_ = lean_uint32_dec_le(v___x_3046_, v___x_3049_);
                        v___y_3009_ = v___y_3041_;
                        v___y_3010_ = v___x_3050_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3043_);
                    leanh::lean_dec(v_fst_3042_);
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_3051_ = leanh::lean_box(0);
                    v___x_3052_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3052_, 0, v___y_3041_);
                    leanh::lean_ctor_set(v___x_3052_, 1, v___x_3051_);
                    return v___x_3052_;
                }
            }
            14 => {
                v___x_3056_ = lean_string_utf8_byte_size(v_fst_3053_);
                v___x_3057_ = lean_nat_dec_eq(v_snd_3054_, v___x_3056_);
                if v___x_3057_ == 0 {
                    leanh::lean_inc(v_snd_3054_);
                    leanh::lean_inc(v_fst_3053_);
                    v_isSharedCheck_3083_ = (!leanh::lean_is_exclusive(v_a_2977_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v_unused_3084_ = leanh::lean_ctor_get(v_a_2977_, 1);
                        leanh::lean_dec(v_unused_3084_);
                        v_unused_3085_ = leanh::lean_ctor_get(v_a_2977_, 0);
                        leanh::lean_dec(v_unused_3085_);
                        v___x_3059_ = v_a_2977_;
                        v_isShared_3060_ = v_isSharedCheck_3083_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2977_);
                        v___x_3059_ = leanh::lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3083_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_3086_ = leanh::lean_box(0);
                    v___x_3087_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3087_, 0, v_a_2977_);
                    leanh::lean_ctor_set(v___x_3087_, 1, v___x_3086_);
                    return v___x_3087_;
                }
            }
            15 => {
                v___x_3061_ = lean_string_utf8_next_fast(v_fst_3053_, v_snd_3054_);
                leanh::lean_dec(v_snd_3054_);
                leanh::lean_inc(v_fst_3053_);
                if v_isShared_3060_ == 0 {
                    leanh::lean_ctor_set(v___x_3059_, 1, v___x_3061_);
                    v___x_3063_ = v___x_3059_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_fst_3053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 1, v___x_3061_);
                    v___x_3063_ = v_reuseFailAlloc_3082_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3064_ = lean_nat_dec_eq(v___x_3061_, v___x_3056_);
                if v___x_3064_ == 0 {
                    v___x_3065_ = lean_string_utf8_get_fast(v_fst_3053_, v___x_3061_);
                    v___x_3066_ = 45;
                    v___x_3067_ = lean_uint32_dec_eq(v___x_3065_, v___x_3066_);
                    if v___x_3067_ == 0 {
                        v___x_3068_ = 43;
                        v___x_3069_ = lean_uint32_dec_eq(v___x_3065_, v___x_3068_);
                        if v___x_3069_ == 0 {
                            v___y_3041_ = v___x_3063_;
                            v_fst_3042_ = v_fst_3053_;
                            v_snd_3043_ = v___x_3061_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_3063_);
                            v___x_3070_ = lean_string_utf8_next_fast(v_fst_3053_, v___x_3061_);
                            leanh::lean_inc(v_fst_3053_);
                            v___x_3071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3071_, 0, v_fst_3053_);
                            leanh::lean_ctor_set(v___x_3071_, 1, v___x_3070_);
                            v___y_3041_ = v___x_3071_;
                            v_fst_3042_ = v_fst_3053_;
                            v_snd_3043_ = v___x_3070_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3063_);
                        v___x_3072_ = lean_string_utf8_next_fast(v_fst_3053_, v___x_3061_);
                        leanh::lean_inc(v_fst_3053_);
                        v___x_3073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3073_, 0, v_fst_3053_);
                        leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                        v___x_3074_ = lean_nat_dec_eq(v___x_3072_, v___x_3056_);
                        if v___x_3074_ == 0 {
                            if v___x_3067_ == 0 {
                                leanh::lean_dec(v_fst_3053_);
                                leanh::lean_dec_ref(v_value_2976_);
                                v___y_2979_ = v___x_3073_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3075_ = lean_string_utf8_get_fast(v_fst_3053_, v___x_3072_);
                                leanh::lean_dec(v_fst_3053_);
                                v___x_3076_ = 48;
                                v___x_3077_ = lean_uint32_dec_le(v___x_3076_, v___x_3075_);
                                if v___x_3077_ == 0 {
                                    v___y_2983_ = v___x_3073_;
                                    v___y_2984_ = v___x_3077_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3078_ = 57;
                                    v___x_3079_ = lean_uint32_dec_le(v___x_3075_, v___x_3078_);
                                    v___y_2983_ = v___x_3073_;
                                    v___y_2984_ = v___x_3079_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_fst_3053_);
                            leanh::lean_dec_ref(v_value_2976_);
                            v___y_2979_ = v___x_3073_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_3053_);
                    leanh::lean_dec_ref(v_value_2976_);
                    v___x_3080_ = leanh::lean_box(0);
                    v___x_3081_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3081_, 0, v___x_3063_);
                    leanh::lean_ctor_set(v___x_3081_, 1, v___x_3080_);
                    return v___x_3081_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(
    mut v_a_3097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3098_ = lean_nat_to_int(v_a_3097_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_Json_Parser_num(
    mut v_a_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3103_: u8 = 0;
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_pos_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v___y_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: u32 = 0;
    let mut v___x_3141_: u32 = 0;
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: u32 = 0;
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: u8 = 0;
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_pos_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v___y_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: u32 = 0;
    let mut v___x_3189_: u32 = 0;
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: u32 = 0;
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: u32 = 0;
    let mut v___x_3199_: u32 = 0;
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: u32 = 0;
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: u32 = 0;
    let mut v___x_3216_: u32 = 0;
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: u32 = 0;
    let mut v___x_3219_: u8 = 0;
    let mut v___y_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v_fst_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v_pos_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v___y_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: u32 = 0;
    let mut v___x_3285_: u32 = 0;
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: u32 = 0;
    let mut v___x_3295_: u32 = 0;
    let mut v___x_3296_: u8 = 0;
    let mut v___x_3297_: u32 = 0;
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3306_: u8 = 0;
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_pos_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u32 = 0;
    let mut v___x_3332_: u32 = 0;
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: u32 = 0;
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: u32 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: u32 = 0;
    let mut v___x_3348_: u32 = 0;
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_unused_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3343_ = leanh::lean_ctor_get(v_a_3099_, 0);
                v_snd_3344_ = leanh::lean_ctor_get(v_a_3099_, 1);
                v___x_3345_ = lean_string_utf8_byte_size(v_fst_3343_);
                v___x_3346_ = lean_nat_dec_eq(v_snd_3344_, v___x_3345_);
                if v___x_3346_ == 0 {
                    leanh::lean_inc(v_snd_3344_);
                    leanh::lean_inc(v_fst_3343_);
                    v___x_3347_ = lean_string_utf8_get_fast(v_fst_3343_, v_snd_3344_);
                    v___x_3348_ = 45;
                    v___x_3349_ = lean_uint32_dec_eq(v___x_3347_, v___x_3348_);
                    if v___x_3349_ == 0 {
                        v___x_3350_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__0_once),
                            _init_l_Lean_Json_Parser_numSign___closed__0,
                        );
                        v_pos_3325_ = v_a_3099_;
                        v_fst_3326_ = v_fst_3343_;
                        v_snd_3327_ = v_snd_3344_;
                        v_res_3328_ = v___x_3350_;
                        state = 29;
                        continue;
                    } else {
                        v_isSharedCheck_3359_ = (!leanh::lean_is_exclusive(v_a_3099_)) as u8;
                        if v_isSharedCheck_3359_ == 0 {
                            v_unused_3360_ = leanh::lean_ctor_get(v_a_3099_, 1);
                            leanh::lean_dec(v_unused_3360_);
                            v_unused_3361_ = leanh::lean_ctor_get(v_a_3099_, 0);
                            leanh::lean_dec(v_unused_3361_);
                            v___x_3352_ = v_a_3099_;
                            v_isShared_3353_ = v_isSharedCheck_3359_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3099_);
                            v___x_3352_ = leanh::lean_box(0);
                            v_isShared_3353_ = v_isSharedCheck_3359_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    v___x_3362_ = leanh::lean_box(0);
                    v___x_3363_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3363_, 0, v_a_3099_);
                    leanh::lean_ctor_set(v___x_3363_, 1, v___x_3362_);
                    return v___x_3363_;
                }
            }
            1 => {
                if v___y_3103_ == 0 {
                    leanh::lean_dec_ref(v___y_3102_);
                    v___x_3104_ = l_Lean_Json_Parser_natMaybeZero___closed__1;
                    v___x_3105_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3105_, 0, v___y_3101_);
                    leanh::lean_ctor_set(v___x_3105_, 1, v___x_3104_);
                    return v___x_3105_;
                } else {
                    v___x_3106_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3107_ = l_Lean_Json_Parser_natCore(v___x_3106_, v___y_3101_);
                    if leanh::lean_obj_tag(v___x_3107_) == 0 {
                        v_pos_3108_ = leanh::lean_ctor_get(v___x_3107_, 0);
                        v_res_3109_ = leanh::lean_ctor_get(v___x_3107_, 1);
                        v_isSharedCheck_3123_ =
                            (!leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3123_ == 0 {
                            v___x_3111_ = v___x_3107_;
                            v_isShared_3112_ = v_isSharedCheck_3123_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_3109_);
                            leanh::lean_inc(v_pos_3108_);
                            leanh::lean_dec(v___x_3107_);
                            v___x_3111_ = leanh::lean_box(0);
                            v_isShared_3112_ = v_isSharedCheck_3123_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3102_);
                        v_pos_3124_ = leanh::lean_ctor_get(v___x_3107_, 0);
                        v_err_3125_ = leanh::lean_ctor_get(v___x_3107_, 1);
                        v_isSharedCheck_3132_ =
                            (!leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3132_ == 0 {
                            v___x_3127_ = v___x_3107_;
                            v_isShared_3128_ = v_isSharedCheck_3132_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3125_);
                            leanh::lean_inc(v_pos_3124_);
                            leanh::lean_dec(v___x_3107_);
                            v___x_3127_ = leanh::lean_box(0);
                            v_isShared_3128_ = v_isSharedCheck_3132_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3113_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0_once),
                    _init_l_Lean_Json_Parser_numWithDecimals___closed__0,
                );
                v___x_3114_ = lean_nat_dec_lt(v___x_3113_, v_res_3109_);
                if v___x_3114_ == 0 {
                    v___x_3115_ = l_Lean_JsonNumber_shiftl(v___y_3102_, v_res_3109_);
                    leanh::lean_dec(v_res_3109_);
                    if v_isShared_3112_ == 0 {
                        leanh::lean_ctor_set(v___x_3111_, 1, v___x_3115_);
                        v___x_3117_ = v___x_3111_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_pos_3108_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3115_);
                        v___x_3117_ = v_reuseFailAlloc_3118_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_res_3109_);
                    leanh::lean_dec_ref(v___y_3102_);
                    v___x_3119_ = l_Lean_Json_Parser_exponent___closed__1;
                    if v_isShared_3112_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3111_, 1);
                        leanh::lean_ctor_set(v___x_3111_, 1, v___x_3119_);
                        v___x_3121_ = v___x_3111_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3122_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_pos_3108_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3119_);
                        v___x_3121_ = v_reuseFailAlloc_3122_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3117_;
            }
            4 => {
                return v___x_3121_;
            }
            5 => {
                if v_isShared_3128_ == 0 {
                    v___x_3130_ = v___x_3127_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_pos_3124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_err_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3130_;
            }
            7 => {
                v___x_3138_ = lean_string_utf8_byte_size(v_fst_3136_);
                v___x_3139_ = lean_nat_dec_eq(v_snd_3137_, v___x_3138_);
                if v___x_3139_ == 0 {
                    v___x_3140_ = lean_string_utf8_get_fast(v_fst_3136_, v_snd_3137_);
                    leanh::lean_dec(v_snd_3137_);
                    leanh::lean_dec(v_fst_3136_);
                    v___x_3141_ = 48;
                    v___x_3142_ = lean_uint32_dec_le(v___x_3141_, v___x_3140_);
                    if v___x_3142_ == 0 {
                        v___y_3101_ = v___y_3135_;
                        v___y_3102_ = v___y_3134_;
                        v___y_3103_ = v___x_3142_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3143_ = 57;
                        v___x_3144_ = lean_uint32_dec_le(v___x_3140_, v___x_3143_);
                        v___y_3101_ = v___y_3135_;
                        v___y_3102_ = v___y_3134_;
                        v___y_3103_ = v___x_3144_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3137_);
                    leanh::lean_dec(v_fst_3136_);
                    leanh::lean_dec_ref(v___y_3134_);
                    v___x_3145_ = leanh::lean_box(0);
                    v___x_3146_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3146_, 0, v___y_3135_);
                    leanh::lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                    return v___x_3146_;
                }
            }
            8 => {
                if v___y_3150_ == 0 {
                    leanh::lean_dec_ref(v___y_3148_);
                    v___x_3151_ = l_Lean_Json_Parser_natMaybeZero___closed__1;
                    v___x_3152_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3152_, 0, v___y_3149_);
                    leanh::lean_ctor_set(v___x_3152_, 1, v___x_3151_);
                    return v___x_3152_;
                } else {
                    v___x_3153_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3154_ = l_Lean_Json_Parser_natCore(v___x_3153_, v___y_3149_);
                    if leanh::lean_obj_tag(v___x_3154_) == 0 {
                        v_pos_3155_ = leanh::lean_ctor_get(v___x_3154_, 0);
                        v_res_3156_ = leanh::lean_ctor_get(v___x_3154_, 1);
                        v_isSharedCheck_3164_ =
                            (!leanh::lean_is_exclusive(v___x_3154_)) as u8;
                        if v_isSharedCheck_3164_ == 0 {
                            v___x_3158_ = v___x_3154_;
                            v_isShared_3159_ = v_isSharedCheck_3164_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_3156_);
                            leanh::lean_inc(v_pos_3155_);
                            leanh::lean_dec(v___x_3154_);
                            v___x_3158_ = leanh::lean_box(0);
                            v_isShared_3159_ = v_isSharedCheck_3164_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3148_);
                        v_pos_3165_ = leanh::lean_ctor_get(v___x_3154_, 0);
                        v_err_3166_ = leanh::lean_ctor_get(v___x_3154_, 1);
                        v_isSharedCheck_3173_ =
                            (!leanh::lean_is_exclusive(v___x_3154_)) as u8;
                        if v_isSharedCheck_3173_ == 0 {
                            v___x_3168_ = v___x_3154_;
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3166_);
                            leanh::lean_inc(v_pos_3165_);
                            leanh::lean_dec(v___x_3154_);
                            v___x_3168_ = leanh::lean_box(0);
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_3160_ = l_Lean_JsonNumber_shiftr(v___y_3148_, v_res_3156_);
                leanh::lean_dec(v_res_3156_);
                if v_isShared_3159_ == 0 {
                    leanh::lean_ctor_set(v___x_3158_, 1, v___x_3160_);
                    v___x_3162_ = v___x_3158_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_pos_3155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3160_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3162_;
            }
            11 => {
                if v_isShared_3169_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_pos_3165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_err_3166_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3171_;
            }
            13 => {
                v___x_3176_ = leanh::lean_box(0);
                v___x_3177_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3177_, 0, v___y_3175_);
                leanh::lean_ctor_set(v___x_3177_, 1, v___x_3176_);
                return v___x_3177_;
            }
            14 => {
                v___x_3183_ = lean_string_utf8_byte_size(v_fst_3181_);
                v___x_3184_ = lean_nat_dec_eq(v_snd_3182_, v___x_3183_);
                if v___x_3184_ == 0 {
                    leanh::lean_dec_ref(v___y_3180_);
                    v___x_3185_ = lean_string_utf8_next_fast(v_fst_3181_, v_snd_3182_);
                    leanh::lean_dec(v_snd_3182_);
                    leanh::lean_inc(v_fst_3181_);
                    v___x_3186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3186_, 0, v_fst_3181_);
                    leanh::lean_ctor_set(v___x_3186_, 1, v___x_3185_);
                    v___x_3187_ = lean_nat_dec_eq(v___x_3185_, v___x_3183_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = lean_string_utf8_get_fast(v_fst_3181_, v___x_3185_);
                        v___x_3189_ = 45;
                        v___x_3190_ = lean_uint32_dec_eq(v___x_3188_, v___x_3189_);
                        if v___x_3190_ == 0 {
                            v___x_3191_ = 43;
                            v___x_3192_ = lean_uint32_dec_eq(v___x_3188_, v___x_3191_);
                            if v___x_3192_ == 0 {
                                v___y_3134_ = v___y_3179_;
                                v___y_3135_ = v___x_3186_;
                                v_fst_3136_ = v_fst_3181_;
                                v_snd_3137_ = v___x_3185_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3186_, 2);
                                v___x_3193_ = lean_string_utf8_next_fast(v_fst_3181_, v___x_3185_);
                                leanh::lean_inc(v_fst_3181_);
                                v___x_3194_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3194_, 0, v_fst_3181_);
                                leanh::lean_ctor_set(v___x_3194_, 1, v___x_3193_);
                                v___y_3134_ = v___y_3179_;
                                v___y_3135_ = v___x_3194_;
                                v_fst_3136_ = v_fst_3181_;
                                v_snd_3137_ = v___x_3193_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_3186_, 2);
                            v___x_3195_ = lean_string_utf8_next_fast(v_fst_3181_, v___x_3185_);
                            leanh::lean_inc(v_fst_3181_);
                            v___x_3196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3196_, 0, v_fst_3181_);
                            leanh::lean_ctor_set(v___x_3196_, 1, v___x_3195_);
                            v___x_3197_ = lean_nat_dec_eq(v___x_3195_, v___x_3183_);
                            if v___x_3197_ == 0 {
                                if v___x_3190_ == 0 {
                                    leanh::lean_dec(v_fst_3181_);
                                    leanh::lean_dec_ref(v___y_3179_);
                                    v___y_3175_ = v___x_3196_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___x_3198_ =
                                        lean_string_utf8_get_fast(v_fst_3181_, v___x_3195_);
                                    leanh::lean_dec(v_fst_3181_);
                                    v___x_3199_ = 48;
                                    v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v___x_3198_);
                                    if v___x_3200_ == 0 {
                                        v___y_3148_ = v___y_3179_;
                                        v___y_3149_ = v___x_3196_;
                                        v___y_3150_ = v___x_3200_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_3201_ = 57;
                                        v___x_3202_ = lean_uint32_dec_le(v___x_3198_, v___x_3201_);
                                        v___y_3148_ = v___y_3179_;
                                        v___y_3149_ = v___x_3196_;
                                        v___y_3150_ = v___x_3202_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_fst_3181_);
                                leanh::lean_dec_ref(v___y_3179_);
                                v___y_3175_ = v___x_3196_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fst_3181_);
                        leanh::lean_dec_ref(v___y_3179_);
                        v___x_3203_ = leanh::lean_box(0);
                        v___x_3204_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3204_, 0, v___x_3186_);
                        leanh::lean_ctor_set(v___x_3204_, 1, v___x_3203_);
                        return v___x_3204_;
                    }
                } else {
                    leanh::lean_dec(v_snd_3182_);
                    leanh::lean_dec(v_fst_3181_);
                    leanh::lean_dec_ref(v___y_3179_);
                    v___x_3205_ = leanh::lean_box(0);
                    v___x_3206_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3206_, 0, v___y_3180_);
                    leanh::lean_ctor_set(v___x_3206_, 1, v___x_3205_);
                    return v___x_3206_;
                }
            }
            15 => {
                v___x_3213_ = lean_string_utf8_byte_size(v_fst_3210_);
                v___x_3214_ = lean_nat_dec_eq(v_snd_3211_, v___x_3213_);
                if v___x_3214_ == 0 {
                    v___x_3215_ = lean_string_utf8_get_fast(v_fst_3210_, v_snd_3211_);
                    v___x_3216_ = 101;
                    v___x_3217_ = lean_uint32_dec_eq(v___x_3215_, v___x_3216_);
                    if v___x_3217_ == 0 {
                        v___x_3218_ = 69;
                        v___x_3219_ = lean_uint32_dec_eq(v___x_3215_, v___x_3218_);
                        if v___x_3219_ == 0 {
                            leanh::lean_dec_ref(v_res_3212_);
                            leanh::lean_dec(v_snd_3211_);
                            leanh::lean_dec(v_fst_3210_);
                            leanh::lean_dec_ref(v_pos_3209_);
                            return v___y_3208_;
                        } else {
                            leanh::lean_dec_ref(v___y_3208_);
                            v___y_3179_ = v_res_3212_;
                            v___y_3180_ = v_pos_3209_;
                            v_fst_3181_ = v_fst_3210_;
                            v_snd_3182_ = v_snd_3211_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3208_);
                        v___y_3179_ = v_res_3212_;
                        v___y_3180_ = v_pos_3209_;
                        v_fst_3181_ = v_fst_3210_;
                        v_snd_3182_ = v_snd_3211_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_res_3212_);
                    leanh::lean_dec(v_snd_3211_);
                    leanh::lean_dec(v_fst_3210_);
                    leanh::lean_dec_ref(v_pos_3209_);
                    return v___y_3208_;
                }
            }
            16 => {
                if v___y_3224_ == 0 {
                    leanh::lean_dec(v___y_3221_);
                    v___x_3225_ = l_Lean_Json_Parser_natNumDigits___closed__1;
                    v___x_3226_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3226_, 0, v___y_3223_);
                    leanh::lean_ctor_set(v___x_3226_, 1, v___x_3225_);
                    return v___x_3226_;
                } else {
                    v___x_3227_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3228_ =
                        l_Lean_Json_Parser_natCoreNumDigits(v___x_3227_, v___x_3227_, v___y_3223_);
                    if leanh::lean_obj_tag(v___x_3228_) == 0 {
                        v_res_3229_ = leanh::lean_ctor_get(v___x_3228_, 1);
                        v_pos_3230_ = leanh::lean_ctor_get(v___x_3228_, 0);
                        v_isSharedCheck_3262_ =
                            (!leanh::lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3262_ == 0 {
                            v___x_3232_ = v___x_3228_;
                            v_isShared_3233_ = v_isSharedCheck_3262_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_3229_);
                            leanh::lean_inc(v_pos_3230_);
                            leanh::lean_dec(v___x_3228_);
                            v___x_3232_ = leanh::lean_box(0);
                            v_isShared_3233_ = v_isSharedCheck_3262_;
                            state = 17;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_3221_);
                        v_pos_3263_ = leanh::lean_ctor_get(v___x_3228_, 0);
                        v_err_3264_ = leanh::lean_ctor_get(v___x_3228_, 1);
                        v_isSharedCheck_3271_ =
                            (!leanh::lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3271_ == 0 {
                            v___x_3266_ = v___x_3228_;
                            v_isShared_3267_ = v_isSharedCheck_3271_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3264_);
                            leanh::lean_inc(v_pos_3263_);
                            leanh::lean_dec(v___x_3228_);
                            v___x_3266_ = leanh::lean_box(0);
                            v_isShared_3267_ = v_isSharedCheck_3271_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            17 => {
                v_fst_3234_ = leanh::lean_ctor_get(v_res_3229_, 0);
                v_snd_3235_ = leanh::lean_ctor_get(v_res_3229_, 1);
                v_isSharedCheck_3261_ = (!leanh::lean_is_exclusive(v_res_3229_)) as u8;
                if v_isSharedCheck_3261_ == 0 {
                    v___x_3237_ = v_res_3229_;
                    v_isShared_3238_ = v_isSharedCheck_3261_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3235_);
                    leanh::lean_inc(v_fst_3234_);
                    leanh::lean_dec(v_res_3229_);
                    v___x_3237_ = leanh::lean_box(0);
                    v_isShared_3238_ = v_isSharedCheck_3261_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3239_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numWithDecimals___closed__0_once),
                    _init_l_Lean_Json_Parser_numWithDecimals___closed__0,
                );
                v___x_3240_ = lean_nat_dec_lt(v___x_3239_, v_snd_3235_);
                if v___x_3240_ == 0 {
                    v___x_3241_ = leanh::lean_unsigned_to_nat(10);
                    v___x_3242_ = lean_nat_pow(v___x_3241_, v_snd_3235_);
                    v_fst_3243_ = leanh::lean_ctor_get(v_pos_3230_, 0);
                    leanh::lean_inc(v_fst_3243_);
                    v_snd_3244_ = leanh::lean_ctor_get(v_pos_3230_, 1);
                    leanh::lean_inc(v_snd_3244_);
                    v___x_3245_ = lean_nat_to_int(v___y_3221_);
                    v___x_3246_ = lean_nat_to_int(v___x_3242_);
                    v___x_3247_ = lean_int_mul(v___x_3245_, v___x_3246_);
                    leanh::lean_dec(v___x_3246_);
                    leanh::lean_dec(v___x_3245_);
                    v___x_3248_ = lean_nat_to_int(v_fst_3234_);
                    v___x_3249_ = lean_int_add(v___x_3247_, v___x_3248_);
                    leanh::lean_dec(v___x_3248_);
                    leanh::lean_dec(v___x_3247_);
                    v___x_3250_ = lean_int_mul(v___y_3222_, v___x_3249_);
                    leanh::lean_dec(v___x_3249_);
                    if v_isShared_3238_ == 0 {
                        leanh::lean_ctor_set(v___x_3237_, 0, v___x_3250_);
                        v___x_3252_ = v___x_3237_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_3256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3250_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_snd_3235_);
                        v___x_3252_ = v_reuseFailAlloc_3256_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3237_);
                    leanh::lean_dec(v_snd_3235_);
                    leanh::lean_dec(v_fst_3234_);
                    leanh::lean_dec(v___y_3221_);
                    v___x_3257_ = l_Lean_Json_Parser_numWithDecimals___closed__2;
                    if v_isShared_3233_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3232_, 1);
                        leanh::lean_ctor_set(v___x_3232_, 1, v___x_3257_);
                        v___x_3259_ = v___x_3232_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3260_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_pos_3230_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3260_, 1, v___x_3257_);
                        v___x_3259_ = v_reuseFailAlloc_3260_;
                        state = 21;
                        continue;
                    }
                }
            }
            19 => {
                leanh::lean_inc_ref(v___x_3252_);
                leanh::lean_inc(v_pos_3230_);
                if v_isShared_3233_ == 0 {
                    leanh::lean_ctor_set(v___x_3232_, 1, v___x_3252_);
                    v___x_3254_ = v___x_3232_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_pos_3230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3252_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___y_3208_ = v___x_3254_;
                v_pos_3209_ = v_pos_3230_;
                v_fst_3210_ = v_fst_3243_;
                v_snd_3211_ = v_snd_3244_;
                v_res_3212_ = v___x_3252_;
                state = 15;
                continue;
            }
            21 => {
                return v___x_3259_;
            }
            22 => {
                if v_isShared_3267_ == 0 {
                    v___x_3269_ = v___x_3266_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_pos_3263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_err_3264_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3269_;
            }
            24 => {
                v___x_3274_ = leanh::lean_box(0);
                v___x_3275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3275_, 0, v___y_3273_);
                leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                return v___x_3275_;
            }
            25 => {
                v___x_3282_ = lean_string_utf8_byte_size(v_fst_3279_);
                v___x_3283_ = lean_nat_dec_eq(v_snd_3280_, v___x_3282_);
                if v___x_3283_ == 0 {
                    v___x_3284_ = lean_string_utf8_get_fast(v_fst_3279_, v_snd_3280_);
                    v___x_3285_ = 46;
                    v___x_3286_ = lean_uint32_dec_eq(v___x_3284_, v___x_3285_);
                    if v___x_3286_ == 0 {
                        v___x_3287_ = lean_nat_to_int(v_res_3281_);
                        v___x_3288_ = lean_int_mul(v___y_3277_, v___x_3287_);
                        leanh::lean_dec(v___x_3287_);
                        v___x_3289_ = l_Lean_JsonNumber_fromInt(v___x_3288_);
                        leanh::lean_inc_ref(v___x_3289_);
                        leanh::lean_inc_ref(v_pos_3278_);
                        v___x_3290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3290_, 0, v_pos_3278_);
                        leanh::lean_ctor_set(v___x_3290_, 1, v___x_3289_);
                        v___y_3208_ = v___x_3290_;
                        v_pos_3209_ = v_pos_3278_;
                        v_fst_3210_ = v_fst_3279_;
                        v_snd_3211_ = v_snd_3280_;
                        v_res_3212_ = v___x_3289_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_pos_3278_);
                        v___x_3291_ = lean_string_utf8_next_fast(v_fst_3279_, v_snd_3280_);
                        leanh::lean_dec(v_snd_3280_);
                        leanh::lean_inc(v_fst_3279_);
                        v___x_3292_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3292_, 0, v_fst_3279_);
                        leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
                        v___x_3293_ = lean_nat_dec_eq(v___x_3291_, v___x_3282_);
                        if v___x_3293_ == 0 {
                            if v___x_3286_ == 0 {
                                leanh::lean_dec(v_res_3281_);
                                leanh::lean_dec(v_fst_3279_);
                                v___y_3273_ = v___x_3292_;
                                state = 24;
                                continue;
                            } else {
                                v___x_3294_ = lean_string_utf8_get_fast(v_fst_3279_, v___x_3291_);
                                leanh::lean_dec(v_fst_3279_);
                                v___x_3295_ = 48;
                                v___x_3296_ = lean_uint32_dec_le(v___x_3295_, v___x_3294_);
                                if v___x_3296_ == 0 {
                                    v___y_3221_ = v_res_3281_;
                                    v___y_3222_ = v___y_3277_;
                                    v___y_3223_ = v___x_3292_;
                                    v___y_3224_ = v___x_3296_;
                                    state = 16;
                                    continue;
                                } else {
                                    v___x_3297_ = 57;
                                    v___x_3298_ = lean_uint32_dec_le(v___x_3294_, v___x_3297_);
                                    v___y_3221_ = v_res_3281_;
                                    v___y_3222_ = v___y_3277_;
                                    v___y_3223_ = v___x_3292_;
                                    v___y_3224_ = v___x_3298_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_res_3281_);
                            leanh::lean_dec(v_fst_3279_);
                            v___y_3273_ = v___x_3292_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    v___x_3299_ = lean_nat_to_int(v_res_3281_);
                    v___x_3300_ = lean_int_mul(v___y_3277_, v___x_3299_);
                    leanh::lean_dec(v___x_3299_);
                    v___x_3301_ = l_Lean_JsonNumber_fromInt(v___x_3300_);
                    leanh::lean_inc_ref(v___x_3301_);
                    leanh::lean_inc_ref(v_pos_3278_);
                    v___x_3302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3302_, 0, v_pos_3278_);
                    leanh::lean_ctor_set(v___x_3302_, 1, v___x_3301_);
                    v___y_3208_ = v___x_3302_;
                    v_pos_3209_ = v_pos_3278_;
                    v_fst_3210_ = v_fst_3279_;
                    v_snd_3211_ = v_snd_3280_;
                    v_res_3212_ = v___x_3301_;
                    state = 15;
                    continue;
                }
            }
            26 => {
                if v___y_3306_ == 0 {
                    v___x_3307_ = l_Lean_Json_Parser_natNonZero___closed__1;
                    v___x_3308_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3308_, 0, v___y_3305_);
                    leanh::lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                    return v___x_3308_;
                } else {
                    v___x_3309_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3310_ = l_Lean_Json_Parser_natCore(v___x_3309_, v___y_3305_);
                    if leanh::lean_obj_tag(v___x_3310_) == 0 {
                        v_pos_3311_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        leanh::lean_inc(v_pos_3311_);
                        v_res_3312_ = leanh::lean_ctor_get(v___x_3310_, 1);
                        leanh::lean_inc(v_res_3312_);
                        leanh::lean_dec_ref_known(v___x_3310_, 2);
                        v_fst_3313_ = leanh::lean_ctor_get(v_pos_3311_, 0);
                        leanh::lean_inc(v_fst_3313_);
                        v_snd_3314_ = leanh::lean_ctor_get(v_pos_3311_, 1);
                        leanh::lean_inc(v_snd_3314_);
                        v___y_3277_ = v___y_3304_;
                        v_pos_3278_ = v_pos_3311_;
                        v_fst_3279_ = v_fst_3313_;
                        v_snd_3280_ = v_snd_3314_;
                        v_res_3281_ = v_res_3312_;
                        state = 25;
                        continue;
                    } else {
                        v_pos_3315_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        v_err_3316_ = leanh::lean_ctor_get(v___x_3310_, 1);
                        v_isSharedCheck_3323_ =
                            (!leanh::lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3323_ == 0 {
                            v___x_3318_ = v___x_3310_;
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3316_);
                            leanh::lean_inc(v_pos_3315_);
                            leanh::lean_dec(v___x_3310_);
                            v___x_3318_ = leanh::lean_box(0);
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            27 => {
                if v_isShared_3319_ == 0 {
                    v___x_3321_ = v___x_3318_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3322_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_pos_3315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_err_3316_);
                    v___x_3321_ = v_reuseFailAlloc_3322_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3321_;
            }
            29 => {
                v___x_3329_ = lean_string_utf8_byte_size(v_fst_3326_);
                v___x_3330_ = lean_nat_dec_eq(v_snd_3327_, v___x_3329_);
                if v___x_3330_ == 0 {
                    v___x_3331_ = lean_string_utf8_get_fast(v_fst_3326_, v_snd_3327_);
                    v___x_3332_ = 48;
                    v___x_3333_ = lean_uint32_dec_eq(v___x_3331_, v___x_3332_);
                    if v___x_3333_ == 0 {
                        leanh::lean_dec(v_snd_3327_);
                        leanh::lean_dec(v_fst_3326_);
                        v___x_3334_ = 49;
                        v___x_3335_ = lean_uint32_dec_le(v___x_3334_, v___x_3331_);
                        if v___x_3335_ == 0 {
                            v___y_3304_ = v_res_3328_;
                            v___y_3305_ = v_pos_3325_;
                            v___y_3306_ = v___x_3335_;
                            state = 26;
                            continue;
                        } else {
                            v___x_3336_ = 57;
                            v___x_3337_ = lean_uint32_dec_le(v___x_3331_, v___x_3336_);
                            v___y_3304_ = v_res_3328_;
                            v___y_3305_ = v_pos_3325_;
                            v___y_3306_ = v___x_3337_;
                            state = 26;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_pos_3325_);
                        v___x_3338_ = lean_string_utf8_next_fast(v_fst_3326_, v_snd_3327_);
                        leanh::lean_dec(v_snd_3327_);
                        leanh::lean_inc(v_fst_3326_);
                        v___x_3339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3339_, 0, v_fst_3326_);
                        leanh::lean_ctor_set(v___x_3339_, 1, v___x_3338_);
                        v___x_3340_ = leanh::lean_unsigned_to_nat(0);
                        v___y_3277_ = v_res_3328_;
                        v_pos_3278_ = v___x_3339_;
                        v_fst_3279_ = v_fst_3326_;
                        v_snd_3280_ = v___x_3338_;
                        v_res_3281_ = v___x_3340_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3327_);
                    leanh::lean_dec(v_fst_3326_);
                    v___x_3341_ = leanh::lean_box(0);
                    v___x_3342_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3342_, 0, v_pos_3325_);
                    leanh::lean_ctor_set(v___x_3342_, 1, v___x_3341_);
                    return v___x_3342_;
                }
            }
            30 => {
                v___x_3354_ = lean_string_utf8_next_fast(v_fst_3343_, v_snd_3344_);
                leanh::lean_dec(v_snd_3344_);
                leanh::lean_inc(v_fst_3343_);
                if v_isShared_3353_ == 0 {
                    leanh::lean_ctor_set(v___x_3352_, 1, v___x_3354_);
                    v___x_3356_ = v___x_3352_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_fst_3343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3354_);
                    v___x_3356_ = v_reuseFailAlloc_3358_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_3357_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Json_Parser_numSign___closed__1_once),
                    _init_l_Lean_Json_Parser_numSign___closed__1,
                );
                v_pos_3325_ = v___x_3356_;
                v_fst_3326_ = v_fst_3343_;
                v_snd_3327_ = v___x_3354_;
                v_res_3328_ = v___x_3357_;
                state = 29;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(
    mut v_msg_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = leanh::lean_box(1);
    v___x_3366_ = lean_panic_fn_borrowed(v___x_3365_, v_msg_3364_);
    return v___x_3366_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2;
    v___x_3371_ = leanh::lean_unsigned_to_nat(35);
    v___x_3372_ = leanh::lean_unsigned_to_nat(182);
    v___x_3373_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1;
    v___x_3374_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0;
    v___x_3375_ = l_mkPanicMessageWithDecl(
        v___x_3374_,
        v___x_3373_,
        v___x_3372_,
        v___x_3371_,
        v___x_3370_,
    );
    return v___x_3375_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2;
    v___x_3377_ = leanh::lean_unsigned_to_nat(21);
    v___x_3378_ = leanh::lean_unsigned_to_nat(183);
    v___x_3379_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1;
    v___x_3380_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0;
    v___x_3381_ = l_mkPanicMessageWithDecl(
        v___x_3380_,
        v___x_3379_,
        v___x_3378_,
        v___x_3377_,
        v___x_3376_,
    );
    return v___x_3381_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3384_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6;
    v___x_3385_ = leanh::lean_unsigned_to_nat(35);
    v___x_3386_ = leanh::lean_unsigned_to_nat(276);
    v___x_3387_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5;
    v___x_3388_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0;
    v___x_3389_ = l_mkPanicMessageWithDecl(
        v___x_3388_,
        v___x_3387_,
        v___x_3386_,
        v___x_3385_,
        v___x_3384_,
    );
    return v___x_3389_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6;
    v___x_3391_ = leanh::lean_unsigned_to_nat(21);
    v___x_3392_ = leanh::lean_unsigned_to_nat(277);
    v___x_3393_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5;
    v___x_3394_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0;
    v___x_3395_ = l_mkPanicMessageWithDecl(
        v___x_3394_,
        v___x_3393_,
        v___x_3392_,
        v___x_3391_,
        v___x_3390_,
    );
    return v___x_3395_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(
    mut v_k_3396_: *mut leanh::LeanObject,
    mut v_v_3397_: *mut leanh::LeanObject,
    mut v_t_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3406_: u8 = 0;
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_size_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut v_unused_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_unused_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v_size_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_unused_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v_unused_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v_k_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut v_unused_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_unused_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v_size_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_unused_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3660_: u8 = 0;
    let mut v_unused_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_unused_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_size_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v_unused_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v_k_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3725_: u8 = 0;
    let mut v_unused_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_unused_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut v_unused_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3398_) == 0 {
                    v_size_3399_ = leanh::lean_ctor_get(v_t_3398_, 0);
                    v_k_3400_ = leanh::lean_ctor_get(v_t_3398_, 1);
                    v_v_3401_ = leanh::lean_ctor_get(v_t_3398_, 2);
                    v_l_3402_ = leanh::lean_ctor_get(v_t_3398_, 3);
                    v_r_3403_ = leanh::lean_ctor_get(v_t_3398_, 4);
                    v_isSharedCheck_3759_ = (!leanh::lean_is_exclusive(v_t_3398_)) as u8;
                    if v_isSharedCheck_3759_ == 0 {
                        v___x_3405_ = v_t_3398_;
                        v_isShared_3406_ = v_isSharedCheck_3759_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3403_);
                        leanh::lean_inc(v_l_3402_);
                        leanh::lean_inc(v_v_3401_);
                        leanh::lean_inc(v_k_3400_);
                        leanh::lean_inc(v_size_3399_);
                        leanh::lean_dec(v_t_3398_);
                        v___x_3405_ = leanh::lean_box(0);
                        v_isShared_3406_ = v_isSharedCheck_3759_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3760_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3761_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3761_, 0, v___x_3760_);
                    leanh::lean_ctor_set(v___x_3761_, 1, v_k_3396_);
                    leanh::lean_ctor_set(v___x_3761_, 2, v_v_3397_);
                    leanh::lean_ctor_set(v___x_3761_, 3, v_t_3398_);
                    leanh::lean_ctor_set(v___x_3761_, 4, v_t_3398_);
                    return v___x_3761_;
                }
            }
            1 => {
                v___x_3407_ = lean_string_compare(v_k_3396_, v_k_3400_);
                match v___x_3407_ {
                    0 => {
                        leanh::lean_dec(v_size_3399_);
                        v___x_3408_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_3396_, v_v_3397_, v_l_3402_);
                        if leanh::lean_obj_tag(v_r_3403_) == 0 {
                            if leanh::lean_obj_tag(v___x_3408_) == 0 {
                                v_size_3409_ = leanh::lean_ctor_get(v_r_3403_, 0);
                                v_size_3410_ = leanh::lean_ctor_get(v___x_3408_, 0);
                                leanh::lean_inc(v_size_3410_);
                                v_k_3411_ = leanh::lean_ctor_get(v___x_3408_, 1);
                                leanh::lean_inc(v_k_3411_);
                                v_v_3412_ = leanh::lean_ctor_get(v___x_3408_, 2);
                                leanh::lean_inc(v_v_3412_);
                                v_l_3413_ = leanh::lean_ctor_get(v___x_3408_, 3);
                                leanh::lean_inc(v_l_3413_);
                                v_r_3414_ = leanh::lean_ctor_get(v___x_3408_, 4);
                                leanh::lean_inc(v_r_3414_);
                                v___x_3415_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3416_ = lean_nat_mul(v___x_3415_, v_size_3409_);
                                v___x_3417_ = lean_nat_dec_lt(v___x_3416_, v_size_3410_);
                                leanh::lean_dec(v___x_3416_);
                                if v___x_3417_ == 0 {
                                    leanh::lean_dec(v_r_3414_);
                                    leanh::lean_dec(v_l_3413_);
                                    leanh::lean_dec(v_v_3412_);
                                    leanh::lean_dec(v_k_3411_);
                                    v___x_3418_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3419_ = lean_nat_add(v___x_3418_, v_size_3410_);
                                    leanh::lean_dec(v_size_3410_);
                                    v___x_3420_ = lean_nat_add(v___x_3419_, v_size_3409_);
                                    leanh::lean_dec(v___x_3419_);
                                    if v_isShared_3406_ == 0 {
                                        leanh::lean_ctor_set(v___x_3405_, 3, v___x_3408_);
                                        leanh::lean_ctor_set(v___x_3405_, 0, v___x_3420_);
                                        v___x_3422_ = v___x_3405_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3423_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3423_,
                                            0,
                                            v___x_3420_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3423_,
                                            1,
                                            v_k_3400_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3423_,
                                            2,
                                            v_v_3401_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3423_,
                                            3,
                                            v___x_3408_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3423_,
                                            4,
                                            v_r_3403_,
                                        );
                                        v___x_3422_ = v_reuseFailAlloc_3423_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3495_ =
                                        (!leanh::lean_is_exclusive(v___x_3408_)) as u8;
                                    if v_isSharedCheck_3495_ == 0 {
                                        v_unused_3496_ =
                                            leanh::lean_ctor_get(v___x_3408_, 4);
                                        leanh::lean_dec(v_unused_3496_);
                                        v_unused_3497_ =
                                            leanh::lean_ctor_get(v___x_3408_, 3);
                                        leanh::lean_dec(v_unused_3497_);
                                        v_unused_3498_ =
                                            leanh::lean_ctor_get(v___x_3408_, 2);
                                        leanh::lean_dec(v_unused_3498_);
                                        v_unused_3499_ =
                                            leanh::lean_ctor_get(v___x_3408_, 1);
                                        leanh::lean_dec(v_unused_3499_);
                                        v_unused_3500_ =
                                            leanh::lean_ctor_get(v___x_3408_, 0);
                                        leanh::lean_dec(v_unused_3500_);
                                        v___x_3425_ = v___x_3408_;
                                        v_isShared_3426_ = v_isSharedCheck_3495_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3408_);
                                        v___x_3425_ = leanh::lean_box(0);
                                        v_isShared_3426_ = v_isSharedCheck_3495_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3501_ = leanh::lean_ctor_get(v_r_3403_, 0);
                                v___x_3502_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3503_ = lean_nat_add(v___x_3502_, v_size_3501_);
                                if v_isShared_3406_ == 0 {
                                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3408_);
                                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3503_);
                                    v___x_3505_ = v___x_3405_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3506_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3506_,
                                        0,
                                        v___x_3503_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3506_,
                                        1,
                                        v_k_3400_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3506_,
                                        2,
                                        v_v_3401_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3506_,
                                        3,
                                        v___x_3408_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3506_,
                                        4,
                                        v_r_3403_,
                                    );
                                    v___x_3505_ = v_reuseFailAlloc_3506_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3408_) == 0 {
                                v_l_3507_ = leanh::lean_ctor_get(v___x_3408_, 3);
                                leanh::lean_inc(v_l_3507_);
                                if leanh::lean_obj_tag(v_l_3507_) == 0 {
                                    v_r_3508_ = leanh::lean_ctor_get(v___x_3408_, 4);
                                    leanh::lean_inc(v_r_3508_);
                                    if leanh::lean_obj_tag(v_r_3508_) == 0 {
                                        v_size_3509_ = leanh::lean_ctor_get(v___x_3408_, 0);
                                        v_k_3510_ = leanh::lean_ctor_get(v___x_3408_, 1);
                                        v_v_3511_ = leanh::lean_ctor_get(v___x_3408_, 2);
                                        v_isSharedCheck_3525_ =
                                            (!leanh::lean_is_exclusive(v___x_3408_)) as u8;
                                        if v_isSharedCheck_3525_ == 0 {
                                            v_unused_3526_ =
                                                leanh::lean_ctor_get(v___x_3408_, 4);
                                            leanh::lean_dec(v_unused_3526_);
                                            v_unused_3527_ =
                                                leanh::lean_ctor_get(v___x_3408_, 3);
                                            leanh::lean_dec(v_unused_3527_);
                                            v___x_3513_ = v___x_3408_;
                                            v_isShared_3514_ = v_isSharedCheck_3525_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3511_);
                                            leanh::lean_inc(v_k_3510_);
                                            leanh::lean_inc(v_size_3509_);
                                            leanh::lean_dec(v___x_3408_);
                                            v___x_3513_ = leanh::lean_box(0);
                                            v_isShared_3514_ = v_isSharedCheck_3525_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3528_ = leanh::lean_ctor_get(v___x_3408_, 1);
                                        v_v_3529_ = leanh::lean_ctor_get(v___x_3408_, 2);
                                        v_isSharedCheck_3541_ =
                                            (!leanh::lean_is_exclusive(v___x_3408_)) as u8;
                                        if v_isSharedCheck_3541_ == 0 {
                                            v_unused_3542_ =
                                                leanh::lean_ctor_get(v___x_3408_, 4);
                                            leanh::lean_dec(v_unused_3542_);
                                            v_unused_3543_ =
                                                leanh::lean_ctor_get(v___x_3408_, 3);
                                            leanh::lean_dec(v_unused_3543_);
                                            v_unused_3544_ =
                                                leanh::lean_ctor_get(v___x_3408_, 0);
                                            leanh::lean_dec(v_unused_3544_);
                                            v___x_3531_ = v___x_3408_;
                                            v_isShared_3532_ = v_isSharedCheck_3541_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3529_);
                                            leanh::lean_inc(v_k_3528_);
                                            leanh::lean_dec(v___x_3408_);
                                            v___x_3531_ = leanh::lean_box(0);
                                            v_isShared_3532_ = v_isSharedCheck_3541_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3545_ = leanh::lean_ctor_get(v___x_3408_, 4);
                                    leanh::lean_inc(v_r_3545_);
                                    if leanh::lean_obj_tag(v_r_3545_) == 0 {
                                        v_k_3546_ = leanh::lean_ctor_get(v___x_3408_, 1);
                                        v_v_3547_ = leanh::lean_ctor_get(v___x_3408_, 2);
                                        v_isSharedCheck_3571_ =
                                            (!leanh::lean_is_exclusive(v___x_3408_)) as u8;
                                        if v_isSharedCheck_3571_ == 0 {
                                            v_unused_3572_ =
                                                leanh::lean_ctor_get(v___x_3408_, 4);
                                            leanh::lean_dec(v_unused_3572_);
                                            v_unused_3573_ =
                                                leanh::lean_ctor_get(v___x_3408_, 3);
                                            leanh::lean_dec(v_unused_3573_);
                                            v_unused_3574_ =
                                                leanh::lean_ctor_get(v___x_3408_, 0);
                                            leanh::lean_dec(v_unused_3574_);
                                            v___x_3549_ = v___x_3408_;
                                            v_isShared_3550_ = v_isSharedCheck_3571_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3547_);
                                            leanh::lean_inc(v_k_3546_);
                                            leanh::lean_dec(v___x_3408_);
                                            v___x_3549_ = leanh::lean_box(0);
                                            v_isShared_3550_ = v_isSharedCheck_3571_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_3575_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3406_ == 0 {
                                            leanh::lean_ctor_set(v___x_3405_, 4, v_r_3545_);
                                            leanh::lean_ctor_set(
                                                v___x_3405_,
                                                3,
                                                v___x_3408_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3405_,
                                                0,
                                                v___x_3575_,
                                            );
                                            v___x_3577_ = v___x_3405_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3578_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3578_,
                                                0,
                                                v___x_3575_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3578_,
                                                1,
                                                v_k_3400_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3578_,
                                                2,
                                                v_v_3401_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3578_,
                                                3,
                                                v___x_3408_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3578_,
                                                4,
                                                v_r_3545_,
                                            );
                                            v___x_3577_ = v_reuseFailAlloc_3578_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3579_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3406_ == 0 {
                                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3408_);
                                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3408_);
                                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3579_);
                                    v___x_3581_ = v___x_3405_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3582_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3582_,
                                        0,
                                        v___x_3579_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3582_,
                                        1,
                                        v_k_3400_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3582_,
                                        2,
                                        v_v_3401_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3582_,
                                        3,
                                        v___x_3408_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3582_,
                                        4,
                                        v___x_3408_,
                                    );
                                    v___x_3581_ = v_reuseFailAlloc_3582_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_3401_);
                        leanh::lean_dec(v_k_3400_);
                        if v_isShared_3406_ == 0 {
                            leanh::lean_ctor_set(v___x_3405_, 2, v_v_3397_);
                            leanh::lean_ctor_set(v___x_3405_, 1, v_k_3396_);
                            v___x_3584_ = v___x_3405_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_3585_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_size_3399_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_k_3396_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_v_3397_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_l_3402_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 4, v_r_3403_);
                            v___x_3584_ = v_reuseFailAlloc_3585_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_3399_);
                        v___x_3586_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_3396_, v_v_3397_, v_r_3403_);
                        if leanh::lean_obj_tag(v_l_3402_) == 0 {
                            if leanh::lean_obj_tag(v___x_3586_) == 0 {
                                v_size_3587_ = leanh::lean_ctor_get(v_l_3402_, 0);
                                v_size_3588_ = leanh::lean_ctor_get(v___x_3586_, 0);
                                leanh::lean_inc(v_size_3588_);
                                v_k_3589_ = leanh::lean_ctor_get(v___x_3586_, 1);
                                leanh::lean_inc(v_k_3589_);
                                v_v_3590_ = leanh::lean_ctor_get(v___x_3586_, 2);
                                leanh::lean_inc(v_v_3590_);
                                v_l_3591_ = leanh::lean_ctor_get(v___x_3586_, 3);
                                leanh::lean_inc(v_l_3591_);
                                v_r_3592_ = leanh::lean_ctor_get(v___x_3586_, 4);
                                leanh::lean_inc(v_r_3592_);
                                v___x_3593_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3594_ = lean_nat_mul(v___x_3593_, v_size_3587_);
                                v___x_3595_ = lean_nat_dec_lt(v___x_3594_, v_size_3588_);
                                leanh::lean_dec(v___x_3594_);
                                if v___x_3595_ == 0 {
                                    leanh::lean_dec(v_r_3592_);
                                    leanh::lean_dec(v_l_3591_);
                                    leanh::lean_dec(v_v_3590_);
                                    leanh::lean_dec(v_k_3589_);
                                    v___x_3596_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3597_ = lean_nat_add(v___x_3596_, v_size_3587_);
                                    v___x_3598_ = lean_nat_add(v___x_3597_, v_size_3588_);
                                    leanh::lean_dec(v_size_3588_);
                                    leanh::lean_dec(v___x_3597_);
                                    if v_isShared_3406_ == 0 {
                                        leanh::lean_ctor_set(v___x_3405_, 4, v___x_3586_);
                                        leanh::lean_ctor_set(v___x_3405_, 0, v___x_3598_);
                                        v___x_3600_ = v___x_3405_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3601_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3601_,
                                            0,
                                            v___x_3598_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3601_,
                                            1,
                                            v_k_3400_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3601_,
                                            2,
                                            v_v_3401_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3601_,
                                            3,
                                            v_l_3402_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3601_,
                                            4,
                                            v___x_3586_,
                                        );
                                        v___x_3600_ = v_reuseFailAlloc_3601_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3671_ =
                                        (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                                    if v_isSharedCheck_3671_ == 0 {
                                        v_unused_3672_ =
                                            leanh::lean_ctor_get(v___x_3586_, 4);
                                        leanh::lean_dec(v_unused_3672_);
                                        v_unused_3673_ =
                                            leanh::lean_ctor_get(v___x_3586_, 3);
                                        leanh::lean_dec(v_unused_3673_);
                                        v_unused_3674_ =
                                            leanh::lean_ctor_get(v___x_3586_, 2);
                                        leanh::lean_dec(v_unused_3674_);
                                        v_unused_3675_ =
                                            leanh::lean_ctor_get(v___x_3586_, 1);
                                        leanh::lean_dec(v_unused_3675_);
                                        v_unused_3676_ =
                                            leanh::lean_ctor_get(v___x_3586_, 0);
                                        leanh::lean_dec(v_unused_3676_);
                                        v___x_3603_ = v___x_3586_;
                                        v_isShared_3604_ = v_isSharedCheck_3671_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3586_);
                                        v___x_3603_ = leanh::lean_box(0);
                                        v_isShared_3604_ = v_isSharedCheck_3671_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3677_ = leanh::lean_ctor_get(v_l_3402_, 0);
                                v___x_3678_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3679_ = lean_nat_add(v___x_3678_, v_size_3677_);
                                if v_isShared_3406_ == 0 {
                                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3586_);
                                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3679_);
                                    v___x_3681_ = v___x_3405_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3682_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3682_,
                                        0,
                                        v___x_3679_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3682_,
                                        1,
                                        v_k_3400_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3682_,
                                        2,
                                        v_v_3401_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3682_,
                                        3,
                                        v_l_3402_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3682_,
                                        4,
                                        v___x_3586_,
                                    );
                                    v___x_3681_ = v_reuseFailAlloc_3682_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3586_) == 0 {
                                v_l_3683_ = leanh::lean_ctor_get(v___x_3586_, 3);
                                leanh::lean_inc(v_l_3683_);
                                if leanh::lean_obj_tag(v_l_3683_) == 0 {
                                    v_r_3684_ = leanh::lean_ctor_get(v___x_3586_, 4);
                                    leanh::lean_inc(v_r_3684_);
                                    if leanh::lean_obj_tag(v_r_3684_) == 0 {
                                        v_size_3685_ = leanh::lean_ctor_get(v___x_3586_, 0);
                                        v_k_3686_ = leanh::lean_ctor_get(v___x_3586_, 1);
                                        v_v_3687_ = leanh::lean_ctor_get(v___x_3586_, 2);
                                        v_isSharedCheck_3701_ =
                                            (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                                        if v_isSharedCheck_3701_ == 0 {
                                            v_unused_3702_ =
                                                leanh::lean_ctor_get(v___x_3586_, 4);
                                            leanh::lean_dec(v_unused_3702_);
                                            v_unused_3703_ =
                                                leanh::lean_ctor_get(v___x_3586_, 3);
                                            leanh::lean_dec(v_unused_3703_);
                                            v___x_3689_ = v___x_3586_;
                                            v_isShared_3690_ = v_isSharedCheck_3701_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3687_);
                                            leanh::lean_inc(v_k_3686_);
                                            leanh::lean_inc(v_size_3685_);
                                            leanh::lean_dec(v___x_3586_);
                                            v___x_3689_ = leanh::lean_box(0);
                                            v_isShared_3690_ = v_isSharedCheck_3701_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3704_ = leanh::lean_ctor_get(v___x_3586_, 1);
                                        v_v_3705_ = leanh::lean_ctor_get(v___x_3586_, 2);
                                        v_isSharedCheck_3729_ =
                                            (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                                        if v_isSharedCheck_3729_ == 0 {
                                            v_unused_3730_ =
                                                leanh::lean_ctor_get(v___x_3586_, 4);
                                            leanh::lean_dec(v_unused_3730_);
                                            v_unused_3731_ =
                                                leanh::lean_ctor_get(v___x_3586_, 3);
                                            leanh::lean_dec(v_unused_3731_);
                                            v_unused_3732_ =
                                                leanh::lean_ctor_get(v___x_3586_, 0);
                                            leanh::lean_dec(v_unused_3732_);
                                            v___x_3707_ = v___x_3586_;
                                            v_isShared_3708_ = v_isSharedCheck_3729_;
                                            state = 43;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3705_);
                                            leanh::lean_inc(v_k_3704_);
                                            leanh::lean_dec(v___x_3586_);
                                            v___x_3707_ = leanh::lean_box(0);
                                            v_isShared_3708_ = v_isSharedCheck_3729_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3733_ = leanh::lean_ctor_get(v___x_3586_, 4);
                                    leanh::lean_inc(v_r_3733_);
                                    if leanh::lean_obj_tag(v_r_3733_) == 0 {
                                        v_k_3734_ = leanh::lean_ctor_get(v___x_3586_, 1);
                                        v_v_3735_ = leanh::lean_ctor_get(v___x_3586_, 2);
                                        v_isSharedCheck_3747_ =
                                            (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                                        if v_isSharedCheck_3747_ == 0 {
                                            v_unused_3748_ =
                                                leanh::lean_ctor_get(v___x_3586_, 4);
                                            leanh::lean_dec(v_unused_3748_);
                                            v_unused_3749_ =
                                                leanh::lean_ctor_get(v___x_3586_, 3);
                                            leanh::lean_dec(v_unused_3749_);
                                            v_unused_3750_ =
                                                leanh::lean_ctor_get(v___x_3586_, 0);
                                            leanh::lean_dec(v_unused_3750_);
                                            v___x_3737_ = v___x_3586_;
                                            v_isShared_3738_ = v_isSharedCheck_3747_;
                                            state = 48;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3735_);
                                            leanh::lean_inc(v_k_3734_);
                                            leanh::lean_dec(v___x_3586_);
                                            v___x_3737_ = leanh::lean_box(0);
                                            v_isShared_3738_ = v_isSharedCheck_3747_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_3751_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3406_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_3405_,
                                                4,
                                                v___x_3586_,
                                            );
                                            leanh::lean_ctor_set(v___x_3405_, 3, v_r_3733_);
                                            leanh::lean_ctor_set(
                                                v___x_3405_,
                                                0,
                                                v___x_3751_,
                                            );
                                            v___x_3753_ = v___x_3405_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3754_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3754_,
                                                0,
                                                v___x_3751_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3754_,
                                                1,
                                                v_k_3400_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3754_,
                                                2,
                                                v_v_3401_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3754_,
                                                3,
                                                v_r_3733_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3754_,
                                                4,
                                                v___x_3586_,
                                            );
                                            v___x_3753_ = v_reuseFailAlloc_3754_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3755_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3406_ == 0 {
                                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3586_);
                                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3586_);
                                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3755_);
                                    v___x_3757_ = v___x_3405_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3758_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3758_,
                                        0,
                                        v___x_3755_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3758_,
                                        1,
                                        v_k_3400_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3758_,
                                        2,
                                        v_v_3401_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3758_,
                                        3,
                                        v___x_3586_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3758_,
                                        4,
                                        v___x_3586_,
                                    );
                                    v___x_3757_ = v_reuseFailAlloc_3758_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3422_;
            }
            3 => {
                if leanh::lean_obj_tag(v_l_3413_) == 0 {
                    if leanh::lean_obj_tag(v_r_3414_) == 0 {
                        v_size_3427_ = leanh::lean_ctor_get(v_l_3413_, 0);
                        v_size_3428_ = leanh::lean_ctor_get(v_r_3414_, 0);
                        v_k_3429_ = leanh::lean_ctor_get(v_r_3414_, 1);
                        v_v_3430_ = leanh::lean_ctor_get(v_r_3414_, 2);
                        v_l_3431_ = leanh::lean_ctor_get(v_r_3414_, 3);
                        v_r_3432_ = leanh::lean_ctor_get(v_r_3414_, 4);
                        v___x_3433_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3434_ = lean_nat_mul(v___x_3433_, v_size_3427_);
                        v___x_3435_ = lean_nat_dec_lt(v_size_3428_, v___x_3434_);
                        leanh::lean_dec(v___x_3434_);
                        if v___x_3435_ == 0 {
                            leanh::lean_inc(v_r_3432_);
                            leanh::lean_inc(v_l_3431_);
                            leanh::lean_inc(v_v_3430_);
                            leanh::lean_inc(v_k_3429_);
                            v_isSharedCheck_3465_ =
                                (!leanh::lean_is_exclusive(v_r_3414_)) as u8;
                            if v_isSharedCheck_3465_ == 0 {
                                v_unused_3466_ = leanh::lean_ctor_get(v_r_3414_, 4);
                                leanh::lean_dec(v_unused_3466_);
                                v_unused_3467_ = leanh::lean_ctor_get(v_r_3414_, 3);
                                leanh::lean_dec(v_unused_3467_);
                                v_unused_3468_ = leanh::lean_ctor_get(v_r_3414_, 2);
                                leanh::lean_dec(v_unused_3468_);
                                v_unused_3469_ = leanh::lean_ctor_get(v_r_3414_, 1);
                                leanh::lean_dec(v_unused_3469_);
                                v_unused_3470_ = leanh::lean_ctor_get(v_r_3414_, 0);
                                leanh::lean_dec(v_unused_3470_);
                                v___x_3437_ = v_r_3414_;
                                v_isShared_3438_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_3414_);
                                v___x_3437_ = leanh::lean_box(0);
                                v_isShared_3438_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3405_);
                            v___x_3471_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3472_ = lean_nat_add(v___x_3471_, v_size_3410_);
                            leanh::lean_dec(v_size_3410_);
                            v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3409_);
                            leanh::lean_dec(v___x_3472_);
                            v___x_3474_ = lean_nat_add(v___x_3471_, v_size_3409_);
                            v___x_3475_ = lean_nat_add(v___x_3474_, v_size_3428_);
                            leanh::lean_dec(v___x_3474_);
                            leanh::lean_inc_ref(v_r_3403_);
                            if v_isShared_3426_ == 0 {
                                leanh::lean_ctor_set(v___x_3425_, 4, v_r_3403_);
                                leanh::lean_ctor_set(v___x_3425_, 3, v_r_3414_);
                                leanh::lean_ctor_set(v___x_3425_, 2, v_v_3401_);
                                leanh::lean_ctor_set(v___x_3425_, 1, v_k_3400_);
                                leanh::lean_ctor_set(v___x_3425_, 0, v___x_3475_);
                                v___x_3477_ = v___x_3425_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_3490_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3475_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_k_3400_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_v_3401_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_r_3414_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_r_3403_);
                                v___x_3477_ = v_reuseFailAlloc_3490_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_3413_, 5);
                        leanh::lean_del_object(v___x_3425_);
                        leanh::lean_dec(v_v_3412_);
                        leanh::lean_dec(v_k_3411_);
                        leanh::lean_dec(v_size_3410_);
                        leanh::lean_dec_ref_known(v_r_3403_, 5);
                        leanh::lean_del_object(v___x_3405_);
                        leanh::lean_dec(v_v_3401_);
                        leanh::lean_dec(v_k_3400_);
                        v___x_3491_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
                        v___x_3492_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_3491_);
                        return v___x_3492_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3425_);
                    leanh::lean_dec(v_r_3414_);
                    leanh::lean_dec(v_v_3412_);
                    leanh::lean_dec(v_k_3411_);
                    leanh::lean_dec(v_size_3410_);
                    leanh::lean_dec_ref_known(v_r_3403_, 5);
                    leanh::lean_del_object(v___x_3405_);
                    leanh::lean_dec(v_v_3401_);
                    leanh::lean_dec(v_k_3400_);
                    v___x_3493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
                    v___x_3494_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_3493_);
                    return v___x_3494_;
                }
            }
            4 => {
                v___x_3439_ = leanh::lean_unsigned_to_nat(1);
                v___x_3440_ = lean_nat_add(v___x_3439_, v_size_3410_);
                leanh::lean_dec(v_size_3410_);
                v___x_3441_ = lean_nat_add(v___x_3440_, v_size_3409_);
                leanh::lean_dec(v___x_3440_);
                v___x_3453_ = lean_nat_add(v___x_3439_, v_size_3427_);
                if leanh::lean_obj_tag(v_l_3431_) == 0 {
                    v_size_3463_ = leanh::lean_ctor_get(v_l_3431_, 0);
                    leanh::lean_inc(v_size_3463_);
                    v___y_3455_ = v_size_3463_;
                    state = 8;
                    continue;
                } else {
                    v___x_3464_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3455_ = v___x_3464_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3446_ = lean_nat_add(v___y_3444_, v___y_3445_);
                leanh::lean_dec(v___y_3445_);
                leanh::lean_dec(v___y_3444_);
                if v_isShared_3438_ == 0 {
                    leanh::lean_ctor_set(v___x_3437_, 4, v_r_3403_);
                    leanh::lean_ctor_set(v___x_3437_, 3, v_r_3432_);
                    leanh::lean_ctor_set(v___x_3437_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3437_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3437_, 0, v___x_3446_);
                    v___x_3448_ = v___x_3437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_r_3432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_r_3403_);
                    v___x_3448_ = v_reuseFailAlloc_3452_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3426_ == 0 {
                    leanh::lean_ctor_set(v___x_3425_, 4, v___x_3448_);
                    leanh::lean_ctor_set(v___x_3425_, 3, v___y_3443_);
                    leanh::lean_ctor_set(v___x_3425_, 2, v_v_3430_);
                    leanh::lean_ctor_set(v___x_3425_, 1, v_k_3429_);
                    leanh::lean_ctor_set(v___x_3425_, 0, v___x_3441_);
                    v___x_3450_ = v___x_3425_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 3, v___y_3443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 4, v___x_3448_);
                    v___x_3450_ = v_reuseFailAlloc_3451_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3450_;
            }
            8 => {
                v___x_3456_ = lean_nat_add(v___x_3453_, v___y_3455_);
                leanh::lean_dec(v___y_3455_);
                leanh::lean_dec(v___x_3453_);
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v_l_3431_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v_l_3413_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3412_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3411_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3456_);
                    v___x_3458_ = v___x_3405_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_k_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_v_3412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_l_3413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_l_3431_);
                    v___x_3458_ = v_reuseFailAlloc_3462_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3459_ = lean_nat_add(v___x_3439_, v_size_3409_);
                if leanh::lean_obj_tag(v_r_3432_) == 0 {
                    v_size_3460_ = leanh::lean_ctor_get(v_r_3432_, 0);
                    leanh::lean_inc(v_size_3460_);
                    v___y_3443_ = v___x_3458_;
                    v___y_3444_ = v___x_3459_;
                    v___y_3445_ = v_size_3460_;
                    state = 5;
                    continue;
                } else {
                    v___x_3461_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3443_ = v___x_3458_;
                    v___y_3444_ = v___x_3459_;
                    v___y_3445_ = v___x_3461_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3484_ = (!leanh::lean_is_exclusive(v_r_3403_)) as u8;
                if v_isSharedCheck_3484_ == 0 {
                    v_unused_3485_ = leanh::lean_ctor_get(v_r_3403_, 4);
                    leanh::lean_dec(v_unused_3485_);
                    v_unused_3486_ = leanh::lean_ctor_get(v_r_3403_, 3);
                    leanh::lean_dec(v_unused_3486_);
                    v_unused_3487_ = leanh::lean_ctor_get(v_r_3403_, 2);
                    leanh::lean_dec(v_unused_3487_);
                    v_unused_3488_ = leanh::lean_ctor_get(v_r_3403_, 1);
                    leanh::lean_dec(v_unused_3488_);
                    v_unused_3489_ = leanh::lean_ctor_get(v_r_3403_, 0);
                    leanh::lean_dec(v_unused_3489_);
                    v___x_3479_ = v_r_3403_;
                    v_isShared_3480_ = v_isSharedCheck_3484_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_3403_);
                    v___x_3479_ = leanh::lean_box(0);
                    v_isShared_3480_ = v_isSharedCheck_3484_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3480_ == 0 {
                    leanh::lean_ctor_set(v___x_3479_, 4, v___x_3477_);
                    leanh::lean_ctor_set(v___x_3479_, 3, v_l_3413_);
                    leanh::lean_ctor_set(v___x_3479_, 2, v_v_3412_);
                    leanh::lean_ctor_set(v___x_3479_, 1, v_k_3411_);
                    leanh::lean_ctor_set(v___x_3479_, 0, v___x_3473_);
                    v___x_3482_ = v___x_3479_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_l_3413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 4, v___x_3477_);
                    v___x_3482_ = v_reuseFailAlloc_3483_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3482_;
            }
            13 => {
                return v___x_3505_;
            }
            14 => {
                v_size_3515_ = leanh::lean_ctor_get(v_r_3508_, 0);
                v___x_3516_ = leanh::lean_unsigned_to_nat(1);
                v___x_3517_ = lean_nat_add(v___x_3516_, v_size_3509_);
                leanh::lean_dec(v_size_3509_);
                v___x_3518_ = lean_nat_add(v___x_3516_, v_size_3515_);
                if v_isShared_3514_ == 0 {
                    leanh::lean_ctor_set(v___x_3513_, 4, v_r_3403_);
                    leanh::lean_ctor_set(v___x_3513_, 3, v_r_3508_);
                    leanh::lean_ctor_set(v___x_3513_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3513_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3518_);
                    v___x_3520_ = v___x_3513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_r_3508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_r_3403_);
                    v___x_3520_ = v_reuseFailAlloc_3524_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3520_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3511_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3510_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3517_);
                    v___x_3522_ = v___x_3405_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 4, v___x_3520_);
                    v___x_3522_ = v_reuseFailAlloc_3523_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3522_;
            }
            17 => {
                v___x_3533_ = leanh::lean_unsigned_to_nat(3);
                v___x_3534_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3532_ == 0 {
                    leanh::lean_ctor_set(v___x_3531_, 3, v_r_3508_);
                    leanh::lean_ctor_set(v___x_3531_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3531_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3531_, 0, v___x_3534_);
                    v___x_3536_ = v___x_3531_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_r_3508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_r_3508_);
                    v___x_3536_ = v_reuseFailAlloc_3540_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3536_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3529_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3528_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3533_);
                    v___x_3538_ = v___x_3405_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_k_3528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_v_3529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 4, v___x_3536_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3538_;
            }
            20 => {
                v_k_3551_ = leanh::lean_ctor_get(v_r_3545_, 1);
                v_v_3552_ = leanh::lean_ctor_get(v_r_3545_, 2);
                v_isSharedCheck_3567_ = (!leanh::lean_is_exclusive(v_r_3545_)) as u8;
                if v_isSharedCheck_3567_ == 0 {
                    v_unused_3568_ = leanh::lean_ctor_get(v_r_3545_, 4);
                    leanh::lean_dec(v_unused_3568_);
                    v_unused_3569_ = leanh::lean_ctor_get(v_r_3545_, 3);
                    leanh::lean_dec(v_unused_3569_);
                    v_unused_3570_ = leanh::lean_ctor_get(v_r_3545_, 0);
                    leanh::lean_dec(v_unused_3570_);
                    v___x_3554_ = v_r_3545_;
                    v_isShared_3555_ = v_isSharedCheck_3567_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3552_);
                    leanh::lean_inc(v_k_3551_);
                    leanh::lean_dec(v_r_3545_);
                    v___x_3554_ = leanh::lean_box(0);
                    v_isShared_3555_ = v_isSharedCheck_3567_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3556_ = leanh::lean_unsigned_to_nat(3);
                v___x_3557_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3555_ == 0 {
                    leanh::lean_ctor_set(v___x_3554_, 4, v_l_3507_);
                    leanh::lean_ctor_set(v___x_3554_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v___x_3554_, 2, v_v_3547_);
                    leanh::lean_ctor_set(v___x_3554_, 1, v_k_3546_);
                    leanh::lean_ctor_set(v___x_3554_, 0, v___x_3557_);
                    v___x_3559_ = v___x_3554_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_k_3546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_v_3547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 4, v_l_3507_);
                    v___x_3559_ = v_reuseFailAlloc_3566_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_3550_ == 0 {
                    leanh::lean_ctor_set(v___x_3549_, 4, v_l_3507_);
                    leanh::lean_ctor_set(v___x_3549_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3549_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3549_, 0, v___x_3557_);
                    v___x_3561_ = v___x_3549_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_l_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_l_3507_);
                    v___x_3561_ = v_reuseFailAlloc_3565_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3561_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3559_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3552_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3551_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3556_);
                    v___x_3563_ = v___x_3405_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 3, v___x_3559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 4, v___x_3561_);
                    v___x_3563_ = v_reuseFailAlloc_3564_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3563_;
            }
            25 => {
                return v___x_3577_;
            }
            26 => {
                return v___x_3581_;
            }
            27 => {
                return v___x_3584_;
            }
            28 => {
                return v___x_3600_;
            }
            29 => {
                if leanh::lean_obj_tag(v_l_3591_) == 0 {
                    if leanh::lean_obj_tag(v_r_3592_) == 0 {
                        v_size_3605_ = leanh::lean_ctor_get(v_l_3591_, 0);
                        v_k_3606_ = leanh::lean_ctor_get(v_l_3591_, 1);
                        v_v_3607_ = leanh::lean_ctor_get(v_l_3591_, 2);
                        v_l_3608_ = leanh::lean_ctor_get(v_l_3591_, 3);
                        v_r_3609_ = leanh::lean_ctor_get(v_l_3591_, 4);
                        v_size_3610_ = leanh::lean_ctor_get(v_r_3592_, 0);
                        v___x_3611_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3612_ = lean_nat_mul(v___x_3611_, v_size_3610_);
                        v___x_3613_ = lean_nat_dec_lt(v_size_3605_, v___x_3612_);
                        leanh::lean_dec(v___x_3612_);
                        if v___x_3613_ == 0 {
                            leanh::lean_inc(v_r_3609_);
                            leanh::lean_inc(v_l_3608_);
                            leanh::lean_inc(v_v_3607_);
                            leanh::lean_inc(v_k_3606_);
                            v_isSharedCheck_3642_ =
                                (!leanh::lean_is_exclusive(v_l_3591_)) as u8;
                            if v_isSharedCheck_3642_ == 0 {
                                v_unused_3643_ = leanh::lean_ctor_get(v_l_3591_, 4);
                                leanh::lean_dec(v_unused_3643_);
                                v_unused_3644_ = leanh::lean_ctor_get(v_l_3591_, 3);
                                leanh::lean_dec(v_unused_3644_);
                                v_unused_3645_ = leanh::lean_ctor_get(v_l_3591_, 2);
                                leanh::lean_dec(v_unused_3645_);
                                v_unused_3646_ = leanh::lean_ctor_get(v_l_3591_, 1);
                                leanh::lean_dec(v_unused_3646_);
                                v_unused_3647_ = leanh::lean_ctor_get(v_l_3591_, 0);
                                leanh::lean_dec(v_unused_3647_);
                                v___x_3615_ = v_l_3591_;
                                v_isShared_3616_ = v_isSharedCheck_3642_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_3591_);
                                v___x_3615_ = leanh::lean_box(0);
                                v_isShared_3616_ = v_isSharedCheck_3642_;
                                state = 30;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3405_);
                            v___x_3648_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3649_ = lean_nat_add(v___x_3648_, v_size_3587_);
                            v___x_3650_ = lean_nat_add(v___x_3649_, v_size_3588_);
                            leanh::lean_dec(v_size_3588_);
                            v___x_3651_ = lean_nat_add(v___x_3649_, v_size_3605_);
                            leanh::lean_dec(v___x_3649_);
                            leanh::lean_inc_ref(v_l_3402_);
                            if v_isShared_3604_ == 0 {
                                leanh::lean_ctor_set(v___x_3603_, 4, v_l_3591_);
                                leanh::lean_ctor_set(v___x_3603_, 3, v_l_3402_);
                                leanh::lean_ctor_set(v___x_3603_, 2, v_v_3401_);
                                leanh::lean_ctor_set(v___x_3603_, 1, v_k_3400_);
                                leanh::lean_ctor_set(v___x_3603_, 0, v___x_3651_);
                                v___x_3653_ = v___x_3603_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3666_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3651_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3400_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3401_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_l_3402_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_l_3591_);
                                v___x_3653_ = v_reuseFailAlloc_3666_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_3591_, 5);
                        leanh::lean_del_object(v___x_3603_);
                        leanh::lean_dec(v_v_3590_);
                        leanh::lean_dec(v_k_3589_);
                        leanh::lean_dec(v_size_3588_);
                        leanh::lean_dec_ref_known(v_l_3402_, 5);
                        leanh::lean_del_object(v___x_3405_);
                        leanh::lean_dec(v_v_3401_);
                        leanh::lean_dec(v_k_3400_);
                        v___x_3667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
                        v___x_3668_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_3667_);
                        return v___x_3668_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3603_);
                    leanh::lean_dec(v_r_3592_);
                    leanh::lean_dec(v_v_3590_);
                    leanh::lean_dec(v_k_3589_);
                    leanh::lean_dec(v_size_3588_);
                    leanh::lean_dec_ref_known(v_l_3402_, 5);
                    leanh::lean_del_object(v___x_3405_);
                    leanh::lean_dec(v_v_3401_);
                    leanh::lean_dec(v_k_3400_);
                    v___x_3669_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
                    v___x_3670_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_3669_);
                    return v___x_3670_;
                }
            }
            30 => {
                v___x_3617_ = leanh::lean_unsigned_to_nat(1);
                v___x_3618_ = lean_nat_add(v___x_3617_, v_size_3587_);
                v___x_3619_ = lean_nat_add(v___x_3618_, v_size_3588_);
                leanh::lean_dec(v_size_3588_);
                if leanh::lean_obj_tag(v_l_3608_) == 0 {
                    v_size_3640_ = leanh::lean_ctor_get(v_l_3608_, 0);
                    leanh::lean_inc(v_size_3640_);
                    v___y_3632_ = v_size_3640_;
                    state = 34;
                    continue;
                } else {
                    v___x_3641_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3632_ = v___x_3641_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3624_ = lean_nat_add(v___y_3622_, v___y_3623_);
                leanh::lean_dec(v___y_3623_);
                leanh::lean_dec(v___y_3622_);
                if v_isShared_3616_ == 0 {
                    leanh::lean_ctor_set(v___x_3615_, 4, v_r_3592_);
                    leanh::lean_ctor_set(v___x_3615_, 3, v_r_3609_);
                    leanh::lean_ctor_set(v___x_3615_, 2, v_v_3590_);
                    leanh::lean_ctor_set(v___x_3615_, 1, v_k_3589_);
                    leanh::lean_ctor_set(v___x_3615_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3615_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_r_3609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_r_3592_);
                    v___x_3626_ = v_reuseFailAlloc_3630_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3604_ == 0 {
                    leanh::lean_ctor_set(v___x_3603_, 4, v___x_3626_);
                    leanh::lean_ctor_set(v___x_3603_, 3, v___y_3621_);
                    leanh::lean_ctor_set(v___x_3603_, 2, v_v_3607_);
                    leanh::lean_ctor_set(v___x_3603_, 1, v_k_3606_);
                    leanh::lean_ctor_set(v___x_3603_, 0, v___x_3619_);
                    v___x_3628_ = v___x_3603_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 3, v___y_3621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 4, v___x_3626_);
                    v___x_3628_ = v_reuseFailAlloc_3629_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3628_;
            }
            34 => {
                v___x_3633_ = lean_nat_add(v___x_3618_, v___y_3632_);
                leanh::lean_dec(v___y_3632_);
                leanh::lean_dec(v___x_3618_);
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v_l_3608_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3633_);
                    v___x_3635_ = v___x_3405_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_l_3402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_l_3608_);
                    v___x_3635_ = v_reuseFailAlloc_3639_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3636_ = lean_nat_add(v___x_3617_, v_size_3610_);
                if leanh::lean_obj_tag(v_r_3609_) == 0 {
                    v_size_3637_ = leanh::lean_ctor_get(v_r_3609_, 0);
                    leanh::lean_inc(v_size_3637_);
                    v___y_3621_ = v___x_3635_;
                    v___y_3622_ = v___x_3636_;
                    v___y_3623_ = v_size_3637_;
                    state = 31;
                    continue;
                } else {
                    v___x_3638_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3621_ = v___x_3635_;
                    v___y_3622_ = v___x_3636_;
                    v___y_3623_ = v___x_3638_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3660_ = (!leanh::lean_is_exclusive(v_l_3402_)) as u8;
                if v_isSharedCheck_3660_ == 0 {
                    v_unused_3661_ = leanh::lean_ctor_get(v_l_3402_, 4);
                    leanh::lean_dec(v_unused_3661_);
                    v_unused_3662_ = leanh::lean_ctor_get(v_l_3402_, 3);
                    leanh::lean_dec(v_unused_3662_);
                    v_unused_3663_ = leanh::lean_ctor_get(v_l_3402_, 2);
                    leanh::lean_dec(v_unused_3663_);
                    v_unused_3664_ = leanh::lean_ctor_get(v_l_3402_, 1);
                    leanh::lean_dec(v_unused_3664_);
                    v_unused_3665_ = leanh::lean_ctor_get(v_l_3402_, 0);
                    leanh::lean_dec(v_unused_3665_);
                    v___x_3655_ = v_l_3402_;
                    v_isShared_3656_ = v_isSharedCheck_3660_;
                    state = 37;
                    continue;
                } else {
                    leanh::lean_dec(v_l_3402_);
                    v___x_3655_ = leanh::lean_box(0);
                    v_isShared_3656_ = v_isSharedCheck_3660_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3656_ == 0 {
                    leanh::lean_ctor_set(v___x_3655_, 4, v_r_3592_);
                    leanh::lean_ctor_set(v___x_3655_, 3, v___x_3653_);
                    leanh::lean_ctor_set(v___x_3655_, 2, v_v_3590_);
                    leanh::lean_ctor_set(v___x_3655_, 1, v_k_3589_);
                    leanh::lean_ctor_set(v___x_3655_, 0, v___x_3650_);
                    v___x_3658_ = v___x_3655_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3659_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 3, v___x_3653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_r_3592_);
                    v___x_3658_ = v_reuseFailAlloc_3659_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3658_;
            }
            39 => {
                return v___x_3681_;
            }
            40 => {
                v_size_3691_ = leanh::lean_ctor_get(v_l_3683_, 0);
                v___x_3692_ = leanh::lean_unsigned_to_nat(1);
                v___x_3693_ = lean_nat_add(v___x_3692_, v_size_3685_);
                leanh::lean_dec(v_size_3685_);
                v___x_3694_ = lean_nat_add(v___x_3692_, v_size_3691_);
                if v_isShared_3690_ == 0 {
                    leanh::lean_ctor_set(v___x_3689_, 4, v_l_3683_);
                    leanh::lean_ctor_set(v___x_3689_, 3, v_l_3402_);
                    leanh::lean_ctor_set(v___x_3689_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3689_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3689_, 0, v___x_3694_);
                    v___x_3696_ = v___x_3689_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_l_3402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 4, v_l_3683_);
                    v___x_3696_ = v_reuseFailAlloc_3700_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v_r_3684_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3696_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3687_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3686_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3693_);
                    v___x_3698_ = v___x_3405_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_k_3686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_v_3687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 3, v___x_3696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_r_3684_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3698_;
            }
            43 => {
                v_k_3709_ = leanh::lean_ctor_get(v_l_3683_, 1);
                v_v_3710_ = leanh::lean_ctor_get(v_l_3683_, 2);
                v_isSharedCheck_3725_ = (!leanh::lean_is_exclusive(v_l_3683_)) as u8;
                if v_isSharedCheck_3725_ == 0 {
                    v_unused_3726_ = leanh::lean_ctor_get(v_l_3683_, 4);
                    leanh::lean_dec(v_unused_3726_);
                    v_unused_3727_ = leanh::lean_ctor_get(v_l_3683_, 3);
                    leanh::lean_dec(v_unused_3727_);
                    v_unused_3728_ = leanh::lean_ctor_get(v_l_3683_, 0);
                    leanh::lean_dec(v_unused_3728_);
                    v___x_3712_ = v_l_3683_;
                    v_isShared_3713_ = v_isSharedCheck_3725_;
                    state = 44;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3710_);
                    leanh::lean_inc(v_k_3709_);
                    leanh::lean_dec(v_l_3683_);
                    v___x_3712_ = leanh::lean_box(0);
                    v_isShared_3713_ = v_isSharedCheck_3725_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3714_ = leanh::lean_unsigned_to_nat(3);
                v___x_3715_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3713_ == 0 {
                    leanh::lean_ctor_set(v___x_3712_, 4, v_r_3684_);
                    leanh::lean_ctor_set(v___x_3712_, 3, v_r_3684_);
                    leanh::lean_ctor_set(v___x_3712_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3712_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3712_, 0, v___x_3715_);
                    v___x_3717_ = v___x_3712_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3724_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_r_3684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_r_3684_);
                    v___x_3717_ = v_reuseFailAlloc_3724_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3708_ == 0 {
                    leanh::lean_ctor_set(v___x_3707_, 3, v_r_3684_);
                    leanh::lean_ctor_set(v___x_3707_, 0, v___x_3715_);
                    v___x_3719_ = v___x_3707_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_k_3704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_v_3705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_r_3684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_r_3684_);
                    v___x_3719_ = v_reuseFailAlloc_3723_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v___x_3719_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3717_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3710_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3709_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3714_);
                    v___x_3721_ = v___x_3405_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_k_3709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_v_3710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 3, v___x_3717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 4, v___x_3719_);
                    v___x_3721_ = v_reuseFailAlloc_3722_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3721_;
            }
            48 => {
                v___x_3739_ = leanh::lean_unsigned_to_nat(3);
                v___x_3740_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3738_ == 0 {
                    leanh::lean_ctor_set(v___x_3737_, 4, v_l_3683_);
                    leanh::lean_ctor_set(v___x_3737_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v___x_3737_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v___x_3737_, 0, v___x_3740_);
                    v___x_3742_ = v___x_3737_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_k_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_v_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_l_3683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 4, v_l_3683_);
                    v___x_3742_ = v_reuseFailAlloc_3746_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_3406_ == 0 {
                    leanh::lean_ctor_set(v___x_3405_, 4, v_r_3733_);
                    leanh::lean_ctor_set(v___x_3405_, 3, v___x_3742_);
                    leanh::lean_ctor_set(v___x_3405_, 2, v_v_3735_);
                    leanh::lean_ctor_set(v___x_3405_, 1, v_k_3734_);
                    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3739_);
                    v___x_3744_ = v___x_3405_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3745_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_k_3734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_v_3735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 3, v___x_3742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_r_3733_);
                    v___x_3744_ = v_reuseFailAlloc_3745_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3744_;
            }
            51 => {
                return v___x_3753_;
            }
            52 => {
                return v___x_3757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_objectCore(
    mut v_kvs_3780_: *mut leanh::LeanObject,
    mut v_a_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: u32 = 0;
    let mut v___x_3787_: u32 = 0;
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3793_: u8 = 0;
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v_fst_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: u32 = 0;
    let mut v___x_3820_: u32 = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3832_: u8 = 0;
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3845_: u32 = 0;
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u32 = 0;
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: u32 = 0;
    let mut v___x_3850_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3868_: u8 = 0;
    let mut v_unused_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3871_: u8 = 0;
    let mut v_pos_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_reuseFailAlloc_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut v_pos_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut v_reuseFailAlloc_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3894_: u8 = 0;
    let mut v_unused_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3782_ = leanh::lean_ctor_get(v_a_3781_, 0);
                v_snd_3783_ = leanh::lean_ctor_get(v_a_3781_, 1);
                v___x_3784_ = lean_string_utf8_byte_size(v_fst_3782_);
                v___x_3785_ = lean_nat_dec_eq(v_snd_3783_, v___x_3784_);
                if v___x_3785_ == 0 {
                    v___x_3786_ = lean_string_utf8_get_fast(v_fst_3782_, v_snd_3783_);
                    v___x_3787_ = 34;
                    v___x_3788_ = lean_uint32_dec_eq(v___x_3786_, v___x_3787_);
                    if v___x_3788_ == 0 {
                        leanh::lean_dec(v_kvs_3780_);
                        v___x_3789_ = l_Lean_Json_Parser_objectCore___closed__1;
                        v___x_3790_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3790_, 0, v_a_3781_);
                        leanh::lean_ctor_set(v___x_3790_, 1, v___x_3789_);
                        return v___x_3790_;
                    } else {
                        leanh::lean_inc(v_snd_3783_);
                        leanh::lean_inc(v_fst_3782_);
                        v_isSharedCheck_3894_ = (!leanh::lean_is_exclusive(v_a_3781_)) as u8;
                        if v_isSharedCheck_3894_ == 0 {
                            v_unused_3895_ = leanh::lean_ctor_get(v_a_3781_, 1);
                            leanh::lean_dec(v_unused_3895_);
                            v_unused_3896_ = leanh::lean_ctor_get(v_a_3781_, 0);
                            leanh::lean_dec(v_unused_3896_);
                            v___x_3792_ = v_a_3781_;
                            v_isShared_3793_ = v_isSharedCheck_3894_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3781_);
                            v___x_3792_ = leanh::lean_box(0);
                            v_isShared_3793_ = v_isSharedCheck_3894_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_kvs_3780_);
                    v___x_3897_ = leanh::lean_box(0);
                    v___x_3898_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3898_, 0, v_a_3781_);
                    leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                    return v___x_3898_;
                }
            }
            1 => {
                v___x_3794_ = lean_string_utf8_next_fast(v_fst_3782_, v_snd_3783_);
                leanh::lean_dec(v_snd_3783_);
                if v_isShared_3793_ == 0 {
                    leanh::lean_ctor_set(v___x_3792_, 1, v___x_3794_);
                    v___x_3796_ = v___x_3792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_fst_3782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___x_3794_);
                    v___x_3796_ = v_reuseFailAlloc_3893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3797_ = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
                v___x_3798_ = l_Lean_Json_Parser_strCore(v___x_3797_, v___x_3796_);
                if leanh::lean_obj_tag(v___x_3798_) == 0 {
                    v_pos_3799_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    v_res_3800_ = leanh::lean_ctor_get(v___x_3798_, 1);
                    v_isSharedCheck_3883_ = (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3802_ = v___x_3798_;
                        v_isShared_3803_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_3800_);
                        leanh::lean_inc(v_pos_3799_);
                        leanh::lean_dec(v___x_3798_);
                        v___x_3802_ = leanh::lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_kvs_3780_);
                    v_pos_3884_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    v_err_3885_ = leanh::lean_ctor_get(v___x_3798_, 1);
                    v_isSharedCheck_3892_ = (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3892_ == 0 {
                        v___x_3887_ = v___x_3798_;
                        v_isShared_3888_ = v_isSharedCheck_3892_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3885_);
                        leanh::lean_inc(v_pos_3884_);
                        leanh::lean_dec(v___x_3798_);
                        v___x_3887_ = leanh::lean_box(0);
                        v_isShared_3888_ = v_isSharedCheck_3892_;
                        state = 17;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3804_ = leanh::lean_ctor_get(v_pos_3799_, 0);
                v_snd_3805_ = leanh::lean_ctor_get(v_pos_3799_, 1);
                v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v_pos_3799_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v___x_3807_ = v_pos_3799_;
                    v_isShared_3808_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3805_);
                    leanh::lean_inc(v_fst_3804_);
                    leanh::lean_dec(v_pos_3799_);
                    v___x_3807_ = leanh::lean_box(0);
                    v_isShared_3808_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3809_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_3804_,
                        v_snd_3805_,
                    );
                leanh::lean_inc(v___x_3809_);
                leanh::lean_inc(v_fst_3804_);
                if v_isShared_3808_ == 0 {
                    leanh::lean_ctor_set(v___x_3807_, 1, v___x_3809_);
                    v___x_3811_ = v___x_3807_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_fst_3804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3809_);
                    v___x_3811_ = v_reuseFailAlloc_3881_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3817_ = lean_string_utf8_byte_size(v_fst_3804_);
                v___x_3818_ = lean_nat_dec_eq(v___x_3809_, v___x_3817_);
                if v___x_3818_ == 0 {
                    if v___x_3788_ == 0 {
                        leanh::lean_dec(v___x_3809_);
                        leanh::lean_dec(v_fst_3804_);
                        leanh::lean_dec(v_res_3800_);
                        leanh::lean_dec(v_kvs_3780_);
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3802_);
                        v___x_3819_ = lean_string_utf8_get_fast(v_fst_3804_, v___x_3809_);
                        v___x_3820_ = 58;
                        v___x_3821_ = lean_uint32_dec_eq(v___x_3819_, v___x_3820_);
                        if v___x_3821_ == 0 {
                            leanh::lean_dec(v___x_3809_);
                            leanh::lean_dec(v_fst_3804_);
                            leanh::lean_dec(v_res_3800_);
                            leanh::lean_dec(v_kvs_3780_);
                            v___x_3822_ = l_Lean_Json_Parser_objectCore___closed__3;
                            v___x_3823_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3823_, 0, v___x_3811_);
                            leanh::lean_ctor_set(v___x_3823_, 1, v___x_3822_);
                            return v___x_3823_;
                        } else {
                            leanh::lean_dec_ref(v___x_3811_);
                            v___x_3824_ = lean_string_utf8_next_fast(v_fst_3804_, v___x_3809_);
                            leanh::lean_dec(v___x_3809_);
                            v___x_3825_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_3804_, v___x_3824_);
                            v___x_3826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3826_, 0, v_fst_3804_);
                            leanh::lean_ctor_set(v___x_3826_, 1, v___x_3825_);
                            v___x_3827_ = l_Lean_Json_Parser_anyCore(v___x_3826_);
                            if leanh::lean_obj_tag(v___x_3827_) == 0 {
                                v_pos_3828_ = leanh::lean_ctor_get(v___x_3827_, 0);
                                v_res_3829_ = leanh::lean_ctor_get(v___x_3827_, 1);
                                v_isSharedCheck_3871_ =
                                    (!leanh::lean_is_exclusive(v___x_3827_)) as u8;
                                if v_isSharedCheck_3871_ == 0 {
                                    v___x_3831_ = v___x_3827_;
                                    v_isShared_3832_ = v_isSharedCheck_3871_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_res_3829_);
                                    leanh::lean_inc(v_pos_3828_);
                                    leanh::lean_dec(v___x_3827_);
                                    v___x_3831_ = leanh::lean_box(0);
                                    v_isShared_3832_ = v_isSharedCheck_3871_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_res_3800_);
                                leanh::lean_dec(v_kvs_3780_);
                                v_pos_3872_ = leanh::lean_ctor_get(v___x_3827_, 0);
                                v_err_3873_ = leanh::lean_ctor_get(v___x_3827_, 1);
                                v_isSharedCheck_3880_ =
                                    (!leanh::lean_is_exclusive(v___x_3827_)) as u8;
                                if v_isSharedCheck_3880_ == 0 {
                                    v___x_3875_ = v___x_3827_;
                                    v_isShared_3876_ = v_isSharedCheck_3880_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_err_3873_);
                                    leanh::lean_inc(v_pos_3872_);
                                    leanh::lean_dec(v___x_3827_);
                                    v___x_3875_ = leanh::lean_box(0);
                                    v_isShared_3876_ = v_isSharedCheck_3880_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3809_);
                    leanh::lean_dec(v_fst_3804_);
                    leanh::lean_dec(v_res_3800_);
                    leanh::lean_dec(v_kvs_3780_);
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3813_ = leanh::lean_box(0);
                if v_isShared_3803_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3802_, 1);
                    leanh::lean_ctor_set(v___x_3802_, 1, v___x_3813_);
                    leanh::lean_ctor_set(v___x_3802_, 0, v___x_3811_);
                    v___x_3815_ = v___x_3802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3815_;
            }
            8 => {
                v_fst_3838_ = leanh::lean_ctor_get(v_pos_3828_, 0);
                v_snd_3839_ = leanh::lean_ctor_get(v_pos_3828_, 1);
                v___x_3840_ = lean_string_utf8_byte_size(v_fst_3838_);
                v___x_3841_ = lean_nat_dec_eq(v_snd_3839_, v___x_3840_);
                if v___x_3841_ == 0 {
                    if v___x_3821_ == 0 {
                        leanh::lean_dec(v_res_3829_);
                        leanh::lean_dec(v_res_3800_);
                        leanh::lean_dec(v_kvs_3780_);
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3839_);
                        leanh::lean_inc(v_fst_3838_);
                        leanh::lean_del_object(v___x_3831_);
                        v_isSharedCheck_3868_ =
                            (!leanh::lean_is_exclusive(v_pos_3828_)) as u8;
                        if v_isSharedCheck_3868_ == 0 {
                            v_unused_3869_ = leanh::lean_ctor_get(v_pos_3828_, 1);
                            leanh::lean_dec(v_unused_3869_);
                            v_unused_3870_ = leanh::lean_ctor_get(v_pos_3828_, 0);
                            leanh::lean_dec(v_unused_3870_);
                            v___x_3843_ = v_pos_3828_;
                            v_isShared_3844_ = v_isSharedCheck_3868_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3828_);
                            v___x_3843_ = leanh::lean_box(0);
                            v_isShared_3844_ = v_isSharedCheck_3868_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_res_3829_);
                    leanh::lean_dec(v_res_3800_);
                    leanh::lean_dec(v_kvs_3780_);
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3834_ = leanh::lean_box(0);
                if v_isShared_3832_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3831_, 1);
                    leanh::lean_ctor_set(v___x_3831_, 1, v___x_3834_);
                    v___x_3836_ = v___x_3831_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3837_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_pos_3828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3834_);
                    v___x_3836_ = v_reuseFailAlloc_3837_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3836_;
            }
            11 => {
                v___x_3845_ = lean_string_utf8_get_fast(v_fst_3838_, v_snd_3839_);
                v___x_3846_ = lean_string_utf8_next_fast(v_fst_3838_, v_snd_3839_);
                leanh::lean_dec(v_snd_3839_);
                v___x_3847_ = 125;
                v___x_3848_ = lean_uint32_dec_eq(v___x_3845_, v___x_3847_);
                if v___x_3848_ == 0 {
                    v___x_3849_ = 44;
                    v___x_3850_ = lean_uint32_dec_eq(v___x_3845_, v___x_3849_);
                    if v___x_3850_ == 0 {
                        leanh::lean_dec(v_res_3829_);
                        leanh::lean_dec(v_res_3800_);
                        leanh::lean_dec(v_kvs_3780_);
                        if v_isShared_3844_ == 0 {
                            leanh::lean_ctor_set(v___x_3843_, 1, v___x_3846_);
                            v___x_3852_ = v___x_3843_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3855_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_fst_3838_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3846_);
                            v___x_3852_ = v_reuseFailAlloc_3855_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___x_3856_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_3838_, v___x_3846_);
                        if v_isShared_3844_ == 0 {
                            leanh::lean_ctor_set(v___x_3843_, 1, v___x_3856_);
                            v___x_3858_ = v___x_3843_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_3861_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_fst_3838_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3856_);
                            v___x_3858_ = v_reuseFailAlloc_3861_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    v___x_3862_ =
                        l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                            v_fst_3838_,
                            v___x_3846_,
                        );
                    if v_isShared_3844_ == 0 {
                        leanh::lean_ctor_set(v___x_3843_, 1, v___x_3862_);
                        v___x_3864_ = v___x_3843_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_fst_3838_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3862_);
                        v___x_3864_ = v_reuseFailAlloc_3867_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3853_ = l_Lean_Json_Parser_objectCore___closed__5;
                v___x_3854_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3854_, 0, v___x_3852_);
                leanh::lean_ctor_set(v___x_3854_, 1, v___x_3853_);
                return v___x_3854_;
            }
            13 => {
                v___x_3859_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_3800_, v_res_3829_, v_kvs_3780_);
                v_kvs_3780_ = v___x_3859_;
                v_a_3781_ = v___x_3858_;
                state = 0;
                continue;
            }
            14 => {
                v___x_3865_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_3800_, v_res_3829_, v_kvs_3780_);
                v___x_3866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                leanh::lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                return v___x_3866_;
            }
            15 => {
                if v_isShared_3876_ == 0 {
                    v___x_3878_ = v___x_3875_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_pos_3872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_err_3873_);
                    v___x_3878_ = v_reuseFailAlloc_3879_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3878_;
            }
            17 => {
                if v_isShared_3888_ == 0 {
                    v___x_3890_ = v___x_3887_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_pos_3884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_err_3885_);
                    v___x_3890_ = v_reuseFailAlloc_3891_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_anyCore(
    mut v_a_3905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v_fst_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_pos_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v___y_3938_: u8 = 0;
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: u32 = 0;
    let mut v___x_3946_: u32 = 0;
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: u32 = 0;
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: u32 = 0;
    let mut v___x_3951_: u8 = 0;
    let mut v___x_3952_: u32 = 0;
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: u32 = 0;
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: u32 = 0;
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: u32 = 0;
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: u32 = 0;
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: u32 = 0;
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v_fst_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_unused_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_fst_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4005_: u8 = 0;
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_isSharedCheck_4015_: u8 = 0;
    let mut v_unused_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v_fst_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut v_unused_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v_fst_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v_pos_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4089_: u8 = 0;
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_reuseFailAlloc_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut v_unused_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4100_: u8 = 0;
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4106_: u8 = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: u32 = 0;
    let mut v___x_4110_: u32 = 0;
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_pos_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_unused_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: u8 = 0;
    let mut v___x_4154_: u32 = 0;
    let mut v___x_4155_: u32 = 0;
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4169_: u8 = 0;
    let mut v_pos_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4178_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_unused_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3941_ = leanh::lean_ctor_get(v_a_3905_, 0);
                v_snd_3942_ = leanh::lean_ctor_get(v_a_3905_, 1);
                v___x_3943_ = lean_string_utf8_byte_size(v_fst_3941_);
                v___x_3944_ = lean_nat_dec_eq(v_snd_3942_, v___x_3943_);
                if v___x_3944_ == 0 {
                    v___x_3945_ = lean_string_utf8_get_fast(v_fst_3941_, v_snd_3942_);
                    v___x_3946_ = 91;
                    v___x_3947_ = lean_uint32_dec_eq(v___x_3945_, v___x_3946_);
                    if v___x_3947_ == 0 {
                        v___x_3948_ = 123;
                        v___x_3949_ = lean_uint32_dec_eq(v___x_3945_, v___x_3948_);
                        if v___x_3949_ == 0 {
                            v___x_3950_ = 34;
                            v___x_3951_ = lean_uint32_dec_eq(v___x_3945_, v___x_3950_);
                            if v___x_3951_ == 0 {
                                v___x_3952_ = 102;
                                v___x_3953_ = lean_uint32_dec_eq(v___x_3945_, v___x_3952_);
                                if v___x_3953_ == 0 {
                                    v___x_3954_ = 116;
                                    v___x_3955_ = lean_uint32_dec_eq(v___x_3945_, v___x_3954_);
                                    if v___x_3955_ == 0 {
                                        v___x_3956_ = 110;
                                        v___x_3957_ = lean_uint32_dec_eq(v___x_3945_, v___x_3956_);
                                        if v___x_3957_ == 0 {
                                            v___x_3958_ = 45;
                                            v___x_3959_ =
                                                lean_uint32_dec_eq(v___x_3945_, v___x_3958_);
                                            if v___x_3959_ == 0 {
                                                v___x_3960_ = 48;
                                                v___x_3961_ =
                                                    lean_uint32_dec_le(v___x_3960_, v___x_3945_);
                                                if v___x_3961_ == 0 {
                                                    v___y_3938_ = v___x_3961_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    v___x_3962_ = 57;
                                                    v___x_3963_ = lean_uint32_dec_le(
                                                        v___x_3945_,
                                                        v___x_3962_,
                                                    );
                                                    v___y_3938_ = v___x_3963_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___x_3964_ = l_Lean_Json_Parser_anyCore___closed__2;
                                            v___x_3965_ = l_Std_Internal_Parsec_String_pstring(
                                                v___x_3964_,
                                                v_a_3905_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3965_) == 0 {
                                                v_pos_3966_ =
                                                    leanh::lean_ctor_get(v___x_3965_, 0);
                                                v_isSharedCheck_3984_ =
                                                    (!leanh::lean_is_exclusive(v___x_3965_))
                                                        as u8;
                                                if v_isSharedCheck_3984_ == 0 {
                                                    v_unused_3985_ =
                                                        leanh::lean_ctor_get(v___x_3965_, 1);
                                                    leanh::lean_dec(v_unused_3985_);
                                                    v___x_3968_ = v___x_3965_;
                                                    v_isShared_3969_ = v_isSharedCheck_3984_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_pos_3966_);
                                                    leanh::lean_dec(v___x_3965_);
                                                    v___x_3968_ = leanh::lean_box(0);
                                                    v_isShared_3969_ = v_isSharedCheck_3984_;
                                                    state = 9;
                                                    continue;
                                                }
                                            } else {
                                                v_pos_3986_ =
                                                    leanh::lean_ctor_get(v___x_3965_, 0);
                                                v_err_3987_ =
                                                    leanh::lean_ctor_get(v___x_3965_, 1);
                                                v_isSharedCheck_3994_ =
                                                    (!leanh::lean_is_exclusive(v___x_3965_))
                                                        as u8;
                                                if v_isSharedCheck_3994_ == 0 {
                                                    v___x_3989_ = v___x_3965_;
                                                    v_isShared_3990_ = v_isSharedCheck_3994_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_err_3987_);
                                                    leanh::lean_inc(v_pos_3986_);
                                                    leanh::lean_dec(v___x_3965_);
                                                    v___x_3989_ = leanh::lean_box(0);
                                                    v_isShared_3990_ = v_isSharedCheck_3994_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_3995_ = l_Lean_Json_Parser_anyCore___closed__3;
                                        v___x_3996_ = l_Std_Internal_Parsec_String_pstring(
                                            v___x_3995_,
                                            v_a_3905_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3996_) == 0 {
                                            v_pos_3997_ =
                                                leanh::lean_ctor_get(v___x_3996_, 0);
                                            v_isSharedCheck_4015_ =
                                                (!leanh::lean_is_exclusive(v___x_3996_))
                                                    as u8;
                                            if v_isSharedCheck_4015_ == 0 {
                                                v_unused_4016_ =
                                                    leanh::lean_ctor_get(v___x_3996_, 1);
                                                leanh::lean_dec(v_unused_4016_);
                                                v___x_3999_ = v___x_3996_;
                                                v_isShared_4000_ = v_isSharedCheck_4015_;
                                                state = 15;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_pos_3997_);
                                                leanh::lean_dec(v___x_3996_);
                                                v___x_3999_ = leanh::lean_box(0);
                                                v_isShared_4000_ = v_isSharedCheck_4015_;
                                                state = 15;
                                                continue;
                                            }
                                        } else {
                                            v_pos_4017_ =
                                                leanh::lean_ctor_get(v___x_3996_, 0);
                                            v_err_4018_ =
                                                leanh::lean_ctor_get(v___x_3996_, 1);
                                            v_isSharedCheck_4025_ =
                                                (!leanh::lean_is_exclusive(v___x_3996_))
                                                    as u8;
                                            if v_isSharedCheck_4025_ == 0 {
                                                v___x_4020_ = v___x_3996_;
                                                v_isShared_4021_ = v_isSharedCheck_4025_;
                                                state = 19;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_err_4018_);
                                                leanh::lean_inc(v_pos_4017_);
                                                leanh::lean_dec(v___x_3996_);
                                                v___x_4020_ = leanh::lean_box(0);
                                                v_isShared_4021_ = v_isSharedCheck_4025_;
                                                state = 19;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_4026_ = l_Lean_Json_Parser_anyCore___closed__4;
                                    v___x_4027_ = l_Std_Internal_Parsec_String_pstring(
                                        v___x_4026_,
                                        v_a_3905_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4027_) == 0 {
                                        v_pos_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                                        v_isSharedCheck_4046_ =
                                            (!leanh::lean_is_exclusive(v___x_4027_)) as u8;
                                        if v_isSharedCheck_4046_ == 0 {
                                            v_unused_4047_ =
                                                leanh::lean_ctor_get(v___x_4027_, 1);
                                            leanh::lean_dec(v_unused_4047_);
                                            v___x_4030_ = v___x_4027_;
                                            v_isShared_4031_ = v_isSharedCheck_4046_;
                                            state = 21;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_pos_4028_);
                                            leanh::lean_dec(v___x_4027_);
                                            v___x_4030_ = leanh::lean_box(0);
                                            v_isShared_4031_ = v_isSharedCheck_4046_;
                                            state = 21;
                                            continue;
                                        }
                                    } else {
                                        v_pos_4048_ = leanh::lean_ctor_get(v___x_4027_, 0);
                                        v_err_4049_ = leanh::lean_ctor_get(v___x_4027_, 1);
                                        v_isSharedCheck_4056_ =
                                            (!leanh::lean_is_exclusive(v___x_4027_)) as u8;
                                        if v_isSharedCheck_4056_ == 0 {
                                            v___x_4051_ = v___x_4027_;
                                            v_isShared_4052_ = v_isSharedCheck_4056_;
                                            state = 25;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_err_4049_);
                                            leanh::lean_inc(v_pos_4048_);
                                            leanh::lean_dec(v___x_4027_);
                                            v___x_4051_ = leanh::lean_box(0);
                                            v_isShared_4052_ = v_isSharedCheck_4056_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_inc(v_snd_3942_);
                                leanh::lean_inc(v_fst_3941_);
                                v_isSharedCheck_4095_ =
                                    (!leanh::lean_is_exclusive(v_a_3905_)) as u8;
                                if v_isSharedCheck_4095_ == 0 {
                                    v_unused_4096_ = leanh::lean_ctor_get(v_a_3905_, 1);
                                    leanh::lean_dec(v_unused_4096_);
                                    v_unused_4097_ = leanh::lean_ctor_get(v_a_3905_, 0);
                                    leanh::lean_dec(v_unused_4097_);
                                    v___x_4058_ = v_a_3905_;
                                    v_isShared_4059_ = v_isSharedCheck_4095_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3905_);
                                    v___x_4058_ = leanh::lean_box(0);
                                    v_isShared_4059_ = v_isSharedCheck_4095_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc(v_snd_3942_);
                            leanh::lean_inc(v_fst_3941_);
                            v_isSharedCheck_4140_ =
                                (!leanh::lean_is_exclusive(v_a_3905_)) as u8;
                            if v_isSharedCheck_4140_ == 0 {
                                v_unused_4141_ = leanh::lean_ctor_get(v_a_3905_, 1);
                                leanh::lean_dec(v_unused_4141_);
                                v_unused_4142_ = leanh::lean_ctor_get(v_a_3905_, 0);
                                leanh::lean_dec(v_unused_4142_);
                                v___x_4099_ = v_a_3905_;
                                v_isShared_4100_ = v_isSharedCheck_4140_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3905_);
                                v___x_4099_ = leanh::lean_box(0);
                                v_isShared_4100_ = v_isSharedCheck_4140_;
                                state = 35;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_snd_3942_);
                        leanh::lean_inc(v_fst_3941_);
                        v_isSharedCheck_4185_ = (!leanh::lean_is_exclusive(v_a_3905_)) as u8;
                        if v_isSharedCheck_4185_ == 0 {
                            v_unused_4186_ = leanh::lean_ctor_get(v_a_3905_, 1);
                            leanh::lean_dec(v_unused_4186_);
                            v_unused_4187_ = leanh::lean_ctor_get(v_a_3905_, 0);
                            leanh::lean_dec(v_unused_4187_);
                            v___x_4144_ = v_a_3905_;
                            v_isShared_4145_ = v_isSharedCheck_4185_;
                            state = 42;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3905_);
                            v___x_4144_ = leanh::lean_box(0);
                            v_isShared_4145_ = v_isSharedCheck_4185_;
                            state = 42;
                            continue;
                        }
                    }
                } else {
                    v___x_4188_ = leanh::lean_box(0);
                    v___x_4189_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4189_, 0, v_a_3905_);
                    leanh::lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                    return v___x_4189_;
                }
            }
            1 => {
                v___x_3907_ = l_Lean_Json_Parser_num(v_a_3905_);
                if leanh::lean_obj_tag(v___x_3907_) == 0 {
                    v_pos_3908_ = leanh::lean_ctor_get(v___x_3907_, 0);
                    v_res_3909_ = leanh::lean_ctor_get(v___x_3907_, 1);
                    v_isSharedCheck_3927_ = (!leanh::lean_is_exclusive(v___x_3907_)) as u8;
                    if v_isSharedCheck_3927_ == 0 {
                        v___x_3911_ = v___x_3907_;
                        v_isShared_3912_ = v_isSharedCheck_3927_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_3909_);
                        leanh::lean_inc(v_pos_3908_);
                        leanh::lean_dec(v___x_3907_);
                        v___x_3911_ = leanh::lean_box(0);
                        v_isShared_3912_ = v_isSharedCheck_3927_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_pos_3928_ = leanh::lean_ctor_get(v___x_3907_, 0);
                    v_err_3929_ = leanh::lean_ctor_get(v___x_3907_, 1);
                    v_isSharedCheck_3936_ = (!leanh::lean_is_exclusive(v___x_3907_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v___x_3931_ = v___x_3907_;
                        v_isShared_3932_ = v_isSharedCheck_3936_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3929_);
                        leanh::lean_inc(v_pos_3928_);
                        leanh::lean_dec(v___x_3907_);
                        v___x_3931_ = leanh::lean_box(0);
                        v_isShared_3932_ = v_isSharedCheck_3936_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3913_ = leanh::lean_ctor_get(v_pos_3908_, 0);
                v_snd_3914_ = leanh::lean_ctor_get(v_pos_3908_, 1);
                v_isSharedCheck_3926_ = (!leanh::lean_is_exclusive(v_pos_3908_)) as u8;
                if v_isSharedCheck_3926_ == 0 {
                    v___x_3916_ = v_pos_3908_;
                    v_isShared_3917_ = v_isSharedCheck_3926_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3914_);
                    leanh::lean_inc(v_fst_3913_);
                    leanh::lean_dec(v_pos_3908_);
                    v___x_3916_ = leanh::lean_box(0);
                    v_isShared_3917_ = v_isSharedCheck_3926_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3918_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_3913_,
                        v_snd_3914_,
                    );
                if v_isShared_3917_ == 0 {
                    leanh::lean_ctor_set(v___x_3916_, 1, v___x_3918_);
                    v___x_3920_ = v___x_3916_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fst_3913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3918_);
                    v___x_3920_ = v_reuseFailAlloc_3925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3921_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3921_, 0, v_res_3909_);
                if v_isShared_3912_ == 0 {
                    leanh::lean_ctor_set(v___x_3911_, 1, v___x_3921_);
                    leanh::lean_ctor_set(v___x_3911_, 0, v___x_3920_);
                    v___x_3923_ = v___x_3911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3921_);
                    v___x_3923_ = v_reuseFailAlloc_3924_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3923_;
            }
            6 => {
                if v_isShared_3932_ == 0 {
                    v___x_3934_ = v___x_3931_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_pos_3928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_err_3929_);
                    v___x_3934_ = v_reuseFailAlloc_3935_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3934_;
            }
            8 => {
                if v___y_3938_ == 0 {
                    v___x_3939_ = l_Lean_Json_Parser_anyCore___closed__1;
                    v___x_3940_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3940_, 0, v_a_3905_);
                    leanh::lean_ctor_set(v___x_3940_, 1, v___x_3939_);
                    return v___x_3940_;
                } else {
                    state = 1;
                    continue;
                }
            }
            9 => {
                v_fst_3970_ = leanh::lean_ctor_get(v_pos_3966_, 0);
                v_snd_3971_ = leanh::lean_ctor_get(v_pos_3966_, 1);
                v_isSharedCheck_3983_ = (!leanh::lean_is_exclusive(v_pos_3966_)) as u8;
                if v_isSharedCheck_3983_ == 0 {
                    v___x_3973_ = v_pos_3966_;
                    v_isShared_3974_ = v_isSharedCheck_3983_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3971_);
                    leanh::lean_inc(v_fst_3970_);
                    leanh::lean_dec(v_pos_3966_);
                    v___x_3973_ = leanh::lean_box(0);
                    v_isShared_3974_ = v_isSharedCheck_3983_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3975_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_3970_,
                        v_snd_3971_,
                    );
                if v_isShared_3974_ == 0 {
                    leanh::lean_ctor_set(v___x_3973_, 1, v___x_3975_);
                    v___x_3977_ = v___x_3973_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_fst_3970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3975_);
                    v___x_3977_ = v_reuseFailAlloc_3982_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3978_ = leanh::lean_box(0);
                if v_isShared_3969_ == 0 {
                    leanh::lean_ctor_set(v___x_3968_, 1, v___x_3978_);
                    leanh::lean_ctor_set(v___x_3968_, 0, v___x_3977_);
                    v___x_3980_ = v___x_3968_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3978_);
                    v___x_3980_ = v_reuseFailAlloc_3981_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3980_;
            }
            13 => {
                if v_isShared_3990_ == 0 {
                    v___x_3992_ = v___x_3989_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_pos_3986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_err_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3992_;
            }
            15 => {
                v_fst_4001_ = leanh::lean_ctor_get(v_pos_3997_, 0);
                v_snd_4002_ = leanh::lean_ctor_get(v_pos_3997_, 1);
                v_isSharedCheck_4014_ = (!leanh::lean_is_exclusive(v_pos_3997_)) as u8;
                if v_isSharedCheck_4014_ == 0 {
                    v___x_4004_ = v_pos_3997_;
                    v_isShared_4005_ = v_isSharedCheck_4014_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4002_);
                    leanh::lean_inc(v_fst_4001_);
                    leanh::lean_dec(v_pos_3997_);
                    v___x_4004_ = leanh::lean_box(0);
                    v_isShared_4005_ = v_isSharedCheck_4014_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4006_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_4001_,
                        v_snd_4002_,
                    );
                if v_isShared_4005_ == 0 {
                    leanh::lean_ctor_set(v___x_4004_, 1, v___x_4006_);
                    v___x_4008_ = v___x_4004_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4013_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_fst_4001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 1, v___x_4006_);
                    v___x_4008_ = v_reuseFailAlloc_4013_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4009_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_4009_, 0 as u32, v___x_3955_);
                if v_isShared_4000_ == 0 {
                    leanh::lean_ctor_set(v___x_3999_, 1, v___x_4009_);
                    leanh::lean_ctor_set(v___x_3999_, 0, v___x_4008_);
                    v___x_4011_ = v___x_3999_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_4009_);
                    v___x_4011_ = v_reuseFailAlloc_4012_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4011_;
            }
            19 => {
                if v_isShared_4021_ == 0 {
                    v___x_4023_ = v___x_4020_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4024_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_pos_4017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_err_4018_);
                    v___x_4023_ = v_reuseFailAlloc_4024_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4023_;
            }
            21 => {
                v_fst_4032_ = leanh::lean_ctor_get(v_pos_4028_, 0);
                v_snd_4033_ = leanh::lean_ctor_get(v_pos_4028_, 1);
                v_isSharedCheck_4045_ = (!leanh::lean_is_exclusive(v_pos_4028_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v___x_4035_ = v_pos_4028_;
                    v_isShared_4036_ = v_isSharedCheck_4045_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4033_);
                    leanh::lean_inc(v_fst_4032_);
                    leanh::lean_dec(v_pos_4028_);
                    v___x_4035_ = leanh::lean_box(0);
                    v_isShared_4036_ = v_isSharedCheck_4045_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_4037_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_4032_,
                        v_snd_4033_,
                    );
                if v_isShared_4036_ == 0 {
                    leanh::lean_ctor_set(v___x_4035_, 1, v___x_4037_);
                    v___x_4039_ = v___x_4035_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_fst_4032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4037_);
                    v___x_4039_ = v_reuseFailAlloc_4044_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4040_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_4040_, 0 as u32, v___x_3951_);
                if v_isShared_4031_ == 0 {
                    leanh::lean_ctor_set(v___x_4030_, 1, v___x_4040_);
                    leanh::lean_ctor_set(v___x_4030_, 0, v___x_4039_);
                    v___x_4042_ = v___x_4030_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v___x_4040_);
                    v___x_4042_ = v_reuseFailAlloc_4043_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4042_;
            }
            25 => {
                if v_isShared_4052_ == 0 {
                    v___x_4054_ = v___x_4051_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_pos_4048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_err_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4054_;
            }
            27 => {
                v___x_4060_ = lean_string_utf8_next_fast(v_fst_3941_, v_snd_3942_);
                leanh::lean_dec(v_snd_3942_);
                if v_isShared_4059_ == 0 {
                    leanh::lean_ctor_set(v___x_4058_, 1, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_fst_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4094_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4063_ = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
                v___x_4064_ = l_Lean_Json_Parser_strCore(v___x_4063_, v___x_4062_);
                if leanh::lean_obj_tag(v___x_4064_) == 0 {
                    v_pos_4065_ = leanh::lean_ctor_get(v___x_4064_, 0);
                    v_res_4066_ = leanh::lean_ctor_get(v___x_4064_, 1);
                    v_isSharedCheck_4084_ = (!leanh::lean_is_exclusive(v___x_4064_)) as u8;
                    if v_isSharedCheck_4084_ == 0 {
                        v___x_4068_ = v___x_4064_;
                        v_isShared_4069_ = v_isSharedCheck_4084_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4066_);
                        leanh::lean_inc(v_pos_4065_);
                        leanh::lean_dec(v___x_4064_);
                        v___x_4068_ = leanh::lean_box(0);
                        v_isShared_4069_ = v_isSharedCheck_4084_;
                        state = 29;
                        continue;
                    }
                } else {
                    v_pos_4085_ = leanh::lean_ctor_get(v___x_4064_, 0);
                    v_err_4086_ = leanh::lean_ctor_get(v___x_4064_, 1);
                    v_isSharedCheck_4093_ = (!leanh::lean_is_exclusive(v___x_4064_)) as u8;
                    if v_isSharedCheck_4093_ == 0 {
                        v___x_4088_ = v___x_4064_;
                        v_isShared_4089_ = v_isSharedCheck_4093_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4086_);
                        leanh::lean_inc(v_pos_4085_);
                        leanh::lean_dec(v___x_4064_);
                        v___x_4088_ = leanh::lean_box(0);
                        v_isShared_4089_ = v_isSharedCheck_4093_;
                        state = 33;
                        continue;
                    }
                }
            }
            29 => {
                v_fst_4070_ = leanh::lean_ctor_get(v_pos_4065_, 0);
                v_snd_4071_ = leanh::lean_ctor_get(v_pos_4065_, 1);
                v_isSharedCheck_4083_ = (!leanh::lean_is_exclusive(v_pos_4065_)) as u8;
                if v_isSharedCheck_4083_ == 0 {
                    v___x_4073_ = v_pos_4065_;
                    v_isShared_4074_ = v_isSharedCheck_4083_;
                    state = 30;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4071_);
                    leanh::lean_inc(v_fst_4070_);
                    leanh::lean_dec(v_pos_4065_);
                    v___x_4073_ = leanh::lean_box(0);
                    v_isShared_4074_ = v_isSharedCheck_4083_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_4075_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_4070_,
                        v_snd_4071_,
                    );
                if v_isShared_4074_ == 0 {
                    leanh::lean_ctor_set(v___x_4073_, 1, v___x_4075_);
                    v___x_4077_ = v___x_4073_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_fst_4070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4075_);
                    v___x_4077_ = v_reuseFailAlloc_4082_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_4078_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4078_, 0, v_res_4066_);
                if v_isShared_4069_ == 0 {
                    leanh::lean_ctor_set(v___x_4068_, 1, v___x_4078_);
                    leanh::lean_ctor_set(v___x_4068_, 0, v___x_4077_);
                    v___x_4080_ = v___x_4068_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4081_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4078_);
                    v___x_4080_ = v_reuseFailAlloc_4081_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4080_;
            }
            33 => {
                if v_isShared_4089_ == 0 {
                    v___x_4091_ = v___x_4088_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_pos_4085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_err_4086_);
                    v___x_4091_ = v_reuseFailAlloc_4092_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4091_;
            }
            35 => {
                v___x_4101_ = lean_string_utf8_next_fast(v_fst_3941_, v_snd_3942_);
                leanh::lean_dec(v_snd_3942_);
                v___x_4102_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_3941_,
                        v___x_4101_,
                    );
                leanh::lean_inc(v___x_4102_);
                leanh::lean_inc(v_fst_3941_);
                if v_isShared_4100_ == 0 {
                    leanh::lean_ctor_set(v___x_4099_, 1, v___x_4102_);
                    v___x_4104_ = v___x_4099_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_fst_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4102_);
                    v___x_4104_ = v_reuseFailAlloc_4139_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_4138_ = lean_nat_dec_eq(v___x_4102_, v___x_3943_);
                if v___x_4138_ == 0 {
                    v___y_4106_ = v___x_3949_;
                    state = 37;
                    continue;
                } else {
                    v___y_4106_ = v___x_3947_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v___y_4106_ == 0 {
                    leanh::lean_dec(v___x_4102_);
                    leanh::lean_dec(v_fst_3941_);
                    v___x_4107_ = leanh::lean_box(0);
                    v___x_4108_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4108_, 0, v___x_4104_);
                    leanh::lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                    return v___x_4108_;
                } else {
                    v___x_4109_ = lean_string_utf8_get_fast(v_fst_3941_, v___x_4102_);
                    v___x_4110_ = 125;
                    v___x_4111_ = lean_uint32_dec_eq(v___x_4109_, v___x_4110_);
                    if v___x_4111_ == 0 {
                        leanh::lean_dec(v___x_4102_);
                        leanh::lean_dec(v_fst_3941_);
                        v___x_4112_ = leanh::lean_box(1);
                        v___x_4113_ = l_Lean_Json_Parser_objectCore(v___x_4112_, v___x_4104_);
                        if leanh::lean_obj_tag(v___x_4113_) == 0 {
                            v_pos_4114_ = leanh::lean_ctor_get(v___x_4113_, 0);
                            v_res_4115_ = leanh::lean_ctor_get(v___x_4113_, 1);
                            v_isSharedCheck_4123_ =
                                (!leanh::lean_is_exclusive(v___x_4113_)) as u8;
                            if v_isSharedCheck_4123_ == 0 {
                                v___x_4117_ = v___x_4113_;
                                v_isShared_4118_ = v_isSharedCheck_4123_;
                                state = 38;
                                continue;
                            } else {
                                leanh::lean_inc(v_res_4115_);
                                leanh::lean_inc(v_pos_4114_);
                                leanh::lean_dec(v___x_4113_);
                                v___x_4117_ = leanh::lean_box(0);
                                v_isShared_4118_ = v_isSharedCheck_4123_;
                                state = 38;
                                continue;
                            }
                        } else {
                            v_pos_4124_ = leanh::lean_ctor_get(v___x_4113_, 0);
                            v_err_4125_ = leanh::lean_ctor_get(v___x_4113_, 1);
                            v_isSharedCheck_4132_ =
                                (!leanh::lean_is_exclusive(v___x_4113_)) as u8;
                            if v_isSharedCheck_4132_ == 0 {
                                v___x_4127_ = v___x_4113_;
                                v_isShared_4128_ = v_isSharedCheck_4132_;
                                state = 40;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4125_);
                                leanh::lean_inc(v_pos_4124_);
                                leanh::lean_dec(v___x_4113_);
                                v___x_4127_ = leanh::lean_box(0);
                                v_isShared_4128_ = v_isSharedCheck_4132_;
                                state = 40;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4104_);
                        v___x_4133_ = lean_string_utf8_next_fast(v_fst_3941_, v___x_4102_);
                        leanh::lean_dec(v___x_4102_);
                        v___x_4134_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_3941_, v___x_4133_);
                        v___x_4135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4135_, 0, v_fst_3941_);
                        leanh::lean_ctor_set(v___x_4135_, 1, v___x_4134_);
                        v___x_4136_ = l_Lean_Json_Parser_anyCore___closed__5;
                        v___x_4137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4137_, 0, v___x_4135_);
                        leanh::lean_ctor_set(v___x_4137_, 1, v___x_4136_);
                        return v___x_4137_;
                    }
                }
            }
            38 => {
                v___x_4119_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4119_, 0, v_res_4115_);
                if v_isShared_4118_ == 0 {
                    leanh::lean_ctor_set(v___x_4117_, 1, v___x_4119_);
                    v___x_4121_ = v___x_4117_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_pos_4114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 1, v___x_4119_);
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4121_;
            }
            40 => {
                if v_isShared_4128_ == 0 {
                    v___x_4130_ = v___x_4127_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_pos_4124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_err_4125_);
                    v___x_4130_ = v_reuseFailAlloc_4131_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4130_;
            }
            42 => {
                v___x_4146_ = lean_string_utf8_next_fast(v_fst_3941_, v_snd_3942_);
                leanh::lean_dec(v_snd_3942_);
                v___x_4147_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_3941_,
                        v___x_4146_,
                    );
                leanh::lean_inc(v___x_4147_);
                leanh::lean_inc(v_fst_3941_);
                if v_isShared_4145_ == 0 {
                    leanh::lean_ctor_set(v___x_4144_, 1, v___x_4147_);
                    v___x_4149_ = v___x_4144_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_fst_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___x_4147_);
                    v___x_4149_ = v_reuseFailAlloc_4184_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_4153_ = lean_nat_dec_eq(v___x_4147_, v___x_3943_);
                if v___x_4153_ == 0 {
                    if v___x_3947_ == 0 {
                        leanh::lean_dec(v___x_4147_);
                        leanh::lean_dec(v_fst_3941_);
                        state = 44;
                        continue;
                    } else {
                        v___x_4154_ = lean_string_utf8_get_fast(v_fst_3941_, v___x_4147_);
                        v___x_4155_ = 93;
                        v___x_4156_ = lean_uint32_dec_eq(v___x_4154_, v___x_4155_);
                        if v___x_4156_ == 0 {
                            leanh::lean_dec(v___x_4147_);
                            leanh::lean_dec(v_fst_3941_);
                            v___x_4157_ = leanh::lean_unsigned_to_nat(4);
                            v___x_4158_ = lean_mk_empty_array_with_capacity(v___x_4157_);
                            v___x_4159_ = l_Lean_Json_Parser_arrayCore(v___x_4158_, v___x_4149_);
                            if leanh::lean_obj_tag(v___x_4159_) == 0 {
                                v_pos_4160_ = leanh::lean_ctor_get(v___x_4159_, 0);
                                v_res_4161_ = leanh::lean_ctor_get(v___x_4159_, 1);
                                v_isSharedCheck_4169_ =
                                    (!leanh::lean_is_exclusive(v___x_4159_)) as u8;
                                if v_isSharedCheck_4169_ == 0 {
                                    v___x_4163_ = v___x_4159_;
                                    v_isShared_4164_ = v_isSharedCheck_4169_;
                                    state = 45;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_res_4161_);
                                    leanh::lean_inc(v_pos_4160_);
                                    leanh::lean_dec(v___x_4159_);
                                    v___x_4163_ = leanh::lean_box(0);
                                    v_isShared_4164_ = v_isSharedCheck_4169_;
                                    state = 45;
                                    continue;
                                }
                            } else {
                                v_pos_4170_ = leanh::lean_ctor_get(v___x_4159_, 0);
                                v_err_4171_ = leanh::lean_ctor_get(v___x_4159_, 1);
                                v_isSharedCheck_4178_ =
                                    (!leanh::lean_is_exclusive(v___x_4159_)) as u8;
                                if v_isSharedCheck_4178_ == 0 {
                                    v___x_4173_ = v___x_4159_;
                                    v_isShared_4174_ = v_isSharedCheck_4178_;
                                    state = 47;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_err_4171_);
                                    leanh::lean_inc(v_pos_4170_);
                                    leanh::lean_dec(v___x_4159_);
                                    v___x_4173_ = leanh::lean_box(0);
                                    v_isShared_4174_ = v_isSharedCheck_4178_;
                                    state = 47;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4149_);
                            v___x_4179_ = lean_string_utf8_next_fast(v_fst_3941_, v___x_4147_);
                            leanh::lean_dec(v___x_4147_);
                            v___x_4180_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_3941_, v___x_4179_);
                            v___x_4181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4181_, 0, v_fst_3941_);
                            leanh::lean_ctor_set(v___x_4181_, 1, v___x_4180_);
                            v___x_4182_ = l_Lean_Json_Parser_anyCore___closed__7;
                            v___x_4183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4183_, 0, v___x_4181_);
                            leanh::lean_ctor_set(v___x_4183_, 1, v___x_4182_);
                            return v___x_4183_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4147_);
                    leanh::lean_dec(v_fst_3941_);
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_4151_ = leanh::lean_box(0);
                v___x_4152_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4152_, 0, v___x_4149_);
                leanh::lean_ctor_set(v___x_4152_, 1, v___x_4151_);
                return v___x_4152_;
            }
            45 => {
                v___x_4165_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4165_, 0, v_res_4161_);
                if v_isShared_4164_ == 0 {
                    leanh::lean_ctor_set(v___x_4163_, 1, v___x_4165_);
                    v___x_4167_ = v___x_4163_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_pos_4160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
                    v___x_4167_ = v_reuseFailAlloc_4168_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4167_;
            }
            47 => {
                if v_isShared_4174_ == 0 {
                    v___x_4176_ = v___x_4173_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4177_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_pos_4170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_err_4171_);
                    v___x_4176_ = v_reuseFailAlloc_4177_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Parser_arrayCore(
    mut v_acc_4190_: *mut leanh::LeanObject,
    mut v_a_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v_fst_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u32 = 0;
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u32 = 0;
    let mut v___x_4209_: u8 = 0;
    let mut v___x_4210_: u32 = 0;
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_unused_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_pos_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4192_ = l_Lean_Json_Parser_anyCore(v_a_4191_);
                if leanh::lean_obj_tag(v___x_4192_) == 0 {
                    v_pos_4193_ = leanh::lean_ctor_get(v___x_4192_, 0);
                    v_res_4194_ = leanh::lean_ctor_get(v___x_4192_, 1);
                    v_isSharedCheck_4238_ = (!leanh::lean_is_exclusive(v___x_4192_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4196_ = v___x_4192_;
                        v_isShared_4197_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4194_);
                        leanh::lean_inc(v_pos_4193_);
                        leanh::lean_dec(v___x_4192_);
                        v___x_4196_ = leanh::lean_box(0);
                        v_isShared_4197_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_acc_4190_);
                    v_pos_4239_ = leanh::lean_ctor_get(v___x_4192_, 0);
                    v_err_4240_ = leanh::lean_ctor_get(v___x_4192_, 1);
                    v_isSharedCheck_4247_ = (!leanh::lean_is_exclusive(v___x_4192_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4242_ = v___x_4192_;
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4240_);
                        leanh::lean_inc(v_pos_4239_);
                        leanh::lean_dec(v___x_4192_);
                        v___x_4242_ = leanh::lean_box(0);
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4198_ = leanh::lean_ctor_get(v_pos_4193_, 0);
                v_snd_4199_ = leanh::lean_ctor_get(v_pos_4193_, 1);
                v___x_4200_ = lean_string_utf8_byte_size(v_fst_4198_);
                v___x_4201_ = lean_nat_dec_eq(v_snd_4199_, v___x_4200_);
                if v___x_4201_ == 0 {
                    leanh::lean_inc(v_snd_4199_);
                    leanh::lean_inc(v_fst_4198_);
                    v_isSharedCheck_4231_ = (!leanh::lean_is_exclusive(v_pos_4193_)) as u8;
                    if v_isSharedCheck_4231_ == 0 {
                        v_unused_4232_ = leanh::lean_ctor_get(v_pos_4193_, 1);
                        leanh::lean_dec(v_unused_4232_);
                        v_unused_4233_ = leanh::lean_ctor_get(v_pos_4193_, 0);
                        leanh::lean_dec(v_unused_4233_);
                        v___x_4203_ = v_pos_4193_;
                        v_isShared_4204_ = v_isSharedCheck_4231_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_pos_4193_);
                        v___x_4203_ = leanh::lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4231_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_res_4194_);
                    leanh::lean_dec_ref(v_acc_4190_);
                    v___x_4234_ = leanh::lean_box(0);
                    if v_isShared_4197_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4196_, 1);
                        leanh::lean_ctor_set(v___x_4196_, 1, v___x_4234_);
                        v___x_4236_ = v___x_4196_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4237_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_pos_4193_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 1, v___x_4234_);
                        v___x_4236_ = v_reuseFailAlloc_4237_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4205_ = lean_array_push(v_acc_4190_, v_res_4194_);
                v___x_4206_ = lean_string_utf8_get_fast(v_fst_4198_, v_snd_4199_);
                v___x_4207_ = lean_string_utf8_next_fast(v_fst_4198_, v_snd_4199_);
                leanh::lean_dec(v_snd_4199_);
                v___x_4208_ = 93;
                v___x_4209_ = lean_uint32_dec_eq(v___x_4206_, v___x_4208_);
                if v___x_4209_ == 0 {
                    v___x_4210_ = 44;
                    v___x_4211_ = lean_uint32_dec_eq(v___x_4206_, v___x_4210_);
                    if v___x_4211_ == 0 {
                        leanh::lean_dec_ref(v___x_4205_);
                        if v_isShared_4204_ == 0 {
                            leanh::lean_ctor_set(v___x_4203_, 1, v___x_4207_);
                            v___x_4213_ = v___x_4203_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4218_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_fst_4198_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v___x_4207_);
                            v___x_4213_ = v_reuseFailAlloc_4218_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4196_);
                        v___x_4219_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_4198_, v___x_4207_);
                        if v_isShared_4204_ == 0 {
                            leanh::lean_ctor_set(v___x_4203_, 1, v___x_4219_);
                            v___x_4221_ = v___x_4203_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4223_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_fst_4198_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 1, v___x_4219_);
                            v___x_4221_ = v_reuseFailAlloc_4223_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_4224_ =
                        l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                            v_fst_4198_,
                            v___x_4207_,
                        );
                    if v_isShared_4204_ == 0 {
                        leanh::lean_ctor_set(v___x_4203_, 1, v___x_4224_);
                        v___x_4226_ = v___x_4203_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_fst_4198_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4224_);
                        v___x_4226_ = v_reuseFailAlloc_4230_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4214_ = l_Lean_Json_Parser_arrayCore___closed__1;
                if v_isShared_4197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4196_, 1);
                    leanh::lean_ctor_set(v___x_4196_, 1, v___x_4214_);
                    leanh::lean_ctor_set(v___x_4196_, 0, v___x_4213_);
                    v___x_4216_ = v___x_4196_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 1, v___x_4214_);
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4216_;
            }
            5 => {
                v_acc_4190_ = v___x_4205_;
                v_a_4191_ = v___x_4221_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4197_ == 0 {
                    leanh::lean_ctor_set(v___x_4196_, 1, v___x_4205_);
                    leanh::lean_ctor_set(v___x_4196_, 0, v___x_4226_);
                    v___x_4228_ = v___x_4196_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4205_);
                    v___x_4228_ = v_reuseFailAlloc_4229_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4228_;
            }
            8 => {
                return v___x_4236_;
            }
            9 => {
                if v_isShared_4243_ == 0 {
                    v___x_4245_ = v___x_4242_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_pos_4239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_err_4240_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(
    mut v_00_u03b2_4248_: *mut leanh::LeanObject,
    mut v_msg_4249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(
    mut v_00_u03b2_4251_: *mut leanh::LeanObject,
    mut v_k_4252_: *mut leanh::LeanObject,
    mut v_v_4253_: *mut leanh::LeanObject,
    mut v_t_4254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_4252_, v_v_4253_, v_t_4254_);
    return v___x_4255_;
}
pub unsafe fn l_Lean_Json_Parser_any(
    mut v_a_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v_unused_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4260_ = leanh::lean_ctor_get(v_a_4259_, 0);
                v_snd_4261_ = leanh::lean_ctor_get(v_a_4259_, 1);
                v_isSharedCheck_4285_ = (!leanh::lean_is_exclusive(v_a_4259_)) as u8;
                if v_isSharedCheck_4285_ == 0 {
                    v___x_4263_ = v_a_4259_;
                    v_isShared_4264_ = v_isSharedCheck_4285_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4261_);
                    leanh::lean_inc(v_fst_4260_);
                    leanh::lean_dec(v_a_4259_);
                    v___x_4263_ = leanh::lean_box(0);
                    v_isShared_4264_ = v_isSharedCheck_4285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4265_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_4260_,
                        v_snd_4261_,
                    );
                if v_isShared_4264_ == 0 {
                    leanh::lean_ctor_set(v___x_4263_, 1, v___x_4265_);
                    v___x_4267_ = v___x_4263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_fst_4260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 1, v___x_4265_);
                    v___x_4267_ = v_reuseFailAlloc_4284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4268_ = l_Lean_Json_Parser_anyCore(v___x_4267_);
                if leanh::lean_obj_tag(v___x_4268_) == 0 {
                    v_pos_4269_ = leanh::lean_ctor_get(v___x_4268_, 0);
                    leanh::lean_inc(v_pos_4269_);
                    v_fst_4270_ = leanh::lean_ctor_get(v_pos_4269_, 0);
                    v_snd_4271_ = leanh::lean_ctor_get(v_pos_4269_, 1);
                    v___x_4272_ = lean_string_utf8_byte_size(v_fst_4270_);
                    v___x_4273_ = lean_nat_dec_eq(v_snd_4271_, v___x_4272_);
                    if v___x_4273_ == 0 {
                        v_isSharedCheck_4281_ =
                            (!leanh::lean_is_exclusive(v___x_4268_)) as u8;
                        if v_isSharedCheck_4281_ == 0 {
                            v_unused_4282_ = leanh::lean_ctor_get(v___x_4268_, 1);
                            leanh::lean_dec(v_unused_4282_);
                            v_unused_4283_ = leanh::lean_ctor_get(v___x_4268_, 0);
                            leanh::lean_dec(v_unused_4283_);
                            v___x_4275_ = v___x_4268_;
                            v_isShared_4276_ = v_isSharedCheck_4281_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4268_);
                            v___x_4275_ = leanh::lean_box(0);
                            v_isShared_4276_ = v_isSharedCheck_4281_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_pos_4269_);
                        return v___x_4268_;
                    }
                } else {
                    return v___x_4268_;
                }
            }
            3 => {
                v___x_4277_ = l_Lean_Json_Parser_any___closed__1;
                if v_isShared_4276_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4275_, 1);
                    leanh::lean_ctor_set(v___x_4275_, 1, v___x_4277_);
                    v___x_4279_ = v___x_4275_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_pos_4269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 1, v___x_4277_);
                    v___x_4279_ = v_reuseFailAlloc_4280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_parse(
    mut v_s_4286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4287_ =
        leanh::lean_alloc_closure(l_Lean_Json_Parser_any as *mut core::ffi::c_void, 1, 0);
    v___x_4288_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_4287_, v_s_4286_);
    return v___x_4288_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Parser(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Json_Parser_escapedChar___boxed__const__1 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__1();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__1);
    l_Lean_Json_Parser_escapedChar___boxed__const__2 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__2();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__2);
    l_Lean_Json_Parser_escapedChar___boxed__const__3 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__3();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__3);
    l_Lean_Json_Parser_escapedChar___boxed__const__4 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__4();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__4);
    l_Lean_Json_Parser_escapedChar___boxed__const__5 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__5();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__5);
    l_Lean_Json_Parser_escapedChar___boxed__const__6 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__6();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__6);
    l_Lean_Json_Parser_escapedChar___boxed__const__7 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__7();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__7);
    l_Lean_Json_Parser_escapedChar___boxed__const__8 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__8();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__8);
    l_Lean_Json_Parser_escapedChar___boxed__const__9 =
        _init_l_Lean_Json_Parser_escapedChar___boxed__const__9();
    leanh::lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__9);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Parser(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Parser(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_Parser(builtin);
}