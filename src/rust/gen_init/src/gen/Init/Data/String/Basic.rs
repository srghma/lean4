// Lean compiler output
// Module: Init.Data.String.Basic
// Imports: Init.Data.String.Decode Init.Data.String.Defs Init.Data.ByteArray.Lemmas Init.Data.Char.Lemmas Init.Data.Char.Basic Init.ByCases Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Data.List.Nat.TakeDrop Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Option.Lemmas Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::String::Decode::{
    initialize_Init_Data_String_Decode, l_UInt8_instDecidableIsUTF8FirstByte___aux__1,
    runtime_initialize_Init_Data_String_Decode,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, l_String_instInhabitedSlice,
    runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Char_utf8Size, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::ffi::lean_byte_array_fget;
use crate::ffi::{
    lean_string_data, lean_string_dec_lt, lean_string_is_valid_pos, lean_string_utf8_at_end,
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_bang,
    lean_string_utf8_get_fast, lean_string_utf8_get_opt, lean_string_utf8_next,
    lean_string_utf8_next_fast, lean_string_utf8_prev, lean_string_validate_utf8,
};
use crate::ffi::lean_string_get_byte_fast;
use crate::ffi::{
    lean_uint8_land, lean_uint32_lor, lean_uint32_shift_left,
};
use crate::ffi::lean_uint8_to_uint32;
use crate::ffi::{
    lean_array_push, lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_from_utf8_unchecked,
    lean_string_to_utf8, lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt,
};
pub static l_ByteArray_utf8Decode_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_ByteArray_utf8Decode_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_utf8Decode_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_fromUTF8_x21___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_String_fromUTF8_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_fromUTF8_x21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_fromUTF8_x21___closed__1_value: crate::leanh::LeanStringObject<23> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_String_fromUTF8_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_fromUTF8_x21___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String_fromUTF8_x21___closed__2_value: crate::leanh::LeanStringObject<17> =
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
            83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0,
        ],
    };
static mut l_String_fromUTF8_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_fromUTF8_x21___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_String_fromUTF8_x21___closed__3_value: crate::leanh::LeanStringObject<21> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_String_fromUTF8_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_fromUTF8_x21___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_String_fromUTF8_x21___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_fromUTF8_x21___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_String_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_String_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_slice_x21___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 115, 108, 105, 99, 101, 33,
            0,
        ],
    };
static mut l_String_Slice_slice_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_slice_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_slice_x21___closed__1_value: crate::leanh::LeanStringObject<62> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            83, 116, 97, 114, 116, 105, 110, 103, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32,
            109, 117, 115, 116, 32, 98, 101, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32,
            111, 114, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 101, 110, 100, 32, 112, 111,
            115, 105, 116, 105, 111, 110, 46, 0,
        ],
    };
static mut l_String_Slice_slice_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_slice_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_slice_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_slice_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_Pos_get_x21___closed__0_value: crate::leanh::LeanStringObject<22> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 103, 101,
            116, 33, 0,
        ],
    };
static mut l_String_Slice_Pos_get_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_get_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_get_x21___closed__1_value: crate::leanh::LeanStringObject<42> =
    crate::leanh::LeanStringObject {
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
            67, 97, 110, 110, 111, 116, 32, 114, 101, 116, 114, 105, 101, 118, 101, 32, 99, 104,
            97, 114, 97, 99, 116, 101, 114, 32, 97, 116, 32, 101, 110, 100, 32, 112, 111, 115, 105,
            116, 105, 111, 110, 0,
        ],
    };
static mut l_String_Slice_Pos_get_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_get_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_get_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_get_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_Pos_next_x21___closed__0_value: crate::leanh::LeanStringObject<23> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 110, 101,
            120, 116, 33, 0,
        ],
    };
static mut l_String_Slice_Pos_next_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_next_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_next_x21___closed__1_value: crate::leanh::LeanStringObject<32> =
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
            67, 97, 110, 110, 111, 116, 32, 97, 100, 118, 97, 110, 99, 101, 32, 116, 104, 101, 32,
            101, 110, 100, 32, 112, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_String_Slice_Pos_next_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_next_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_next_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_next_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_pos_x21___closed__0_value: crate::leanh::LeanStringObject<18> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 112, 111, 115, 33, 0,
        ],
    };
static mut l_String_Slice_pos_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_pos_x21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_pos_x21___closed__1_value: crate::leanh::LeanStringObject<50> =
    crate::leanh::LeanStringObject {
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
            79, 102, 102, 115, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 116, 32, 97, 32,
            118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 99, 104, 97, 114, 97, 99, 116, 101,
            114, 32, 98, 111, 117, 110, 100, 97, 114, 121, 0,
        ],
    };
static mut l_String_Slice_pos_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_pos_x21___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_pos_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_pos_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_Pos_sliceOrPanic___redArg___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
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
        83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 115, 108,
        105, 99, 101, 79, 114, 80, 97, 110, 105, 99, 0,
    ],
};
static mut l_String_Slice_Pos_sliceOrPanic___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_sliceOrPanic___redArg___closed__1_value:
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
        80, 111, 115, 105, 116, 105, 111, 110, 32, 105, 115, 32, 111, 117, 116, 115, 105, 100, 101,
        32, 111, 102, 32, 116, 104, 101, 32, 98, 111, 117, 110, 100, 115, 32, 111, 102, 32, 116,
        104, 101, 32, 115, 108, 105, 99, 101, 46, 0,
    ],
};
static mut l_String_Slice_Pos_sliceOrPanic___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_sliceOrPanic___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_Pos_ofSlice_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
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
        83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 111, 102, 83,
        108, 105, 99, 101, 33, 0,
    ],
};
static mut l_String_Slice_Pos_ofSlice_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_ofSlice_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_Pos_slice_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
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
        83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 115, 108,
        105, 99, 101, 33, 0,
    ],
};
static mut l_String_Slice_Pos_slice_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_slice_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_slice_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<
    126,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 126,
    m_capacity: 126,
    m_length: 125,
    m_data: [
        83, 116, 97, 114, 116, 105, 110, 103, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 109,
        117, 115, 116, 32, 98, 101, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32, 111, 114,
        32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 101, 110, 100, 32, 112, 111, 115, 105, 116,
        105, 111, 110, 32, 97, 110, 100, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 109, 117,
        115, 116, 32, 98, 101, 32, 98, 101, 116, 119, 101, 101, 110, 32, 115, 116, 97, 114, 116,
        105, 110, 103, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 97, 110, 100, 32, 101, 110,
        100, 32, 112, 111, 115, 105, 116, 105, 111, 110, 46, 0,
    ],
};
static mut l_String_Slice_Pos_slice_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_slice_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_slice_x21___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_slice_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_ByteArray_utf8Decode_x3f_go___redArg(
    mut v_b_2143_: *mut crate::leanh::LeanObject,
    mut v_i_2144_: *mut crate::leanh::LeanObject,
    mut v_acc_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2147_: u32 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: u8 = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: u8 = 0;
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2170_: u8 = 0;
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v_b_u2080_2194_: u8 = 0;
    let mut v___x_2195_: u8 = 0;
    let mut v_b_u2081_2196_: u8 = 0;
    let mut v_b_u2082_2197_: u8 = 0;
    let mut v_b_u2083_2198_: u8 = 0;
    let mut v___x_2199_: u32 = 0;
    let mut v___x_2200_: u32 = 0;
    let mut v___x_2201_: u32 = 0;
    let mut v___x_2202_: u32 = 0;
    let mut v___x_2203_: u32 = 0;
    let mut v___x_2204_: u32 = 0;
    let mut v___x_2205_: u32 = 0;
    let mut v___x_2206_: u32 = 0;
    let mut v___x_2207_: u32 = 0;
    let mut v___x_2208_: u32 = 0;
    let mut v___x_2209_: u32 = 0;
    let mut v___x_2210_: u32 = 0;
    let mut v_r_2211_: u32 = 0;
    let mut v___x_2212_: u32 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: u32 = 0;
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v_b_u2080_2233_: u8 = 0;
    let mut v___x_2234_: u8 = 0;
    let mut v_b_u2081_2235_: u8 = 0;
    let mut v_b_u2082_2236_: u8 = 0;
    let mut v___x_2237_: u32 = 0;
    let mut v___x_2238_: u32 = 0;
    let mut v___x_2239_: u32 = 0;
    let mut v___x_2240_: u32 = 0;
    let mut v___x_2241_: u32 = 0;
    let mut v___x_2242_: u32 = 0;
    let mut v___x_2243_: u32 = 0;
    let mut v___x_2244_: u32 = 0;
    let mut v_r_2245_: u32 = 0;
    let mut v___x_2246_: u32 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u32 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: u32 = 0;
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v_b_u2080_2263_: u8 = 0;
    let mut v___x_2264_: u8 = 0;
    let mut v_b_u2081_2265_: u8 = 0;
    let mut v___x_2266_: u32 = 0;
    let mut v___x_2267_: u32 = 0;
    let mut v___x_2268_: u32 = 0;
    let mut v___x_2269_: u32 = 0;
    let mut v_r_2270_: u32 = 0;
    let mut v___x_2271_: u32 = 0;
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2153_ = lean_byte_array_size(v_b_2143_);
                v___x_2154_ = lean_nat_dec_lt(v_i_2144_, v___x_2153_);
                if v___x_2154_ == 0 {
                    crate::leanh::lean_dec(v_i_2144_);
                    v___x_2155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2155_, 0, v_acc_2145_);
                    return v___x_2155_;
                } else {
                    if v___x_2154_ == 0 {
                        crate::leanh::lean_dec_ref(v_acc_2145_);
                        crate::leanh::lean_dec(v_i_2144_);
                        v___x_2156_ = crate::leanh::lean_box(0);
                        return v___x_2156_;
                    } else {
                        v___x_2157_ = lean_byte_array_fget(v_b_2143_, v_i_2144_);
                        v___x_2158_ = 128;
                        v___x_2159_ = lean_uint8_land(v___x_2157_, v___x_2158_);
                        v___x_2160_ = 0;
                        v___x_2161_ = lean_uint8_dec_eq(v___x_2159_, v___x_2160_);
                        if v___x_2161_ == 0 {
                            v___x_2162_ = 224;
                            v___x_2163_ = lean_uint8_land(v___x_2157_, v___x_2162_);
                            v___x_2164_ = 192;
                            v___x_2165_ = lean_uint8_dec_eq(v___x_2163_, v___x_2164_);
                            if v___x_2165_ == 0 {
                                v___x_2166_ = 240;
                                v___x_2167_ = lean_uint8_land(v___x_2157_, v___x_2166_);
                                v___x_2168_ = lean_uint8_dec_eq(v___x_2167_, v___x_2162_);
                                if v___x_2168_ == 0 {
                                    v___x_2169_ = 248;
                                    v___x_2170_ = lean_uint8_land(v___x_2157_, v___x_2169_);
                                    v___x_2171_ = lean_uint8_dec_eq(v___x_2170_, v___x_2166_);
                                    if v___x_2171_ == 0 {
                                        crate::leanh::lean_dec_ref(v_acc_2145_);
                                        crate::leanh::lean_dec(v_i_2144_);
                                        v___x_2172_ = crate::leanh::lean_box(0);
                                        return v___x_2172_;
                                    } else {
                                        v___x_2173_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_2174_ = lean_nat_add(v_i_2144_, v___x_2173_);
                                        v___x_2175_ = lean_nat_dec_lt(v___x_2174_, v___x_2153_);
                                        if v___x_2175_ == 0 {
                                            crate::leanh::lean_dec(v___x_2174_);
                                            crate::leanh::lean_dec_ref(v_acc_2145_);
                                            crate::leanh::lean_dec(v_i_2144_);
                                            v___x_2176_ = crate::leanh::lean_box(0);
                                            return v___x_2176_;
                                        } else {
                                            v___x_2177_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_2178_ = lean_nat_add(v_i_2144_, v___x_2177_);
                                            v___x_2179_ =
                                                lean_byte_array_fget(v_b_2143_, v___x_2178_);
                                            crate::leanh::lean_dec(v___x_2178_);
                                            v___x_2180_ = lean_uint8_land(v___x_2179_, v___x_2164_);
                                            v___x_2181_ =
                                                lean_uint8_dec_eq(v___x_2180_, v___x_2158_);
                                            if v___x_2181_ == 0 {
                                                crate::leanh::lean_dec(v___x_2174_);
                                                crate::leanh::lean_dec_ref(v_acc_2145_);
                                                crate::leanh::lean_dec(v_i_2144_);
                                                v___x_2182_ = crate::leanh::lean_box(0);
                                                return v___x_2182_;
                                            } else {
                                                v___x_2183_ = crate::leanh::lean_unsigned_to_nat(2);
                                                v___x_2184_ = lean_nat_add(v_i_2144_, v___x_2183_);
                                                v___x_2185_ =
                                                    lean_byte_array_fget(v_b_2143_, v___x_2184_);
                                                crate::leanh::lean_dec(v___x_2184_);
                                                v___x_2186_ =
                                                    lean_uint8_land(v___x_2185_, v___x_2164_);
                                                v___x_2187_ =
                                                    lean_uint8_dec_eq(v___x_2186_, v___x_2158_);
                                                if v___x_2187_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2174_);
                                                    crate::leanh::lean_dec_ref(v_acc_2145_);
                                                    crate::leanh::lean_dec(v_i_2144_);
                                                    v___x_2188_ = crate::leanh::lean_box(0);
                                                    return v___x_2188_;
                                                } else {
                                                    v___x_2189_ = lean_byte_array_fget(
                                                        v_b_2143_,
                                                        v___x_2174_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2174_);
                                                    v___x_2190_ =
                                                        lean_uint8_land(v___x_2189_, v___x_2164_);
                                                    v___x_2191_ =
                                                        lean_uint8_dec_eq(v___x_2190_, v___x_2158_);
                                                    if v___x_2191_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_acc_2145_);
                                                        crate::leanh::lean_dec(v_i_2144_);
                                                        v___x_2192_ = crate::leanh::lean_box(0);
                                                        return v___x_2192_;
                                                    } else {
                                                        v___x_2193_ = 7;
                                                        v_b_u2080_2194_ = lean_uint8_land(
                                                            v___x_2157_,
                                                            v___x_2193_,
                                                        );
                                                        v___x_2195_ = 63;
                                                        v_b_u2081_2196_ = lean_uint8_land(
                                                            v___x_2179_,
                                                            v___x_2195_,
                                                        );
                                                        v_b_u2082_2197_ = lean_uint8_land(
                                                            v___x_2185_,
                                                            v___x_2195_,
                                                        );
                                                        v_b_u2083_2198_ = lean_uint8_land(
                                                            v___x_2189_,
                                                            v___x_2195_,
                                                        );
                                                        v___x_2199_ =
                                                            lean_uint8_to_uint32(v_b_u2080_2194_);
                                                        v___x_2200_ = 18;
                                                        v___x_2201_ = lean_uint32_shift_left(
                                                            v___x_2199_,
                                                            v___x_2200_,
                                                        );
                                                        v___x_2202_ =
                                                            lean_uint8_to_uint32(v_b_u2081_2196_);
                                                        v___x_2203_ = 12;
                                                        v___x_2204_ = lean_uint32_shift_left(
                                                            v___x_2202_,
                                                            v___x_2203_,
                                                        );
                                                        v___x_2205_ = lean_uint32_lor(
                                                            v___x_2201_,
                                                            v___x_2204_,
                                                        );
                                                        v___x_2206_ =
                                                            lean_uint8_to_uint32(v_b_u2082_2197_);
                                                        v___x_2207_ = 6;
                                                        v___x_2208_ = lean_uint32_shift_left(
                                                            v___x_2206_,
                                                            v___x_2207_,
                                                        );
                                                        v___x_2209_ = lean_uint32_lor(
                                                            v___x_2205_,
                                                            v___x_2208_,
                                                        );
                                                        v___x_2210_ =
                                                            lean_uint8_to_uint32(v_b_u2083_2198_);
                                                        v_r_2211_ = lean_uint32_lor(
                                                            v___x_2209_,
                                                            v___x_2210_,
                                                        );
                                                        v___x_2212_ = 65536;
                                                        v___x_2213_ = lean_uint32_dec_lt(
                                                            v_r_2211_,
                                                            v___x_2212_,
                                                        );
                                                        if v___x_2213_ == 0 {
                                                            v___x_2214_ = 1114111;
                                                            v___x_2215_ = lean_uint32_dec_lt(
                                                                v___x_2214_,
                                                                v_r_2211_,
                                                            );
                                                            if v___x_2215_ == 0 {
                                                                v_val_2147_ = v_r_2211_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_acc_2145_,
                                                                );
                                                                crate::leanh::lean_dec(v_i_2144_);
                                                                v___x_2216_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_2216_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_acc_2145_);
                                                            crate::leanh::lean_dec(v_i_2144_);
                                                            v___x_2217_ = crate::leanh::lean_box(0);
                                                            return v___x_2217_;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_2218_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_2219_ = lean_nat_add(v_i_2144_, v___x_2218_);
                                    v___x_2220_ = lean_nat_dec_lt(v___x_2219_, v___x_2153_);
                                    if v___x_2220_ == 0 {
                                        crate::leanh::lean_dec(v___x_2219_);
                                        crate::leanh::lean_dec_ref(v_acc_2145_);
                                        crate::leanh::lean_dec(v_i_2144_);
                                        v___x_2221_ = crate::leanh::lean_box(0);
                                        return v___x_2221_;
                                    } else {
                                        v___x_2222_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_2223_ = lean_nat_add(v_i_2144_, v___x_2222_);
                                        v___x_2224_ = lean_byte_array_fget(v_b_2143_, v___x_2223_);
                                        crate::leanh::lean_dec(v___x_2223_);
                                        v___x_2225_ = lean_uint8_land(v___x_2224_, v___x_2164_);
                                        v___x_2226_ = lean_uint8_dec_eq(v___x_2225_, v___x_2158_);
                                        if v___x_2226_ == 0 {
                                            crate::leanh::lean_dec(v___x_2219_);
                                            crate::leanh::lean_dec_ref(v_acc_2145_);
                                            crate::leanh::lean_dec(v_i_2144_);
                                            v___x_2227_ = crate::leanh::lean_box(0);
                                            return v___x_2227_;
                                        } else {
                                            v___x_2228_ =
                                                lean_byte_array_fget(v_b_2143_, v___x_2219_);
                                            crate::leanh::lean_dec(v___x_2219_);
                                            v___x_2229_ = lean_uint8_land(v___x_2228_, v___x_2164_);
                                            v___x_2230_ =
                                                lean_uint8_dec_eq(v___x_2229_, v___x_2158_);
                                            if v___x_2230_ == 0 {
                                                crate::leanh::lean_dec_ref(v_acc_2145_);
                                                crate::leanh::lean_dec(v_i_2144_);
                                                v___x_2231_ = crate::leanh::lean_box(0);
                                                return v___x_2231_;
                                            } else {
                                                v___x_2232_ = 15;
                                                v_b_u2080_2233_ =
                                                    lean_uint8_land(v___x_2157_, v___x_2232_);
                                                v___x_2234_ = 63;
                                                v_b_u2081_2235_ =
                                                    lean_uint8_land(v___x_2224_, v___x_2234_);
                                                v_b_u2082_2236_ =
                                                    lean_uint8_land(v___x_2228_, v___x_2234_);
                                                v___x_2237_ = lean_uint8_to_uint32(v_b_u2080_2233_);
                                                v___x_2238_ = 12;
                                                v___x_2239_ = lean_uint32_shift_left(
                                                    v___x_2237_,
                                                    v___x_2238_,
                                                );
                                                v___x_2240_ = lean_uint8_to_uint32(v_b_u2081_2235_);
                                                v___x_2241_ = 6;
                                                v___x_2242_ = lean_uint32_shift_left(
                                                    v___x_2240_,
                                                    v___x_2241_,
                                                );
                                                v___x_2243_ =
                                                    lean_uint32_lor(v___x_2239_, v___x_2242_);
                                                v___x_2244_ = lean_uint8_to_uint32(v_b_u2082_2236_);
                                                v_r_2245_ =
                                                    lean_uint32_lor(v___x_2243_, v___x_2244_);
                                                v___x_2246_ = 2048;
                                                v___x_2247_ =
                                                    lean_uint32_dec_lt(v_r_2245_, v___x_2246_);
                                                if v___x_2247_ == 0 {
                                                    v___x_2248_ = 55296;
                                                    v___x_2249_ =
                                                        lean_uint32_dec_le(v___x_2248_, v_r_2245_);
                                                    if v___x_2249_ == 0 {
                                                        v_val_2147_ = v_r_2245_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2250_ = 57343;
                                                        v___x_2251_ = lean_uint32_dec_le(
                                                            v_r_2245_,
                                                            v___x_2250_,
                                                        );
                                                        if v___x_2251_ == 0 {
                                                            v_val_2147_ = v_r_2245_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_acc_2145_);
                                                            crate::leanh::lean_dec(v_i_2144_);
                                                            v___x_2252_ = crate::leanh::lean_box(0);
                                                            return v___x_2252_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_acc_2145_);
                                                    crate::leanh::lean_dec(v_i_2144_);
                                                    v___x_2253_ = crate::leanh::lean_box(0);
                                                    return v___x_2253_;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_2254_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2255_ = lean_nat_add(v_i_2144_, v___x_2254_);
                                v___x_2256_ = lean_nat_dec_lt(v___x_2255_, v___x_2153_);
                                if v___x_2256_ == 0 {
                                    crate::leanh::lean_dec(v___x_2255_);
                                    crate::leanh::lean_dec_ref(v_acc_2145_);
                                    crate::leanh::lean_dec(v_i_2144_);
                                    v___x_2257_ = crate::leanh::lean_box(0);
                                    return v___x_2257_;
                                } else {
                                    v___x_2258_ = lean_byte_array_fget(v_b_2143_, v___x_2255_);
                                    crate::leanh::lean_dec(v___x_2255_);
                                    v___x_2259_ = lean_uint8_land(v___x_2258_, v___x_2164_);
                                    v___x_2260_ = lean_uint8_dec_eq(v___x_2259_, v___x_2158_);
                                    if v___x_2260_ == 0 {
                                        crate::leanh::lean_dec_ref(v_acc_2145_);
                                        crate::leanh::lean_dec(v_i_2144_);
                                        v___x_2261_ = crate::leanh::lean_box(0);
                                        return v___x_2261_;
                                    } else {
                                        v___x_2262_ = 31;
                                        v_b_u2080_2263_ = lean_uint8_land(v___x_2157_, v___x_2262_);
                                        v___x_2264_ = 63;
                                        v_b_u2081_2265_ = lean_uint8_land(v___x_2258_, v___x_2264_);
                                        v___x_2266_ = lean_uint8_to_uint32(v_b_u2080_2263_);
                                        v___x_2267_ = 6;
                                        v___x_2268_ =
                                            lean_uint32_shift_left(v___x_2266_, v___x_2267_);
                                        v___x_2269_ = lean_uint8_to_uint32(v_b_u2081_2265_);
                                        v_r_2270_ = lean_uint32_lor(v___x_2268_, v___x_2269_);
                                        v___x_2271_ = 128;
                                        v___x_2272_ = lean_uint32_dec_lt(v_r_2270_, v___x_2271_);
                                        if v___x_2272_ == 0 {
                                            v_val_2147_ = v_r_2270_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_acc_2145_);
                                            crate::leanh::lean_dec(v_i_2144_);
                                            v___x_2273_ = crate::leanh::lean_box(0);
                                            return v___x_2273_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_2274_ = lean_uint8_to_uint32(v___x_2157_);
                            v_val_2147_ = v___x_2274_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2148_ = l_Char_utf8Size(v_val_2147_);
                v___x_2149_ = lean_nat_add(v_i_2144_, v___x_2148_);
                crate::leanh::lean_dec(v___x_2148_);
                crate::leanh::lean_dec(v_i_2144_);
                v___x_2150_ = crate::leanh::lean_box_uint32(v_val_2147_);
                v___x_2151_ = lean_array_push(v_acc_2145_, v___x_2150_);
                v_i_2144_ = v___x_2149_;
                v_acc_2145_ = v___x_2151_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_utf8Decode_x3f_go___redArg___boxed(
    mut v_b_2275_: *mut crate::leanh::LeanObject,
    mut v_i_2276_: *mut crate::leanh::LeanObject,
    mut v_acc_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_2275_, v_i_2276_, v_acc_2277_);
    crate::leanh::lean_dec_ref(v_b_2275_);
    return v_res_2278_;
}
pub unsafe fn l_ByteArray_utf8Decode_x3f_go(
    mut v_b_2279_: *mut crate::leanh::LeanObject,
    mut v_i_2280_: *mut crate::leanh::LeanObject,
    mut v_acc_2281_: *mut crate::leanh::LeanObject,
    mut v_hi_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_2279_, v_i_2280_, v_acc_2281_);
    return v___x_2283_;
}
pub unsafe fn l_ByteArray_utf8Decode_x3f_go___boxed(
    mut v_b_2284_: *mut crate::leanh::LeanObject,
    mut v_i_2285_: *mut crate::leanh::LeanObject,
    mut v_acc_2286_: *mut crate::leanh::LeanObject,
    mut v_hi_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_ByteArray_utf8Decode_x3f_go(v_b_2284_, v_i_2285_, v_acc_2286_, v_hi_2287_);
    crate::leanh::lean_dec_ref(v_b_2284_);
    return v_res_2288_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(
    mut v_x_2289_: *mut crate::leanh::LeanObject,
    mut v_h__1_2290_: *mut crate::leanh::LeanObject,
    mut v_h__2_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2289_) == 0 {
        let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2291_);
        v___x_2292_ = crate::leanh::lean_apply_1(v_h__1_2290_, crate::leanh::lean_box(0));
        return v___x_2292_;
    } else {
        let mut v_val_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2290_);
        v_val_2293_ = crate::leanh::lean_ctor_get(v_x_2289_, 0);
        crate::leanh::lean_inc(v_val_2293_);
        crate::leanh::lean_dec_ref_known(v_x_2289_, 1);
        v___x_2294_ =
            crate::leanh::lean_apply_2(v_h__2_2291_, v_val_2293_, crate::leanh::lean_box(0));
        return v___x_2294_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(
    mut v_motive_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: *mut crate::leanh::LeanObject,
    mut v_h__1_2297_: *mut crate::leanh::LeanObject,
    mut v_h__2_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2296_) == 0 {
        let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2298_);
        v___x_2299_ = crate::leanh::lean_apply_1(v_h__1_2297_, crate::leanh::lean_box(0));
        return v___x_2299_;
    } else {
        let mut v_val_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2297_);
        v_val_2300_ = crate::leanh::lean_ctor_get(v_x_2296_, 0);
        crate::leanh::lean_inc(v_val_2300_);
        crate::leanh::lean_dec_ref_known(v_x_2296_, 1);
        v___x_2301_ =
            crate::leanh::lean_apply_2(v_h__2_2298_, v_val_2300_, crate::leanh::lean_box(0));
        return v___x_2301_;
    }
}
pub unsafe fn l_ByteArray_utf8Decode_x3f(
    mut v_b_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2306_ = l_ByteArray_utf8Decode_x3f___closed__0;
    v___x_2307_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_2304_, v___x_2305_, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn l_ByteArray_utf8Decode_x3f___boxed(
    mut v_b_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_ByteArray_utf8Decode_x3f(v_b_2308_);
    crate::leanh::lean_dec_ref(v_b_2308_);
    return v_res_2309_;
}
pub unsafe fn l_ByteArray_validateUTF8_go___redArg(
    mut v_b_2310_: *mut crate::leanh::LeanObject,
    mut v_i_2311_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2317_: u8 = 0;
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: u8 = 0;
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: u8 = 0;
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: u8 = 0;
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: u8 = 0;
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: u8 = 0;
    let mut v_b_u2080_2369_: u8 = 0;
    let mut v___x_2370_: u8 = 0;
    let mut v_b_u2081_2371_: u8 = 0;
    let mut v_b_u2082_2372_: u8 = 0;
    let mut v_b_u2083_2373_: u8 = 0;
    let mut v___x_2374_: u32 = 0;
    let mut v___x_2375_: u32 = 0;
    let mut v___x_2376_: u32 = 0;
    let mut v___x_2377_: u32 = 0;
    let mut v___x_2378_: u32 = 0;
    let mut v___x_2379_: u32 = 0;
    let mut v___x_2380_: u32 = 0;
    let mut v___x_2381_: u32 = 0;
    let mut v___x_2382_: u32 = 0;
    let mut v___x_2383_: u32 = 0;
    let mut v___x_2384_: u32 = 0;
    let mut v___x_2385_: u32 = 0;
    let mut v_r_2386_: u32 = 0;
    let mut v___x_2387_: u32 = 0;
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: u32 = 0;
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: u8 = 0;
    let mut v_b_u2080_2403_: u8 = 0;
    let mut v___x_2404_: u8 = 0;
    let mut v_b_u2081_2405_: u8 = 0;
    let mut v_b_u2082_2406_: u8 = 0;
    let mut v___x_2407_: u32 = 0;
    let mut v___x_2408_: u32 = 0;
    let mut v___x_2409_: u32 = 0;
    let mut v___x_2410_: u32 = 0;
    let mut v___x_2411_: u32 = 0;
    let mut v___x_2412_: u32 = 0;
    let mut v___x_2413_: u32 = 0;
    let mut v___x_2414_: u32 = 0;
    let mut v_r_2415_: u32 = 0;
    let mut v___x_2416_: u32 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: u32 = 0;
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: u32 = 0;
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: u8 = 0;
    let mut v_b_u2080_2429_: u8 = 0;
    let mut v___x_2430_: u8 = 0;
    let mut v_b_u2081_2431_: u8 = 0;
    let mut v___x_2432_: u32 = 0;
    let mut v___x_2433_: u32 = 0;
    let mut v___x_2434_: u32 = 0;
    let mut v___x_2435_: u32 = 0;
    let mut v_r_2436_: u32 = 0;
    let mut v___x_2437_: u32 = 0;
    let mut v___x_2438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = lean_byte_array_size(v_b_2310_);
                v___x_2335_ = lean_nat_dec_lt(v_i_2311_, v___x_2334_);
                if v___x_2335_ == 0 {
                    crate::leanh::lean_dec(v_i_2311_);
                    v___x_2336_ = 1;
                    return v___x_2336_;
                } else {
                    if v___x_2335_ == 0 {
                        crate::leanh::lean_dec(v_i_2311_);
                        return v___x_2335_;
                    } else {
                        v___x_2337_ = lean_byte_array_fget(v_b_2310_, v_i_2311_);
                        v___x_2338_ = 128;
                        v___x_2339_ = lean_uint8_land(v___x_2337_, v___x_2338_);
                        v___x_2340_ = 0;
                        v___x_2341_ = lean_uint8_dec_eq(v___x_2339_, v___x_2340_);
                        if v___x_2341_ == 0 {
                            v___x_2342_ = 224;
                            v___x_2343_ = lean_uint8_land(v___x_2337_, v___x_2342_);
                            v___x_2344_ = 192;
                            v___x_2345_ = lean_uint8_dec_eq(v___x_2343_, v___x_2344_);
                            if v___x_2345_ == 0 {
                                v___x_2346_ = 240;
                                v___x_2347_ = lean_uint8_land(v___x_2337_, v___x_2346_);
                                v___x_2348_ = lean_uint8_dec_eq(v___x_2347_, v___x_2342_);
                                if v___x_2348_ == 0 {
                                    v___x_2349_ = 248;
                                    v___x_2350_ = lean_uint8_land(v___x_2337_, v___x_2349_);
                                    v___x_2351_ = lean_uint8_dec_eq(v___x_2350_, v___x_2346_);
                                    if v___x_2351_ == 0 {
                                        v___y_2317_ = v___x_2351_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2352_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_2353_ = lean_nat_add(v_i_2311_, v___x_2352_);
                                        v___x_2354_ = lean_nat_dec_lt(v___x_2353_, v___x_2334_);
                                        if v___x_2354_ == 0 {
                                            crate::leanh::lean_dec(v___x_2353_);
                                            v___y_2317_ = v___x_2348_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_2355_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_2356_ = lean_nat_add(v_i_2311_, v___x_2355_);
                                            v___x_2357_ =
                                                lean_byte_array_fget(v_b_2310_, v___x_2356_);
                                            crate::leanh::lean_dec(v___x_2356_);
                                            v___x_2358_ = lean_uint8_land(v___x_2357_, v___x_2344_);
                                            v___x_2359_ =
                                                lean_uint8_dec_eq(v___x_2358_, v___x_2338_);
                                            if v___x_2359_ == 0 {
                                                crate::leanh::lean_dec(v___x_2353_);
                                                v___y_2317_ = v___x_2359_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_2360_ = crate::leanh::lean_unsigned_to_nat(2);
                                                v___x_2361_ = lean_nat_add(v_i_2311_, v___x_2360_);
                                                v___x_2362_ =
                                                    lean_byte_array_fget(v_b_2310_, v___x_2361_);
                                                crate::leanh::lean_dec(v___x_2361_);
                                                v___x_2363_ =
                                                    lean_uint8_land(v___x_2362_, v___x_2344_);
                                                v___x_2364_ =
                                                    lean_uint8_dec_eq(v___x_2363_, v___x_2338_);
                                                if v___x_2364_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2353_);
                                                    v___y_2317_ = v___x_2364_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_2365_ = lean_byte_array_fget(
                                                        v_b_2310_,
                                                        v___x_2353_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2353_);
                                                    v___x_2366_ =
                                                        lean_uint8_land(v___x_2365_, v___x_2344_);
                                                    v___x_2367_ =
                                                        lean_uint8_dec_eq(v___x_2366_, v___x_2338_);
                                                    if v___x_2367_ == 0 {
                                                        v___y_2317_ = v___x_2367_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_2368_ = 7;
                                                        v_b_u2080_2369_ = lean_uint8_land(
                                                            v___x_2337_,
                                                            v___x_2368_,
                                                        );
                                                        v___x_2370_ = 63;
                                                        v_b_u2081_2371_ = lean_uint8_land(
                                                            v___x_2357_,
                                                            v___x_2370_,
                                                        );
                                                        v_b_u2082_2372_ = lean_uint8_land(
                                                            v___x_2362_,
                                                            v___x_2370_,
                                                        );
                                                        v_b_u2083_2373_ = lean_uint8_land(
                                                            v___x_2365_,
                                                            v___x_2370_,
                                                        );
                                                        v___x_2374_ =
                                                            lean_uint8_to_uint32(v_b_u2080_2369_);
                                                        v___x_2375_ = 18;
                                                        v___x_2376_ = lean_uint32_shift_left(
                                                            v___x_2374_,
                                                            v___x_2375_,
                                                        );
                                                        v___x_2377_ =
                                                            lean_uint8_to_uint32(v_b_u2081_2371_);
                                                        v___x_2378_ = 12;
                                                        v___x_2379_ = lean_uint32_shift_left(
                                                            v___x_2377_,
                                                            v___x_2378_,
                                                        );
                                                        v___x_2380_ = lean_uint32_lor(
                                                            v___x_2376_,
                                                            v___x_2379_,
                                                        );
                                                        v___x_2381_ =
                                                            lean_uint8_to_uint32(v_b_u2082_2372_);
                                                        v___x_2382_ = 6;
                                                        v___x_2383_ = lean_uint32_shift_left(
                                                            v___x_2381_,
                                                            v___x_2382_,
                                                        );
                                                        v___x_2384_ = lean_uint32_lor(
                                                            v___x_2380_,
                                                            v___x_2383_,
                                                        );
                                                        v___x_2385_ =
                                                            lean_uint8_to_uint32(v_b_u2083_2373_);
                                                        v_r_2386_ = lean_uint32_lor(
                                                            v___x_2384_,
                                                            v___x_2385_,
                                                        );
                                                        v___x_2387_ = 65536;
                                                        v___x_2388_ = lean_uint32_dec_le(
                                                            v___x_2387_,
                                                            v_r_2386_,
                                                        );
                                                        if v___x_2388_ == 0 {
                                                            v___y_2317_ = v___x_2348_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            v___x_2389_ = 1114111;
                                                            v___x_2390_ = lean_uint32_dec_le(
                                                                v_r_2386_,
                                                                v___x_2389_,
                                                            );
                                                            if v___x_2390_ == 0 {
                                                                v___y_2317_ = v___x_2348_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v___y_2317_ = v___x_2367_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_2391_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_2392_ = lean_nat_add(v_i_2311_, v___x_2391_);
                                    v___x_2393_ = lean_nat_dec_lt(v___x_2392_, v___x_2334_);
                                    if v___x_2393_ == 0 {
                                        crate::leanh::lean_dec(v___x_2392_);
                                        v___y_2317_ = v___x_2345_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2394_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_2395_ = lean_nat_add(v_i_2311_, v___x_2394_);
                                        v___x_2396_ = lean_byte_array_fget(v_b_2310_, v___x_2395_);
                                        crate::leanh::lean_dec(v___x_2395_);
                                        v___x_2397_ = lean_uint8_land(v___x_2396_, v___x_2344_);
                                        v___x_2398_ = lean_uint8_dec_eq(v___x_2397_, v___x_2338_);
                                        if v___x_2398_ == 0 {
                                            crate::leanh::lean_dec(v___x_2392_);
                                            v___y_2317_ = v___x_2398_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_2399_ =
                                                lean_byte_array_fget(v_b_2310_, v___x_2392_);
                                            crate::leanh::lean_dec(v___x_2392_);
                                            v___x_2400_ = lean_uint8_land(v___x_2399_, v___x_2344_);
                                            v___x_2401_ =
                                                lean_uint8_dec_eq(v___x_2400_, v___x_2338_);
                                            if v___x_2401_ == 0 {
                                                v___y_2317_ = v___x_2401_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_2402_ = 15;
                                                v_b_u2080_2403_ =
                                                    lean_uint8_land(v___x_2337_, v___x_2402_);
                                                v___x_2404_ = 63;
                                                v_b_u2081_2405_ =
                                                    lean_uint8_land(v___x_2396_, v___x_2404_);
                                                v_b_u2082_2406_ =
                                                    lean_uint8_land(v___x_2399_, v___x_2404_);
                                                v___x_2407_ = lean_uint8_to_uint32(v_b_u2080_2403_);
                                                v___x_2408_ = 12;
                                                v___x_2409_ = lean_uint32_shift_left(
                                                    v___x_2407_,
                                                    v___x_2408_,
                                                );
                                                v___x_2410_ = lean_uint8_to_uint32(v_b_u2081_2405_);
                                                v___x_2411_ = 6;
                                                v___x_2412_ = lean_uint32_shift_left(
                                                    v___x_2410_,
                                                    v___x_2411_,
                                                );
                                                v___x_2413_ =
                                                    lean_uint32_lor(v___x_2409_, v___x_2412_);
                                                v___x_2414_ = lean_uint8_to_uint32(v_b_u2082_2406_);
                                                v_r_2415_ =
                                                    lean_uint32_lor(v___x_2413_, v___x_2414_);
                                                v___x_2416_ = 2048;
                                                v___x_2417_ =
                                                    lean_uint32_dec_le(v___x_2416_, v_r_2415_);
                                                if v___x_2417_ == 0 {
                                                    v___y_2317_ = v___x_2345_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_2418_ = 55296;
                                                    v___x_2419_ =
                                                        lean_uint32_dec_lt(v_r_2415_, v___x_2418_);
                                                    if v___x_2419_ == 0 {
                                                        v___x_2420_ = 57343;
                                                        v___x_2421_ = lean_uint32_dec_lt(
                                                            v___x_2420_,
                                                            v_r_2415_,
                                                        );
                                                        if v___x_2421_ == 0 {
                                                            v___y_2317_ = v___x_2345_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            v___y_2317_ = v___x_2401_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___y_2317_ = v___x_2401_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_2422_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2423_ = lean_nat_add(v_i_2311_, v___x_2422_);
                                v___x_2424_ = lean_nat_dec_lt(v___x_2423_, v___x_2334_);
                                if v___x_2424_ == 0 {
                                    crate::leanh::lean_dec(v___x_2423_);
                                    v___y_2317_ = v___x_2341_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2425_ = lean_byte_array_fget(v_b_2310_, v___x_2423_);
                                    crate::leanh::lean_dec(v___x_2423_);
                                    v___x_2426_ = lean_uint8_land(v___x_2425_, v___x_2344_);
                                    v___x_2427_ = lean_uint8_dec_eq(v___x_2426_, v___x_2338_);
                                    if v___x_2427_ == 0 {
                                        v___y_2317_ = v___x_2427_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2428_ = 31;
                                        v_b_u2080_2429_ = lean_uint8_land(v___x_2337_, v___x_2428_);
                                        v___x_2430_ = 63;
                                        v_b_u2081_2431_ = lean_uint8_land(v___x_2425_, v___x_2430_);
                                        v___x_2432_ = lean_uint8_to_uint32(v_b_u2080_2429_);
                                        v___x_2433_ = 6;
                                        v___x_2434_ =
                                            lean_uint32_shift_left(v___x_2432_, v___x_2433_);
                                        v___x_2435_ = lean_uint8_to_uint32(v_b_u2081_2431_);
                                        v_r_2436_ = lean_uint32_lor(v___x_2434_, v___x_2435_);
                                        v___x_2437_ = 128;
                                        v___x_2438_ = lean_uint32_dec_le(v___x_2437_, v_r_2436_);
                                        v___y_2317_ = v___x_2438_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___y_2317_ = v___x_2341_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2314_ = lean_nat_add(v_i_2311_, v___y_2313_);
                crate::leanh::lean_dec(v_i_2311_);
                v_i_2311_ = v___x_2314_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2317_ == 0 {
                    crate::leanh::lean_dec(v_i_2311_);
                    return v___y_2317_;
                } else {
                    v___x_2318_ = lean_byte_array_fget(v_b_2310_, v_i_2311_);
                    v___x_2319_ = 128;
                    v___x_2320_ = lean_uint8_land(v___x_2318_, v___x_2319_);
                    v___x_2321_ = 0;
                    v___x_2322_ = lean_uint8_dec_eq(v___x_2320_, v___x_2321_);
                    if v___x_2322_ == 0 {
                        v___x_2323_ = 224;
                        v___x_2324_ = lean_uint8_land(v___x_2318_, v___x_2323_);
                        v___x_2325_ = 192;
                        v___x_2326_ = lean_uint8_dec_eq(v___x_2324_, v___x_2325_);
                        if v___x_2326_ == 0 {
                            v___x_2327_ = 240;
                            v___x_2328_ = lean_uint8_land(v___x_2318_, v___x_2327_);
                            v___x_2329_ = lean_uint8_dec_eq(v___x_2328_, v___x_2323_);
                            if v___x_2329_ == 0 {
                                v___x_2330_ = crate::leanh::lean_unsigned_to_nat(4);
                                v___y_2313_ = v___x_2330_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2331_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___y_2313_ = v___x_2331_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2332_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___y_2313_ = v___x_2332_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2333_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___y_2313_ = v___x_2333_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_validateUTF8_go___redArg___boxed(
    mut v_b_2439_: *mut crate::leanh::LeanObject,
    mut v_i_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: u8 = 0;
    let mut v_r_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_ByteArray_validateUTF8_go___redArg(v_b_2439_, v_i_2440_);
    crate::leanh::lean_dec_ref(v_b_2439_);
    v_r_2442_ = crate::leanh::lean_box((v_res_2441_) as usize);
    return v_r_2442_;
}
pub unsafe fn l_ByteArray_validateUTF8_go(
    mut v_b_2443_: *mut crate::leanh::LeanObject,
    mut v_i_2444_: *mut crate::leanh::LeanObject,
    mut v_hi_2445_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2446_: u8 = 0;
    v___x_2446_ = l_ByteArray_validateUTF8_go___redArg(v_b_2443_, v_i_2444_);
    return v___x_2446_;
}
pub unsafe fn l_ByteArray_validateUTF8_go___boxed(
    mut v_b_2447_: *mut crate::leanh::LeanObject,
    mut v_i_2448_: *mut crate::leanh::LeanObject,
    mut v_hi_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2450_: u8 = 0;
    let mut v_r_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_ByteArray_validateUTF8_go(v_b_2447_, v_i_2448_, v_hi_2449_);
    crate::leanh::lean_dec_ref(v_b_2447_);
    v_r_2451_ = crate::leanh::lean_box((v_res_2450_) as usize);
    return v_r_2451_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(
    mut v_x_2452_: u8,
    mut v_h__1_2453_: *mut crate::leanh::LeanObject,
    mut v_h__2_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_2452_ == 0 {
        let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2454_);
        v___x_2455_ = crate::leanh::lean_apply_1(v_h__1_2453_, crate::leanh::lean_box(0));
        return v___x_2455_;
    } else {
        let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2453_);
        v___x_2456_ = crate::leanh::lean_apply_1(v_h__2_2454_, crate::leanh::lean_box(0));
        return v___x_2456_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(
    mut v_x_2457_: *mut crate::leanh::LeanObject,
    mut v_h__1_2458_: *mut crate::leanh::LeanObject,
    mut v_h__2_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_2460_: u8 = 0;
    let mut v_res_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_2460_ = (crate::leanh::lean_unbox(v_x_2457_) as u8);
    v_res_2461_ =
        l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(
            v_x_26__boxed_2460_,
            v_h__1_2458_,
            v_h__2_2459_,
        );
    return v_res_2461_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(
    mut v_motive_2462_: *mut crate::leanh::LeanObject,
    mut v_x_2463_: u8,
    mut v_h__1_2464_: *mut crate::leanh::LeanObject,
    mut v_h__2_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_2463_ == 0 {
        let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2465_);
        v___x_2466_ = crate::leanh::lean_apply_1(v_h__1_2464_, crate::leanh::lean_box(0));
        return v___x_2466_;
    } else {
        let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2464_);
        v___x_2467_ = crate::leanh::lean_apply_1(v_h__2_2465_, crate::leanh::lean_box(0));
        return v___x_2467_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(
    mut v_motive_2468_: *mut crate::leanh::LeanObject,
    mut v_x_2469_: *mut crate::leanh::LeanObject,
    mut v_h__1_2470_: *mut crate::leanh::LeanObject,
    mut v_h__2_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_2472_: u8 = 0;
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_2472_ = (crate::leanh::lean_unbox(v_x_2469_) as u8);
    v_res_2473_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(
        v_motive_2468_,
        v_x_33__boxed_2472_,
        v_h__1_2470_,
        v_h__2_2471_,
    );
    return v_res_2473_;
}
pub unsafe fn l_ByteArray_validateUTF8___boxed(
    mut v_b_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2476_: u8 = 0;
    let mut v_r_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2476_ = lean_string_validate_utf8(v_b_2475_);
    crate::leanh::lean_dec_ref(v_b_2475_);
    v_r_2477_ = crate::leanh::lean_box((v_res_2476_) as usize);
    return v_r_2477_;
}
pub unsafe fn l_instDecidableIsValidUTF8(mut v_b_2478_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_2479_: u8 = 0;
    v___x_2479_ = lean_string_validate_utf8(v_b_2478_);
    return v___x_2479_;
}
pub unsafe fn l_instDecidableIsValidUTF8___boxed(
    mut v_b_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: u8 = 0;
    let mut v_r_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_instDecidableIsValidUTF8(v_b_2480_);
    crate::leanh::lean_dec_ref(v_b_2480_);
    v_r_2482_ = crate::leanh::lean_box((v_res_2481_) as usize);
    return v_r_2482_;
}
pub unsafe fn l_String_fromUTF8_x3f(
    mut v_a_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: u8 = 0;
    v___x_2484_ = lean_string_validate_utf8(v_a_2483_);
    if v___x_2484_ == 0 {
        let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2483_);
        v___x_2485_ = crate::leanh::lean_box(0);
        return v___x_2485_;
    } else {
        let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2486_ = lean_string_from_utf8_unchecked(v_a_2483_);
        v___x_2487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2487_, 0, v___x_2486_);
        return v___x_2487_;
    }
}
pub unsafe fn _init_l_String_fromUTF8_x21___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_String_fromUTF8_x21___closed__3;
    v___x_2493_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_2494_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_2495_ = l_String_fromUTF8_x21___closed__2;
    v___x_2496_ = l_String_fromUTF8_x21___closed__1;
    v___x_2497_ = l_mkPanicMessageWithDecl(
        v___x_2496_,
        v___x_2495_,
        v___x_2494_,
        v___x_2493_,
        v___x_2492_,
    );
    return v___x_2497_;
}
pub unsafe fn l_String_fromUTF8_x21(
    mut v_a_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: u8 = 0;
    v___x_2499_ = lean_string_validate_utf8(v_a_2498_);
    if v___x_2499_ == 0 {
        let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2498_);
        v___x_2500_ = l_String_fromUTF8_x21___closed__0;
        v___x_2501_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_fromUTF8_x21___closed__4),
            core::ptr::addr_of_mut!(l_String_fromUTF8_x21___closed__4_once),
            _init_l_String_fromUTF8_x21___closed__4,
        );
        v___x_2502_ = l_panic___redArg(v___x_2500_, v___x_2501_);
        return v___x_2502_;
    } else {
        let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2503_ = lean_string_from_utf8_unchecked(v_a_2498_);
        return v___x_2503_;
    }
}
pub unsafe fn l_String_Internal_toArray(
    mut v_b_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = lean_string_to_utf8(v_b_2504_);
    v___x_2506_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2507_ = l_ByteArray_utf8Decode_x3f___closed__0;
    v___x_2508_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_2505_, v___x_2506_, v___x_2507_);
    crate::leanh::lean_dec_ref(v___x_2505_);
    v_val_2509_ = crate::leanh::lean_ctor_get(v___x_2508_, 0);
    crate::leanh::lean_inc(v_val_2509_);
    crate::leanh::lean_dec(v___x_2508_);
    return v_val_2509_;
}
pub unsafe fn l_String_toList___boxed(
    mut v_s_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = lean_string_data(v_s_2511_);
    return v_res_2512_;
}
pub unsafe fn l_String_data___boxed(
    mut v_b_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = lean_string_data(v_b_2514_);
    return v_res_2515_;
}
pub unsafe fn _init_l_String_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = crate::leanh::lean_box(0);
    return v___x_2516_;
}
pub unsafe fn l_String_decidableLT___boxed(
    mut v_s_u2081_2519_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: u8 = 0;
    let mut v_r_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = lean_string_dec_lt(v_s_u2081_2519_, v_s_u2082_2520_);
    crate::leanh::lean_dec_ref(v_s_u2082_2520_);
    crate::leanh::lean_dec_ref(v_s_u2081_2519_);
    v_r_2522_ = crate::leanh::lean_box((v_res_2521_) as usize);
    return v_r_2522_;
}
pub unsafe fn _init_l_String_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = crate::leanh::lean_box(0);
    return v___x_2523_;
}
pub unsafe fn l_String_decLE(
    mut v_s_u2081_2524_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_2525_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2526_: u8 = 0;
    v___x_2526_ = lean_string_dec_lt(v_s_u2082_2525_, v_s_u2081_2524_);
    if v___x_2526_ == 0 {
        let mut v___x_2527_: u8 = 0;
        v___x_2527_ = 1;
        return v___x_2527_;
    } else {
        let mut v___x_2528_: u8 = 0;
        v___x_2528_ = 0;
        return v___x_2528_;
    }
}
pub unsafe fn l_String_decLE___boxed(
    mut v_s_u2081_2529_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2531_: u8 = 0;
    let mut v_r_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2531_ = l_String_decLE(v_s_u2081_2529_, v_s_u2082_2530_);
    crate::leanh::lean_dec_ref(v_s_u2082_2530_);
    crate::leanh::lean_dec_ref(v_s_u2081_2529_);
    v_r_2532_ = crate::leanh::lean_box((v_res_2531_) as usize);
    return v_r_2532_;
}
pub unsafe fn l_String_Pos_Raw_isValid___boxed(
    mut v_s_2535_: *mut crate::leanh::LeanObject,
    mut v_p_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2537_: u8 = 0;
    let mut v_r_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = lean_string_is_valid_pos(v_s_2535_, v_p_2536_);
    crate::leanh::lean_dec(v_p_2536_);
    crate::leanh::lean_dec_ref(v_s_2535_);
    v_r_2538_ = crate::leanh::lean_box((v_res_2537_) as usize);
    return v_r_2538_;
}
pub unsafe fn l_String_instDecidableIsValid(
    mut v_s_2539_: *mut crate::leanh::LeanObject,
    mut v_p_2540_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2541_: u8 = 0;
    v___x_2541_ = lean_string_is_valid_pos(v_s_2539_, v_p_2540_);
    return v___x_2541_;
}
pub unsafe fn l_String_instDecidableIsValid___boxed(
    mut v_s_2542_: *mut crate::leanh::LeanObject,
    mut v_p_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2544_: u8 = 0;
    let mut v_r_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_String_instDecidableIsValid(v_s_2542_, v_p_2543_);
    crate::leanh::lean_dec(v_p_2543_);
    crate::leanh::lean_dec_ref(v_s_2542_);
    v_r_2545_ = crate::leanh::lean_box((v_res_2544_) as usize);
    return v_r_2545_;
}
pub unsafe fn l_String_extract___boxed(
    mut v_s_2549_: *mut crate::leanh::LeanObject,
    mut v_b_2550_: *mut crate::leanh::LeanObject,
    mut v_e_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ = lean_string_utf8_extract(v_s_2549_, v_b_2550_, v_e_2551_);
    crate::leanh::lean_dec(v_e_2551_);
    crate::leanh::lean_dec(v_b_2550_);
    crate::leanh::lean_dec_ref(v_s_2549_);
    return v_res_2552_;
}
pub unsafe fn l_String_Pos_extract(
    mut v_s_2553_: *mut crate::leanh::LeanObject,
    mut v_b_2554_: *mut crate::leanh::LeanObject,
    mut v_e_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2556_ = lean_string_utf8_extract(v_s_2553_, v_b_2554_, v_e_2555_);
    return v___x_2556_;
}
pub unsafe fn l_String_Pos_extract___boxed(
    mut v_s_2557_: *mut crate::leanh::LeanObject,
    mut v_b_2558_: *mut crate::leanh::LeanObject,
    mut v_e_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_String_Pos_extract(v_s_2557_, v_b_2558_, v_e_2559_);
    crate::leanh::lean_dec(v_e_2559_);
    crate::leanh::lean_dec(v_b_2558_);
    crate::leanh::lean_dec_ref(v_s_2557_);
    return v_res_2560_;
}
pub unsafe fn l_String_Slice_copy(
    mut v_s_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_2562_ = crate::leanh::lean_ctor_get(v_s_2561_, 0);
    v_startInclusive_2563_ = crate::leanh::lean_ctor_get(v_s_2561_, 1);
    v_endExclusive_2564_ = crate::leanh::lean_ctor_get(v_s_2561_, 2);
    v___x_2565_ =
        lean_string_utf8_extract(v_str_2562_, v_startInclusive_2563_, v_endExclusive_2564_);
    return v___x_2565_;
}
pub unsafe fn l_String_Slice_copy___boxed(
    mut v_s_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_String_Slice_copy(v_s_2566_);
    crate::leanh::lean_dec_ref(v_s_2566_);
    return v_res_2567_;
}
pub unsafe fn l_String_Pos_Raw_isValidForSlice(
    mut v_s_2568_: *mut crate::leanh::LeanObject,
    mut v_p_2569_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    v_str_2570_ = crate::leanh::lean_ctor_get(v_s_2568_, 0);
    v_startInclusive_2571_ = crate::leanh::lean_ctor_get(v_s_2568_, 1);
    v_endExclusive_2572_ = crate::leanh::lean_ctor_get(v_s_2568_, 2);
    v___x_2573_ = lean_nat_sub(v_endExclusive_2572_, v_startInclusive_2571_);
    v___x_2574_ = lean_nat_dec_lt(v_p_2569_, v___x_2573_);
    if v___x_2574_ == 0 {
        let mut v___x_2575_: u8 = 0;
        v___x_2575_ = lean_nat_dec_eq(v_p_2569_, v___x_2573_);
        crate::leanh::lean_dec(v___x_2573_);
        return v___x_2575_;
    } else {
        let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2577_: u8 = 0;
        let mut v___x_2578_: u8 = 0;
        crate::leanh::lean_dec(v___x_2573_);
        v___x_2576_ = lean_nat_add(v_startInclusive_2571_, v_p_2569_);
        v___x_2577_ = lean_string_get_byte_fast(v_str_2570_, v___x_2576_);
        v___x_2578_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_2577_);
        return v___x_2578_;
    }
}
pub unsafe fn l_String_Pos_Raw_isValidForSlice___boxed(
    mut v_s_2579_: *mut crate::leanh::LeanObject,
    mut v_p_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2581_: u8 = 0;
    let mut v_r_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_String_Pos_Raw_isValidForSlice(v_s_2579_, v_p_2580_);
    crate::leanh::lean_dec(v_p_2580_);
    crate::leanh::lean_dec_ref(v_s_2579_);
    v_r_2582_ = crate::leanh::lean_box((v_res_2581_) as usize);
    return v_r_2582_;
}
pub unsafe fn l_String_instDecidableIsValidForSlice(
    mut v_s_2583_: *mut crate::leanh::LeanObject,
    mut v_p_2584_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2585_: u8 = 0;
    v___x_2585_ = l_String_Pos_Raw_isValidForSlice(v_s_2583_, v_p_2584_);
    return v___x_2585_;
}
pub unsafe fn l_String_instDecidableIsValidForSlice___boxed(
    mut v_s_2586_: *mut crate::leanh::LeanObject,
    mut v_p_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2588_: u8 = 0;
    let mut v_r_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2588_ = l_String_instDecidableIsValidForSlice(v_s_2586_, v_p_2587_);
    crate::leanh::lean_dec(v_p_2587_);
    crate::leanh::lean_dec_ref(v_s_2586_);
    v_r_2589_ = crate::leanh::lean_box((v_res_2588_) as usize);
    return v_r_2589_;
}
pub unsafe fn l_String_Slice_Pos_str(
    mut v_s_2590_: *mut crate::leanh::LeanObject,
    mut v_pos_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2592_ = crate::leanh::lean_ctor_get(v_s_2590_, 1);
    v___x_2593_ = lean_nat_add(v_startInclusive_2592_, v_pos_2591_);
    return v___x_2593_;
}
pub unsafe fn l_String_Slice_Pos_str___boxed(
    mut v_s_2594_: *mut crate::leanh::LeanObject,
    mut v_pos_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_String_Slice_Pos_str(v_s_2594_, v_pos_2595_);
    crate::leanh::lean_dec(v_pos_2595_);
    crate::leanh::lean_dec_ref(v_s_2594_);
    return v_res_2596_;
}
pub unsafe fn l_String_Slice_Pos_ofStr___redArg(
    mut v_s_2597_: *mut crate::leanh::LeanObject,
    mut v_pos_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2599_ = crate::leanh::lean_ctor_get(v_s_2597_, 1);
    v___x_2600_ = lean_nat_sub(v_pos_2598_, v_startInclusive_2599_);
    return v___x_2600_;
}
pub unsafe fn l_String_Slice_Pos_ofStr___redArg___boxed(
    mut v_s_2601_: *mut crate::leanh::LeanObject,
    mut v_pos_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2603_ = l_String_Slice_Pos_ofStr___redArg(v_s_2601_, v_pos_2602_);
    crate::leanh::lean_dec(v_pos_2602_);
    crate::leanh::lean_dec_ref(v_s_2601_);
    return v_res_2603_;
}
pub unsafe fn l_String_Slice_Pos_ofStr(
    mut v_s_2604_: *mut crate::leanh::LeanObject,
    mut v_pos_2605_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_2606_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2608_ = crate::leanh::lean_ctor_get(v_s_2604_, 1);
    v___x_2609_ = lean_nat_sub(v_pos_2605_, v_startInclusive_2608_);
    return v___x_2609_;
}
pub unsafe fn l_String_Slice_Pos_ofStr___boxed(
    mut v_s_2610_: *mut crate::leanh::LeanObject,
    mut v_pos_2611_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_2612_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ =
        l_String_Slice_Pos_ofStr(v_s_2610_, v_pos_2611_, v_h_u2081_2612_, v_h_u2082_2613_);
    crate::leanh::lean_dec(v_pos_2611_);
    crate::leanh::lean_dec_ref(v_s_2610_);
    return v_res_2614_;
}
pub unsafe fn l_String_Slice_sliceFrom(
    mut v_s_2615_: *mut crate::leanh::LeanObject,
    mut v_pos_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2617_ = crate::leanh::lean_ctor_get(v_s_2615_, 0);
                v_startInclusive_2618_ = crate::leanh::lean_ctor_get(v_s_2615_, 1);
                v_endExclusive_2619_ = crate::leanh::lean_ctor_get(v_s_2615_, 2);
                v_isSharedCheck_2627_ = (!crate::leanh::lean_is_exclusive(v_s_2615_)) as u8;
                if v_isSharedCheck_2627_ == 0 {
                    v___x_2621_ = v_s_2615_;
                    v_isShared_2622_ = v_isSharedCheck_2627_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_2619_);
                    crate::leanh::lean_inc(v_startInclusive_2618_);
                    crate::leanh::lean_inc(v_str_2617_);
                    crate::leanh::lean_dec(v_s_2615_);
                    v___x_2621_ = crate::leanh::lean_box(0);
                    v_isShared_2622_ = v_isSharedCheck_2627_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2623_ = lean_nat_add(v_startInclusive_2618_, v_pos_2616_);
                crate::leanh::lean_dec(v_startInclusive_2618_);
                if v_isShared_2622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2621_, 1, v___x_2623_);
                    v___x_2625_ = v___x_2621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_str_2617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___x_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_endExclusive_2619_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_sliceFrom___boxed(
    mut v_s_2628_: *mut crate::leanh::LeanObject,
    mut v_pos_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_String_Slice_sliceFrom(v_s_2628_, v_pos_2629_);
    crate::leanh::lean_dec(v_pos_2629_);
    return v_res_2630_;
}
pub unsafe fn l_String_Slice_replaceStart(
    mut v_s_2631_: *mut crate::leanh::LeanObject,
    mut v_pos_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2633_ = crate::leanh::lean_ctor_get(v_s_2631_, 0);
                v_startInclusive_2634_ = crate::leanh::lean_ctor_get(v_s_2631_, 1);
                v_endExclusive_2635_ = crate::leanh::lean_ctor_get(v_s_2631_, 2);
                v_isSharedCheck_2643_ = (!crate::leanh::lean_is_exclusive(v_s_2631_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v___x_2637_ = v_s_2631_;
                    v_isShared_2638_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_2635_);
                    crate::leanh::lean_inc(v_startInclusive_2634_);
                    crate::leanh::lean_inc(v_str_2633_);
                    crate::leanh::lean_dec(v_s_2631_);
                    v___x_2637_ = crate::leanh::lean_box(0);
                    v_isShared_2638_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2639_ = lean_nat_add(v_startInclusive_2634_, v_pos_2632_);
                crate::leanh::lean_dec(v_startInclusive_2634_);
                if v_isShared_2638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2637_, 1, v___x_2639_);
                    v___x_2641_ = v___x_2637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_str_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_endExclusive_2635_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_replaceStart___boxed(
    mut v_s_2644_: *mut crate::leanh::LeanObject,
    mut v_pos_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_String_Slice_replaceStart(v_s_2644_, v_pos_2645_);
    crate::leanh::lean_dec(v_pos_2645_);
    return v_res_2646_;
}
pub unsafe fn l_String_Slice_sliceTo(
    mut v_s_2647_: *mut crate::leanh::LeanObject,
    mut v_pos_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut v_unused_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2649_ = crate::leanh::lean_ctor_get(v_s_2647_, 0);
                v_startInclusive_2650_ = crate::leanh::lean_ctor_get(v_s_2647_, 1);
                v_isSharedCheck_2658_ = (!crate::leanh::lean_is_exclusive(v_s_2647_)) as u8;
                if v_isSharedCheck_2658_ == 0 {
                    v_unused_2659_ = crate::leanh::lean_ctor_get(v_s_2647_, 2);
                    crate::leanh::lean_dec(v_unused_2659_);
                    v___x_2652_ = v_s_2647_;
                    v_isShared_2653_ = v_isSharedCheck_2658_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_2650_);
                    crate::leanh::lean_inc(v_str_2649_);
                    crate::leanh::lean_dec(v_s_2647_);
                    v___x_2652_ = crate::leanh::lean_box(0);
                    v_isShared_2653_ = v_isSharedCheck_2658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2654_ = lean_nat_add(v_startInclusive_2650_, v_pos_2648_);
                if v_isShared_2653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2652_, 2, v___x_2654_);
                    v___x_2656_ = v___x_2652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_str_2649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_startInclusive_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 2, v___x_2654_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_sliceTo___boxed(
    mut v_s_2660_: *mut crate::leanh::LeanObject,
    mut v_pos_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2662_ = l_String_Slice_sliceTo(v_s_2660_, v_pos_2661_);
    crate::leanh::lean_dec(v_pos_2661_);
    return v_res_2662_;
}
pub unsafe fn l_String_Slice_replaceEnd(
    mut v_s_2663_: *mut crate::leanh::LeanObject,
    mut v_pos_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_unused_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2665_ = crate::leanh::lean_ctor_get(v_s_2663_, 0);
                v_startInclusive_2666_ = crate::leanh::lean_ctor_get(v_s_2663_, 1);
                v_isSharedCheck_2674_ = (!crate::leanh::lean_is_exclusive(v_s_2663_)) as u8;
                if v_isSharedCheck_2674_ == 0 {
                    v_unused_2675_ = crate::leanh::lean_ctor_get(v_s_2663_, 2);
                    crate::leanh::lean_dec(v_unused_2675_);
                    v___x_2668_ = v_s_2663_;
                    v_isShared_2669_ = v_isSharedCheck_2674_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_2666_);
                    crate::leanh::lean_inc(v_str_2665_);
                    crate::leanh::lean_dec(v_s_2663_);
                    v___x_2668_ = crate::leanh::lean_box(0);
                    v_isShared_2669_ = v_isSharedCheck_2674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2670_ = lean_nat_add(v_startInclusive_2666_, v_pos_2664_);
                if v_isShared_2669_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2668_, 2, v___x_2670_);
                    v___x_2672_ = v___x_2668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2673_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_str_2665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_startInclusive_2666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 2, v___x_2670_);
                    v___x_2672_ = v_reuseFailAlloc_2673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_replaceEnd___boxed(
    mut v_s_2676_: *mut crate::leanh::LeanObject,
    mut v_pos_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_String_Slice_replaceEnd(v_s_2676_, v_pos_2677_);
    crate::leanh::lean_dec(v_pos_2677_);
    return v_res_2678_;
}
pub unsafe fn l_String_Slice_slice___redArg(
    mut v_s_2679_: *mut crate::leanh::LeanObject,
    mut v_newStart_2680_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2682_ = crate::leanh::lean_ctor_get(v_s_2679_, 0);
                v_startInclusive_2683_ = crate::leanh::lean_ctor_get(v_s_2679_, 1);
                v_isSharedCheck_2692_ = (!crate::leanh::lean_is_exclusive(v_s_2679_)) as u8;
                if v_isSharedCheck_2692_ == 0 {
                    v_unused_2693_ = crate::leanh::lean_ctor_get(v_s_2679_, 2);
                    crate::leanh::lean_dec(v_unused_2693_);
                    v___x_2685_ = v_s_2679_;
                    v_isShared_2686_ = v_isSharedCheck_2692_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_2683_);
                    crate::leanh::lean_inc(v_str_2682_);
                    crate::leanh::lean_dec(v_s_2679_);
                    v___x_2685_ = crate::leanh::lean_box(0);
                    v_isShared_2686_ = v_isSharedCheck_2692_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2687_ = lean_nat_add(v_startInclusive_2683_, v_newStart_2680_);
                v___x_2688_ = lean_nat_add(v_startInclusive_2683_, v_newEnd_2681_);
                crate::leanh::lean_dec(v_startInclusive_2683_);
                if v_isShared_2686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2685_, 2, v___x_2688_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 1, v___x_2687_);
                    v___x_2690_ = v___x_2685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_str_2682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 2, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_slice___redArg___boxed(
    mut v_s_2694_: *mut crate::leanh::LeanObject,
    mut v_newStart_2695_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2697_ = l_String_Slice_slice___redArg(v_s_2694_, v_newStart_2695_, v_newEnd_2696_);
    crate::leanh::lean_dec(v_newEnd_2696_);
    crate::leanh::lean_dec(v_newStart_2695_);
    return v_res_2697_;
}
pub unsafe fn l_String_Slice_slice(
    mut v_s_2698_: *mut crate::leanh::LeanObject,
    mut v_newStart_2699_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2700_: *mut crate::leanh::LeanObject,
    mut v_h_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2712_: u8 = 0;
    let mut v_unused_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2702_ = crate::leanh::lean_ctor_get(v_s_2698_, 0);
                v_startInclusive_2703_ = crate::leanh::lean_ctor_get(v_s_2698_, 1);
                v_isSharedCheck_2712_ = (!crate::leanh::lean_is_exclusive(v_s_2698_)) as u8;
                if v_isSharedCheck_2712_ == 0 {
                    v_unused_2713_ = crate::leanh::lean_ctor_get(v_s_2698_, 2);
                    crate::leanh::lean_dec(v_unused_2713_);
                    v___x_2705_ = v_s_2698_;
                    v_isShared_2706_ = v_isSharedCheck_2712_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_2703_);
                    crate::leanh::lean_inc(v_str_2702_);
                    crate::leanh::lean_dec(v_s_2698_);
                    v___x_2705_ = crate::leanh::lean_box(0);
                    v_isShared_2706_ = v_isSharedCheck_2712_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2707_ = lean_nat_add(v_startInclusive_2703_, v_newStart_2699_);
                v___x_2708_ = lean_nat_add(v_startInclusive_2703_, v_newEnd_2700_);
                crate::leanh::lean_dec(v_startInclusive_2703_);
                if v_isShared_2706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2705_, 2, v___x_2708_);
                    crate::leanh::lean_ctor_set(v___x_2705_, 1, v___x_2707_);
                    v___x_2710_ = v___x_2705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2711_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_str_2702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 2, v___x_2708_);
                    v___x_2710_ = v_reuseFailAlloc_2711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_slice___boxed(
    mut v_s_2714_: *mut crate::leanh::LeanObject,
    mut v_newStart_2715_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2716_: *mut crate::leanh::LeanObject,
    mut v_h_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_String_Slice_slice(v_s_2714_, v_newStart_2715_, v_newEnd_2716_, v_h_2717_);
    crate::leanh::lean_dec(v_newEnd_2716_);
    crate::leanh::lean_dec(v_newStart_2715_);
    return v_res_2718_;
}
pub unsafe fn l_String_Slice_replaceStartEnd___redArg(
    mut v_s_2719_: *mut crate::leanh::LeanObject,
    mut v_newStart_2720_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v_unused_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2722_ = crate::leanh::lean_ctor_get(v_s_2719_, 0);
                v_startInclusive_2723_ = crate::leanh::lean_ctor_get(v_s_2719_, 1);
                v_isSharedCheck_2732_ = (!crate::leanh::lean_is_exclusive(v_s_2719_)) as u8;
                if v_isSharedCheck_2732_ == 0 {
                    v_unused_2733_ = crate::leanh::lean_ctor_get(v_s_2719_, 2);
                    crate::leanh::lean_dec(v_unused_2733_);
                    v___x_2725_ = v_s_2719_;
                    v_isShared_2726_ = v_isSharedCheck_2732_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_2723_);
                    crate::leanh::lean_inc(v_str_2722_);
                    crate::leanh::lean_dec(v_s_2719_);
                    v___x_2725_ = crate::leanh::lean_box(0);
                    v_isShared_2726_ = v_isSharedCheck_2732_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2727_ = lean_nat_add(v_startInclusive_2723_, v_newStart_2720_);
                v___x_2728_ = lean_nat_add(v_startInclusive_2723_, v_newEnd_2721_);
                crate::leanh::lean_dec(v_startInclusive_2723_);
                if v_isShared_2726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2725_, 2, v___x_2728_);
                    crate::leanh::lean_ctor_set(v___x_2725_, 1, v___x_2727_);
                    v___x_2730_ = v___x_2725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2731_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_str_2722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2731_, 1, v___x_2727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2731_, 2, v___x_2728_);
                    v___x_2730_ = v_reuseFailAlloc_2731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_replaceStartEnd___redArg___boxed(
    mut v_s_2734_: *mut crate::leanh::LeanObject,
    mut v_newStart_2735_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2737_ =
        l_String_Slice_replaceStartEnd___redArg(v_s_2734_, v_newStart_2735_, v_newEnd_2736_);
    crate::leanh::lean_dec(v_newEnd_2736_);
    crate::leanh::lean_dec(v_newStart_2735_);
    return v_res_2737_;
}
pub unsafe fn l_String_Slice_replaceStartEnd(
    mut v_s_2738_: *mut crate::leanh::LeanObject,
    mut v_newStart_2739_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2740_: *mut crate::leanh::LeanObject,
    mut v_h_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ =
        l_String_Slice_replaceStartEnd___redArg(v_s_2738_, v_newStart_2739_, v_newEnd_2740_);
    return v___x_2742_;
}
pub unsafe fn l_String_Slice_replaceStartEnd___boxed(
    mut v_s_2743_: *mut crate::leanh::LeanObject,
    mut v_newStart_2744_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2745_: *mut crate::leanh::LeanObject,
    mut v_h_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ =
        l_String_Slice_replaceStartEnd(v_s_2743_, v_newStart_2744_, v_newEnd_2745_, v_h_2746_);
    crate::leanh::lean_dec(v_newEnd_2745_);
    crate::leanh::lean_dec(v_newStart_2744_);
    return v_res_2747_;
}
pub unsafe fn l_String_Slice_slice_x3f(
    mut v_s_2748_: *mut crate::leanh::LeanObject,
    mut v_newStart_2749_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2757_: u8 = 0;
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut v_unused_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2751_ = lean_nat_dec_le(v_newStart_2749_, v_newEnd_2750_);
                if v___x_2751_ == 0 {
                    crate::leanh::lean_dec_ref(v_s_2748_);
                    v___x_2752_ = crate::leanh::lean_box(0);
                    return v___x_2752_;
                } else {
                    v_str_2753_ = crate::leanh::lean_ctor_get(v_s_2748_, 0);
                    v_startInclusive_2754_ = crate::leanh::lean_ctor_get(v_s_2748_, 1);
                    v_isSharedCheck_2764_ = (!crate::leanh::lean_is_exclusive(v_s_2748_)) as u8;
                    if v_isSharedCheck_2764_ == 0 {
                        v_unused_2765_ = crate::leanh::lean_ctor_get(v_s_2748_, 2);
                        crate::leanh::lean_dec(v_unused_2765_);
                        v___x_2756_ = v_s_2748_;
                        v_isShared_2757_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_2754_);
                        crate::leanh::lean_inc(v_str_2753_);
                        crate::leanh::lean_dec(v_s_2748_);
                        v___x_2756_ = crate::leanh::lean_box(0);
                        v_isShared_2757_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2758_ = lean_nat_add(v_startInclusive_2754_, v_newStart_2749_);
                v___x_2759_ = lean_nat_add(v_startInclusive_2754_, v_newEnd_2750_);
                crate::leanh::lean_dec(v_startInclusive_2754_);
                if v_isShared_2757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2756_, 2, v___x_2759_);
                    crate::leanh::lean_ctor_set(v___x_2756_, 1, v___x_2758_);
                    v___x_2761_ = v___x_2756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2763_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_str_2753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2758_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 2, v___x_2759_);
                    v___x_2761_ = v_reuseFailAlloc_2763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2762_, 0, v___x_2761_);
                return v___x_2762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_slice_x3f___boxed(
    mut v_s_2766_: *mut crate::leanh::LeanObject,
    mut v_newStart_2767_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2769_ = l_String_Slice_slice_x3f(v_s_2766_, v_newStart_2767_, v_newEnd_2768_);
    crate::leanh::lean_dec(v_newEnd_2768_);
    crate::leanh::lean_dec(v_newStart_2767_);
    return v_res_2769_;
}
pub unsafe fn l_panic___at___00String_Slice_slice_x21_spec__0(
    mut v_msg_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2771_ = l_String_instInhabitedSlice;
    v___x_2772_ = lean_panic_fn_borrowed(v___x_2771_, v_msg_2770_);
    return v___x_2772_;
}
pub unsafe fn _init_l_String_Slice_slice_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = l_String_Slice_slice_x21___closed__1;
    v___x_2776_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2777_ = crate::leanh::lean_unsigned_to_nat(1096);
    v___x_2778_ = l_String_Slice_slice_x21___closed__0;
    v___x_2779_ = l_String_fromUTF8_x21___closed__1;
    v___x_2780_ = l_mkPanicMessageWithDecl(
        v___x_2779_,
        v___x_2778_,
        v___x_2777_,
        v___x_2776_,
        v___x_2775_,
    );
    return v___x_2780_;
}
pub unsafe fn l_String_Slice_slice_x21(
    mut v_s_2781_: *mut crate::leanh::LeanObject,
    mut v_newStart_2782_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: u8 = 0;
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_unused_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2784_ = lean_nat_dec_le(v_newStart_2782_, v_newEnd_2783_);
                if v___x_2784_ == 0 {
                    crate::leanh::lean_dec_ref(v_s_2781_);
                    v___x_2785_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_String_Slice_slice_x21___closed__2),
                        core::ptr::addr_of_mut!(l_String_Slice_slice_x21___closed__2_once),
                        _init_l_String_Slice_slice_x21___closed__2,
                    );
                    v___x_2786_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_2785_);
                    return v___x_2786_;
                } else {
                    v_str_2787_ = crate::leanh::lean_ctor_get(v_s_2781_, 0);
                    v_startInclusive_2788_ = crate::leanh::lean_ctor_get(v_s_2781_, 1);
                    v_isSharedCheck_2797_ = (!crate::leanh::lean_is_exclusive(v_s_2781_)) as u8;
                    if v_isSharedCheck_2797_ == 0 {
                        v_unused_2798_ = crate::leanh::lean_ctor_get(v_s_2781_, 2);
                        crate::leanh::lean_dec(v_unused_2798_);
                        v___x_2790_ = v_s_2781_;
                        v_isShared_2791_ = v_isSharedCheck_2797_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_2788_);
                        crate::leanh::lean_inc(v_str_2787_);
                        crate::leanh::lean_dec(v_s_2781_);
                        v___x_2790_ = crate::leanh::lean_box(0);
                        v_isShared_2791_ = v_isSharedCheck_2797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2792_ = lean_nat_add(v_startInclusive_2788_, v_newStart_2782_);
                v___x_2793_ = lean_nat_add(v_startInclusive_2788_, v_newEnd_2783_);
                crate::leanh::lean_dec(v_startInclusive_2788_);
                if v_isShared_2791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2790_, 2, v___x_2793_);
                    crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2792_);
                    v___x_2795_ = v___x_2790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_str_2787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 2, v___x_2793_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_slice_x21___boxed(
    mut v_s_2799_: *mut crate::leanh::LeanObject,
    mut v_newStart_2800_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2802_ = l_String_Slice_slice_x21(v_s_2799_, v_newStart_2800_, v_newEnd_2801_);
    crate::leanh::lean_dec(v_newEnd_2801_);
    crate::leanh::lean_dec(v_newStart_2800_);
    return v_res_2802_;
}
pub unsafe fn l_String_Slice_replaceStartEnd_x21(
    mut v_s_2803_: *mut crate::leanh::LeanObject,
    mut v_newStart_2804_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2806_ = l_String_Slice_slice_x21(v_s_2803_, v_newStart_2804_, v_newEnd_2805_);
    return v___x_2806_;
}
pub unsafe fn l_String_Slice_replaceStartEnd_x21___boxed(
    mut v_s_2807_: *mut crate::leanh::LeanObject,
    mut v_newStart_2808_: *mut crate::leanh::LeanObject,
    mut v_newEnd_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_String_Slice_replaceStartEnd_x21(v_s_2807_, v_newStart_2808_, v_newEnd_2809_);
    crate::leanh::lean_dec(v_newEnd_2809_);
    crate::leanh::lean_dec(v_newStart_2808_);
    return v_res_2810_;
}
pub unsafe fn l_String_decodeChar___boxed(
    mut v_s_2814_: *mut crate::leanh::LeanObject,
    mut v_byteIdx_2815_: *mut crate::leanh::LeanObject,
    mut v_h_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2817_: u32 = 0;
    let mut v_r_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = lean_string_utf8_get_fast(v_s_2814_, v_byteIdx_2815_);
    crate::leanh::lean_dec(v_byteIdx_2815_);
    crate::leanh::lean_dec_ref(v_s_2814_);
    v_r_2818_ = crate::leanh::lean_box_uint32(v_res_2817_);
    return v_r_2818_;
}
pub unsafe fn l_String_Slice_Pos_get___redArg(
    mut v_s_2819_: *mut crate::leanh::LeanObject,
    mut v_pos_2820_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_str_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u32 = 0;
    v_str_2821_ = crate::leanh::lean_ctor_get(v_s_2819_, 0);
    v_startInclusive_2822_ = crate::leanh::lean_ctor_get(v_s_2819_, 1);
    v___x_2823_ = lean_nat_add(v_startInclusive_2822_, v_pos_2820_);
    v___x_2824_ = lean_string_utf8_get_fast(v_str_2821_, v___x_2823_);
    crate::leanh::lean_dec(v___x_2823_);
    return v___x_2824_;
}
pub unsafe fn l_String_Slice_Pos_get___redArg___boxed(
    mut v_s_2825_: *mut crate::leanh::LeanObject,
    mut v_pos_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: u32 = 0;
    let mut v_r_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_String_Slice_Pos_get___redArg(v_s_2825_, v_pos_2826_);
    crate::leanh::lean_dec(v_pos_2826_);
    crate::leanh::lean_dec_ref(v_s_2825_);
    v_r_2828_ = crate::leanh::lean_box_uint32(v_res_2827_);
    return v_r_2828_;
}
pub unsafe fn l_String_Slice_Pos_get(
    mut v_s_2829_: *mut crate::leanh::LeanObject,
    mut v_pos_2830_: *mut crate::leanh::LeanObject,
    mut v_h_2831_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_str_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u32 = 0;
    v_str_2832_ = crate::leanh::lean_ctor_get(v_s_2829_, 0);
    v_startInclusive_2833_ = crate::leanh::lean_ctor_get(v_s_2829_, 1);
    v___x_2834_ = lean_nat_add(v_startInclusive_2833_, v_pos_2830_);
    v___x_2835_ = lean_string_utf8_get_fast(v_str_2832_, v___x_2834_);
    crate::leanh::lean_dec(v___x_2834_);
    return v___x_2835_;
}
pub unsafe fn l_String_Slice_Pos_get___boxed(
    mut v_s_2836_: *mut crate::leanh::LeanObject,
    mut v_pos_2837_: *mut crate::leanh::LeanObject,
    mut v_h_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2839_: u32 = 0;
    let mut v_r_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l_String_Slice_Pos_get(v_s_2836_, v_pos_2837_, v_h_2838_);
    crate::leanh::lean_dec(v_pos_2837_);
    crate::leanh::lean_dec_ref(v_s_2836_);
    v_r_2840_ = crate::leanh::lean_box_uint32(v_res_2839_);
    return v_r_2840_;
}
pub unsafe fn l_String_Slice_Pos_get_x3f(
    mut v_s_2841_: *mut crate::leanh::LeanObject,
    mut v_pos_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    v_str_2843_ = crate::leanh::lean_ctor_get(v_s_2841_, 0);
    v_startInclusive_2844_ = crate::leanh::lean_ctor_get(v_s_2841_, 1);
    v_endExclusive_2845_ = crate::leanh::lean_ctor_get(v_s_2841_, 2);
    v___x_2846_ = lean_nat_sub(v_endExclusive_2845_, v_startInclusive_2844_);
    v___x_2847_ = lean_nat_dec_eq(v_pos_2842_, v___x_2846_);
    crate::leanh::lean_dec(v___x_2846_);
    if v___x_2847_ == 0 {
        let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2849_: u32 = 0;
        let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2848_ = lean_nat_add(v_startInclusive_2844_, v_pos_2842_);
        v___x_2849_ = lean_string_utf8_get_fast(v_str_2843_, v___x_2848_);
        crate::leanh::lean_dec(v___x_2848_);
        v___x_2850_ = crate::leanh::lean_box_uint32(v___x_2849_);
        v___x_2851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2851_, 0, v___x_2850_);
        return v___x_2851_;
    } else {
        let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2852_ = crate::leanh::lean_box(0);
        return v___x_2852_;
    }
}
pub unsafe fn l_String_Slice_Pos_get_x3f___boxed(
    mut v_s_2853_: *mut crate::leanh::LeanObject,
    mut v_pos_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2855_ = l_String_Slice_Pos_get_x3f(v_s_2853_, v_pos_2854_);
    crate::leanh::lean_dec(v_pos_2854_);
    crate::leanh::lean_dec_ref(v_s_2853_);
    return v_res_2855_;
}
pub unsafe fn _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: u32 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2856_ = 65;
    v___x_2857_ = crate::leanh::lean_box_uint32(v___x_2856_);
    return v___x_2857_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_get_x21_spec__0(
    mut v_msg_2858_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u32 = 0;
    v___x_2859_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
    v___x_2860_ = lean_panic_fn_borrowed(v___x_2859_, v_msg_2858_);
    v___x_2861_ = crate::leanh::lean_unbox_uint32(v___x_2860_);
    crate::leanh::lean_dec(v___x_2860_);
    return v___x_2861_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(
    mut v_msg_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2863_: u32 = 0;
    let mut v_r_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_2862_);
    v_r_2864_ = crate::leanh::lean_box_uint32(v_res_2863_);
    return v_r_2864_;
}
pub unsafe fn _init_l_String_Slice_Pos_get_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_String_Slice_Pos_get_x21___closed__1;
    v___x_2868_ = crate::leanh::lean_unsigned_to_nat(29);
    v___x_2869_ = crate::leanh::lean_unsigned_to_nat(1181);
    v___x_2870_ = l_String_Slice_Pos_get_x21___closed__0;
    v___x_2871_ = l_String_fromUTF8_x21___closed__1;
    v___x_2872_ = l_mkPanicMessageWithDecl(
        v___x_2871_,
        v___x_2870_,
        v___x_2869_,
        v___x_2868_,
        v___x_2867_,
    );
    return v___x_2872_;
}
pub unsafe fn l_String_Slice_Pos_get_x21(
    mut v_s_2873_: *mut crate::leanh::LeanObject,
    mut v_pos_2874_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_str_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u8 = 0;
    v_str_2875_ = crate::leanh::lean_ctor_get(v_s_2873_, 0);
    v_startInclusive_2876_ = crate::leanh::lean_ctor_get(v_s_2873_, 1);
    v_endExclusive_2877_ = crate::leanh::lean_ctor_get(v_s_2873_, 2);
    v___x_2878_ = lean_nat_sub(v_endExclusive_2877_, v_startInclusive_2876_);
    v___x_2879_ = lean_nat_dec_eq(v_pos_2874_, v___x_2878_);
    crate::leanh::lean_dec(v___x_2878_);
    if v___x_2879_ == 0 {
        let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2881_: u32 = 0;
        v___x_2880_ = lean_nat_add(v_startInclusive_2876_, v_pos_2874_);
        v___x_2881_ = lean_string_utf8_get_fast(v_str_2875_, v___x_2880_);
        crate::leanh::lean_dec(v___x_2880_);
        return v___x_2881_;
    } else {
        let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2883_: u32 = 0;
        v___x_2882_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_get_x21___closed__2),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_get_x21___closed__2_once),
            _init_l_String_Slice_Pos_get_x21___closed__2,
        );
        v___x_2883_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_2882_);
        return v___x_2883_;
    }
}
pub unsafe fn l_String_Slice_Pos_get_x21___boxed(
    mut v_s_2884_: *mut crate::leanh::LeanObject,
    mut v_pos_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2886_: u32 = 0;
    let mut v_r_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2886_ = l_String_Slice_Pos_get_x21(v_s_2884_, v_pos_2885_);
    crate::leanh::lean_dec(v_pos_2885_);
    crate::leanh::lean_dec_ref(v_s_2884_);
    v_r_2887_ = crate::leanh::lean_box_uint32(v_res_2886_);
    return v_r_2887_;
}
pub unsafe fn l_String_Pos_toSlice___redArg(
    mut v_pos_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2888_);
    return v_pos_2888_;
}
pub unsafe fn l_String_Pos_toSlice___redArg___boxed(
    mut v_pos_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_String_Pos_toSlice___redArg(v_pos_2889_);
    crate::leanh::lean_dec(v_pos_2889_);
    return v_res_2890_;
}
pub unsafe fn l_String_Pos_toSlice(
    mut v_s_2891_: *mut crate::leanh::LeanObject,
    mut v_pos_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2892_);
    return v_pos_2892_;
}
pub unsafe fn l_String_Pos_toSlice___boxed(
    mut v_s_2893_: *mut crate::leanh::LeanObject,
    mut v_pos_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_String_Pos_toSlice(v_s_2893_, v_pos_2894_);
    crate::leanh::lean_dec(v_pos_2894_);
    crate::leanh::lean_dec_ref(v_s_2893_);
    return v_res_2895_;
}
pub unsafe fn l_String_Pos_ofToSlice___redArg(
    mut v_pos_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2896_);
    return v_pos_2896_;
}
pub unsafe fn l_String_Pos_ofToSlice___redArg___boxed(
    mut v_pos_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l_String_Pos_ofToSlice___redArg(v_pos_2897_);
    crate::leanh::lean_dec(v_pos_2897_);
    return v_res_2898_;
}
pub unsafe fn l_String_Pos_ofToSlice(
    mut v_s_2899_: *mut crate::leanh::LeanObject,
    mut v_pos_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2900_);
    return v_pos_2900_;
}
pub unsafe fn l_String_Pos_ofToSlice___boxed(
    mut v_s_2901_: *mut crate::leanh::LeanObject,
    mut v_pos_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2903_ = l_String_Pos_ofToSlice(v_s_2901_, v_pos_2902_);
    crate::leanh::lean_dec(v_pos_2902_);
    crate::leanh::lean_dec_ref(v_s_2901_);
    return v_res_2903_;
}
pub unsafe fn l_String_Pos_get___redArg(
    mut v_s_2904_: *mut crate::leanh::LeanObject,
    mut v_pos_2905_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2906_: u32 = 0;
    v___x_2906_ = lean_string_utf8_get_fast(v_s_2904_, v_pos_2905_);
    return v___x_2906_;
}
pub unsafe fn l_String_Pos_get___redArg___boxed(
    mut v_s_2907_: *mut crate::leanh::LeanObject,
    mut v_pos_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2909_: u32 = 0;
    let mut v_r_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_String_Pos_get___redArg(v_s_2907_, v_pos_2908_);
    crate::leanh::lean_dec(v_pos_2908_);
    crate::leanh::lean_dec_ref(v_s_2907_);
    v_r_2910_ = crate::leanh::lean_box_uint32(v_res_2909_);
    return v_r_2910_;
}
pub unsafe fn l_String_Pos_get(
    mut v_s_2911_: *mut crate::leanh::LeanObject,
    mut v_pos_2912_: *mut crate::leanh::LeanObject,
    mut v_h_2913_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2914_: u32 = 0;
    v___x_2914_ = lean_string_utf8_get_fast(v_s_2911_, v_pos_2912_);
    return v___x_2914_;
}
pub unsafe fn l_String_Pos_get___boxed(
    mut v_s_2915_: *mut crate::leanh::LeanObject,
    mut v_pos_2916_: *mut crate::leanh::LeanObject,
    mut v_h_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2918_: u32 = 0;
    let mut v_r_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2918_ = l_String_Pos_get(v_s_2915_, v_pos_2916_, v_h_2917_);
    crate::leanh::lean_dec(v_pos_2916_);
    crate::leanh::lean_dec_ref(v_s_2915_);
    v_r_2919_ = crate::leanh::lean_box_uint32(v_res_2918_);
    return v_r_2919_;
}
pub unsafe fn l_String_Pos_get_x3f(
    mut v_s_2920_: *mut crate::leanh::LeanObject,
    mut v_pos_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2922_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2923_ = lean_string_utf8_byte_size(v_s_2920_);
    v___x_2924_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2924_, 0, v_s_2920_);
    crate::leanh::lean_ctor_set(v___x_2924_, 1, v___x_2922_);
    crate::leanh::lean_ctor_set(v___x_2924_, 2, v___x_2923_);
    v___x_2925_ = l_String_Slice_Pos_get_x3f(v___x_2924_, v_pos_2921_);
    crate::leanh::lean_dec_ref_known(v___x_2924_, 3);
    return v___x_2925_;
}
pub unsafe fn l_String_Pos_get_x3f___boxed(
    mut v_s_2926_: *mut crate::leanh::LeanObject,
    mut v_pos_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2928_ = l_String_Pos_get_x3f(v_s_2926_, v_pos_2927_);
    crate::leanh::lean_dec(v_pos_2927_);
    return v_res_2928_;
}
pub unsafe fn l_String_Pos_get_x21(
    mut v_s_2929_: *mut crate::leanh::LeanObject,
    mut v_pos_2930_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u32 = 0;
    v___x_2931_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2932_ = lean_string_utf8_byte_size(v_s_2929_);
    v___x_2933_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2933_, 0, v_s_2929_);
    crate::leanh::lean_ctor_set(v___x_2933_, 1, v___x_2931_);
    crate::leanh::lean_ctor_set(v___x_2933_, 2, v___x_2932_);
    v___x_2934_ = l_String_Slice_Pos_get_x21(v___x_2933_, v_pos_2930_);
    crate::leanh::lean_dec_ref_known(v___x_2933_, 3);
    return v___x_2934_;
}
pub unsafe fn l_String_Pos_get_x21___boxed(
    mut v_s_2935_: *mut crate::leanh::LeanObject,
    mut v_pos_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2937_: u32 = 0;
    let mut v_r_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_String_Pos_get_x21(v_s_2935_, v_pos_2936_);
    crate::leanh::lean_dec(v_pos_2936_);
    v_r_2938_ = crate::leanh::lean_box_uint32(v_res_2937_);
    return v_r_2938_;
}
pub unsafe fn l_String_Pos_byte___redArg(
    mut v_s_2939_: *mut crate::leanh::LeanObject,
    mut v_pos_2940_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2941_: u8 = 0;
    v___x_2941_ = lean_string_get_byte_fast(v_s_2939_, v_pos_2940_);
    return v___x_2941_;
}
pub unsafe fn l_String_Pos_byte___redArg___boxed(
    mut v_s_2942_: *mut crate::leanh::LeanObject,
    mut v_pos_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2944_: u8 = 0;
    let mut v_r_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2944_ = l_String_Pos_byte___redArg(v_s_2942_, v_pos_2943_);
    crate::leanh::lean_dec_ref(v_s_2942_);
    v_r_2945_ = crate::leanh::lean_box((v_res_2944_) as usize);
    return v_r_2945_;
}
pub unsafe fn l_String_Pos_byte(
    mut v_s_2946_: *mut crate::leanh::LeanObject,
    mut v_pos_2947_: *mut crate::leanh::LeanObject,
    mut v_h_2948_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2949_: u8 = 0;
    v___x_2949_ = lean_string_get_byte_fast(v_s_2946_, v_pos_2947_);
    return v___x_2949_;
}
pub unsafe fn l_String_Pos_byte___boxed(
    mut v_s_2950_: *mut crate::leanh::LeanObject,
    mut v_pos_2951_: *mut crate::leanh::LeanObject,
    mut v_h_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2953_: u8 = 0;
    let mut v_r_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_String_Pos_byte(v_s_2950_, v_pos_2951_, v_h_2952_);
    crate::leanh::lean_dec_ref(v_s_2950_);
    v_r_2954_ = crate::leanh::lean_box((v_res_2953_) as usize);
    return v_r_2954_;
}
pub unsafe fn l_String_Pos_ofCopy___redArg(
    mut v_pos_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2955_);
    return v_pos_2955_;
}
pub unsafe fn l_String_Pos_ofCopy___redArg___boxed(
    mut v_pos_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2957_ = l_String_Pos_ofCopy___redArg(v_pos_2956_);
    crate::leanh::lean_dec(v_pos_2956_);
    return v_res_2957_;
}
pub unsafe fn l_String_Pos_ofCopy(
    mut v_s_2958_: *mut crate::leanh::LeanObject,
    mut v_pos_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2959_);
    return v_pos_2959_;
}
pub unsafe fn l_String_Pos_ofCopy___boxed(
    mut v_s_2960_: *mut crate::leanh::LeanObject,
    mut v_pos_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_String_Pos_ofCopy(v_s_2960_, v_pos_2961_);
    crate::leanh::lean_dec(v_pos_2961_);
    crate::leanh::lean_dec_ref(v_s_2960_);
    return v_res_2962_;
}
pub unsafe fn l_String_Slice_Pos_copy___redArg(
    mut v_pos_2963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2963_);
    return v_pos_2963_;
}
pub unsafe fn l_String_Slice_Pos_copy___redArg___boxed(
    mut v_pos_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_String_Slice_Pos_copy___redArg(v_pos_2964_);
    crate::leanh::lean_dec(v_pos_2964_);
    return v_res_2965_;
}
pub unsafe fn l_String_Slice_Pos_copy(
    mut v_s_2966_: *mut crate::leanh::LeanObject,
    mut v_pos_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2967_);
    return v_pos_2967_;
}
pub unsafe fn l_String_Slice_Pos_copy___boxed(
    mut v_s_2968_: *mut crate::leanh::LeanObject,
    mut v_pos_2969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2970_ = l_String_Slice_Pos_copy(v_s_2968_, v_pos_2969_);
    crate::leanh::lean_dec(v_pos_2969_);
    crate::leanh::lean_dec_ref(v_s_2968_);
    return v_res_2970_;
}
pub unsafe fn l_String_Slice_Pos_toCopy___redArg(
    mut v_pos_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2971_);
    return v_pos_2971_;
}
pub unsafe fn l_String_Slice_Pos_toCopy___redArg___boxed(
    mut v_pos_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2973_ = l_String_Slice_Pos_toCopy___redArg(v_pos_2972_);
    crate::leanh::lean_dec(v_pos_2972_);
    return v_res_2973_;
}
pub unsafe fn l_String_Slice_Pos_toCopy(
    mut v_s_2974_: *mut crate::leanh::LeanObject,
    mut v_pos_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_2975_);
    return v_pos_2975_;
}
pub unsafe fn l_String_Slice_Pos_toCopy___boxed(
    mut v_s_2976_: *mut crate::leanh::LeanObject,
    mut v_pos_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_String_Slice_Pos_toCopy(v_s_2976_, v_pos_2977_);
    crate::leanh::lean_dec(v_pos_2977_);
    crate::leanh::lean_dec_ref(v_s_2976_);
    return v_res_2978_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceFrom___redArg(
    mut v_p_u2080_2979_: *mut crate::leanh::LeanObject,
    mut v_pos_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2981_ = lean_nat_add(v_p_u2080_2979_, v_pos_2980_);
    return v___x_2981_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceFrom___redArg___boxed(
    mut v_p_u2080_2982_: *mut crate::leanh::LeanObject,
    mut v_pos_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_2982_, v_pos_2983_);
    crate::leanh::lean_dec(v_pos_2983_);
    crate::leanh::lean_dec(v_p_u2080_2982_);
    return v_res_2984_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceFrom(
    mut v_s_2985_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_2986_: *mut crate::leanh::LeanObject,
    mut v_pos_2987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = lean_nat_add(v_p_u2080_2986_, v_pos_2987_);
    return v___x_2988_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceFrom___boxed(
    mut v_s_2989_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_2990_: *mut crate::leanh::LeanObject,
    mut v_pos_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_String_Slice_Pos_ofSliceFrom(v_s_2989_, v_p_u2080_2990_, v_pos_2991_);
    crate::leanh::lean_dec(v_pos_2991_);
    crate::leanh::lean_dec(v_p_u2080_2990_);
    crate::leanh::lean_dec_ref(v_s_2989_);
    return v_res_2992_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceStart___redArg(
    mut v_p_u2080_2993_: *mut crate::leanh::LeanObject,
    mut v_pos_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = lean_nat_add(v_p_u2080_2993_, v_pos_2994_);
    return v___x_2995_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceStart___redArg___boxed(
    mut v_p_u2080_2996_: *mut crate::leanh::LeanObject,
    mut v_pos_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2998_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_2996_, v_pos_2997_);
    crate::leanh::lean_dec(v_pos_2997_);
    crate::leanh::lean_dec(v_p_u2080_2996_);
    return v_res_2998_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceStart(
    mut v_s_2999_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3000_: *mut crate::leanh::LeanObject,
    mut v_pos_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = lean_nat_add(v_p_u2080_3000_, v_pos_3001_);
    return v___x_3002_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceStart___boxed(
    mut v_s_3003_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3004_: *mut crate::leanh::LeanObject,
    mut v_pos_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_String_Slice_Pos_ofReplaceStart(v_s_3003_, v_p_u2080_3004_, v_pos_3005_);
    crate::leanh::lean_dec(v_pos_3005_);
    crate::leanh::lean_dec(v_p_u2080_3004_);
    crate::leanh::lean_dec_ref(v_s_3003_);
    return v_res_3006_;
}
pub unsafe fn l_String_Slice_Pos_sliceFrom___redArg(
    mut v_p_u2080_3007_: *mut crate::leanh::LeanObject,
    mut v_pos_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3009_ = lean_nat_sub(v_pos_3008_, v_p_u2080_3007_);
    return v___x_3009_;
}
pub unsafe fn l_String_Slice_Pos_sliceFrom___redArg___boxed(
    mut v_p_u2080_3010_: *mut crate::leanh::LeanObject,
    mut v_pos_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_3010_, v_pos_3011_);
    crate::leanh::lean_dec(v_pos_3011_);
    crate::leanh::lean_dec(v_p_u2080_3010_);
    return v_res_3012_;
}
pub unsafe fn l_String_Slice_Pos_sliceFrom(
    mut v_s_3013_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3014_: *mut crate::leanh::LeanObject,
    mut v_pos_3015_: *mut crate::leanh::LeanObject,
    mut v_h_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = lean_nat_sub(v_pos_3015_, v_p_u2080_3014_);
    return v___x_3017_;
}
pub unsafe fn l_String_Slice_Pos_sliceFrom___boxed(
    mut v_s_3018_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3019_: *mut crate::leanh::LeanObject,
    mut v_pos_3020_: *mut crate::leanh::LeanObject,
    mut v_h_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3022_ = l_String_Slice_Pos_sliceFrom(v_s_3018_, v_p_u2080_3019_, v_pos_3020_, v_h_3021_);
    crate::leanh::lean_dec(v_pos_3020_);
    crate::leanh::lean_dec(v_p_u2080_3019_);
    crate::leanh::lean_dec_ref(v_s_3018_);
    return v_res_3022_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceStart___redArg(
    mut v_p_u2080_3023_: *mut crate::leanh::LeanObject,
    mut v_pos_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = lean_nat_sub(v_pos_3024_, v_p_u2080_3023_);
    return v___x_3025_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceStart___redArg___boxed(
    mut v_p_u2080_3026_: *mut crate::leanh::LeanObject,
    mut v_pos_3027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3028_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_3026_, v_pos_3027_);
    crate::leanh::lean_dec(v_pos_3027_);
    crate::leanh::lean_dec(v_p_u2080_3026_);
    return v_res_3028_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceStart(
    mut v_s_3029_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3030_: *mut crate::leanh::LeanObject,
    mut v_pos_3031_: *mut crate::leanh::LeanObject,
    mut v_h_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ = lean_nat_sub(v_pos_3031_, v_p_u2080_3030_);
    return v___x_3033_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceStart___boxed(
    mut v_s_3034_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3035_: *mut crate::leanh::LeanObject,
    mut v_pos_3036_: *mut crate::leanh::LeanObject,
    mut v_h_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3038_ =
        l_String_Slice_Pos_toReplaceStart(v_s_3034_, v_p_u2080_3035_, v_pos_3036_, v_h_3037_);
    crate::leanh::lean_dec(v_pos_3036_);
    crate::leanh::lean_dec(v_p_u2080_3035_);
    crate::leanh::lean_dec_ref(v_s_3034_);
    return v_res_3038_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceTo___redArg(
    mut v_pos_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3039_);
    return v_pos_3039_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceTo___redArg___boxed(
    mut v_pos_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_3040_);
    crate::leanh::lean_dec(v_pos_3040_);
    return v_res_3041_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceTo(
    mut v_s_3042_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3043_: *mut crate::leanh::LeanObject,
    mut v_pos_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3044_);
    return v_pos_3044_;
}
pub unsafe fn l_String_Slice_Pos_ofSliceTo___boxed(
    mut v_s_3045_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3046_: *mut crate::leanh::LeanObject,
    mut v_pos_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_String_Slice_Pos_ofSliceTo(v_s_3045_, v_p_u2080_3046_, v_pos_3047_);
    crate::leanh::lean_dec(v_pos_3047_);
    crate::leanh::lean_dec(v_p_u2080_3046_);
    crate::leanh::lean_dec_ref(v_s_3045_);
    return v_res_3048_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceEnd___redArg(
    mut v_pos_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3049_);
    return v_pos_3049_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(
    mut v_pos_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_3050_);
    crate::leanh::lean_dec(v_pos_3050_);
    return v_res_3051_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceEnd(
    mut v_s_3052_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3053_: *mut crate::leanh::LeanObject,
    mut v_pos_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3054_);
    return v_pos_3054_;
}
pub unsafe fn l_String_Slice_Pos_ofReplaceEnd___boxed(
    mut v_s_3055_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3056_: *mut crate::leanh::LeanObject,
    mut v_pos_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_String_Slice_Pos_ofReplaceEnd(v_s_3055_, v_p_u2080_3056_, v_pos_3057_);
    crate::leanh::lean_dec(v_pos_3057_);
    crate::leanh::lean_dec(v_p_u2080_3056_);
    crate::leanh::lean_dec_ref(v_s_3055_);
    return v_res_3058_;
}
pub unsafe fn l_String_Slice_Pos_sliceTo___redArg(
    mut v_pos_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3059_);
    return v_pos_3059_;
}
pub unsafe fn l_String_Slice_Pos_sliceTo___redArg___boxed(
    mut v_pos_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_3060_);
    crate::leanh::lean_dec(v_pos_3060_);
    return v_res_3061_;
}
pub unsafe fn l_String_Slice_Pos_sliceTo(
    mut v_s_3062_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3063_: *mut crate::leanh::LeanObject,
    mut v_pos_3064_: *mut crate::leanh::LeanObject,
    mut v_h_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3064_);
    return v_pos_3064_;
}
pub unsafe fn l_String_Slice_Pos_sliceTo___boxed(
    mut v_s_3066_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3067_: *mut crate::leanh::LeanObject,
    mut v_pos_3068_: *mut crate::leanh::LeanObject,
    mut v_h_3069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3070_ = l_String_Slice_Pos_sliceTo(v_s_3066_, v_p_u2080_3067_, v_pos_3068_, v_h_3069_);
    crate::leanh::lean_dec(v_pos_3068_);
    crate::leanh::lean_dec(v_p_u2080_3067_);
    crate::leanh::lean_dec_ref(v_s_3066_);
    return v_res_3070_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceEnd___redArg(
    mut v_pos_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3071_);
    return v_pos_3071_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceEnd___redArg___boxed(
    mut v_pos_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_3072_);
    crate::leanh::lean_dec(v_pos_3072_);
    return v_res_3073_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceEnd(
    mut v_s_3074_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3075_: *mut crate::leanh::LeanObject,
    mut v_pos_3076_: *mut crate::leanh::LeanObject,
    mut v_h_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3076_);
    return v_pos_3076_;
}
pub unsafe fn l_String_Slice_Pos_toReplaceEnd___boxed(
    mut v_s_3078_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3079_: *mut crate::leanh::LeanObject,
    mut v_pos_3080_: *mut crate::leanh::LeanObject,
    mut v_h_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3082_ =
        l_String_Slice_Pos_toReplaceEnd(v_s_3078_, v_p_u2080_3079_, v_pos_3080_, v_h_3081_);
    crate::leanh::lean_dec(v_pos_3080_);
    crate::leanh::lean_dec(v_p_u2080_3079_);
    crate::leanh::lean_dec_ref(v_s_3078_);
    return v_res_3082_;
}
pub unsafe fn l_String_Slice_Pos_next___redArg(
    mut v_s_3083_: *mut crate::leanh::LeanObject,
    mut v_pos_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: u8 = 0;
    v_str_3085_ = crate::leanh::lean_ctor_get(v_s_3083_, 0);
    v_startInclusive_3086_ = crate::leanh::lean_ctor_get(v_s_3083_, 1);
    v___x_3087_ = lean_nat_add(v_startInclusive_3086_, v_pos_3084_);
    v___x_3088_ = lean_string_get_byte_fast(v_str_3085_, v___x_3087_);
    v___x_3089_ = 128;
    v___x_3090_ = lean_uint8_land(v___x_3088_, v___x_3089_);
    v___x_3091_ = 0;
    v___x_3092_ = lean_uint8_dec_eq(v___x_3090_, v___x_3091_);
    if v___x_3092_ == 0 {
        let mut v___x_3093_: u8 = 0;
        let mut v___x_3094_: u8 = 0;
        let mut v___x_3095_: u8 = 0;
        let mut v___x_3096_: u8 = 0;
        v___x_3093_ = 224;
        v___x_3094_ = lean_uint8_land(v___x_3088_, v___x_3093_);
        v___x_3095_ = 192;
        v___x_3096_ = lean_uint8_dec_eq(v___x_3094_, v___x_3095_);
        if v___x_3096_ == 0 {
            let mut v___x_3097_: u8 = 0;
            let mut v___x_3098_: u8 = 0;
            let mut v___x_3099_: u8 = 0;
            v___x_3097_ = 240;
            v___x_3098_ = lean_uint8_land(v___x_3088_, v___x_3097_);
            v___x_3099_ = lean_uint8_dec_eq(v___x_3098_, v___x_3093_);
            if v___x_3099_ == 0 {
                let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3100_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3101_ = lean_nat_add(v_pos_3084_, v___x_3100_);
                return v___x_3101_;
            } else {
                let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3102_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3103_ = lean_nat_add(v_pos_3084_, v___x_3102_);
                return v___x_3103_;
            }
        } else {
            let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3104_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_3105_ = lean_nat_add(v_pos_3084_, v___x_3104_);
            return v___x_3105_;
        }
    } else {
        let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3106_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3107_ = lean_nat_add(v_pos_3084_, v___x_3106_);
        return v___x_3107_;
    }
}
pub unsafe fn l_String_Slice_Pos_next___redArg___boxed(
    mut v_s_3108_: *mut crate::leanh::LeanObject,
    mut v_pos_3109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3110_ = l_String_Slice_Pos_next___redArg(v_s_3108_, v_pos_3109_);
    crate::leanh::lean_dec(v_pos_3109_);
    crate::leanh::lean_dec_ref(v_s_3108_);
    return v_res_3110_;
}
pub unsafe fn l_String_Slice_Pos_next(
    mut v_s_3111_: *mut crate::leanh::LeanObject,
    mut v_pos_3112_: *mut crate::leanh::LeanObject,
    mut v_h_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_String_Slice_Pos_next___redArg(v_s_3111_, v_pos_3112_);
    return v___x_3114_;
}
pub unsafe fn l_String_Slice_Pos_next___boxed(
    mut v_s_3115_: *mut crate::leanh::LeanObject,
    mut v_pos_3116_: *mut crate::leanh::LeanObject,
    mut v_h_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3118_ = l_String_Slice_Pos_next(v_s_3115_, v_pos_3116_, v_h_3117_);
    crate::leanh::lean_dec(v_pos_3116_);
    crate::leanh::lean_dec_ref(v_s_3115_);
    return v_res_3118_;
}
pub unsafe fn l_String_Slice_Pos_next_x3f(
    mut v_s_3119_: *mut crate::leanh::LeanObject,
    mut v_pos_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    v_startInclusive_3121_ = crate::leanh::lean_ctor_get(v_s_3119_, 1);
    v_endExclusive_3122_ = crate::leanh::lean_ctor_get(v_s_3119_, 2);
    v___x_3123_ = lean_nat_sub(v_endExclusive_3122_, v_startInclusive_3121_);
    v___x_3124_ = lean_nat_dec_eq(v_pos_3120_, v___x_3123_);
    crate::leanh::lean_dec(v___x_3123_);
    if v___x_3124_ == 0 {
        let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3125_ = l_String_Slice_Pos_next___redArg(v_s_3119_, v_pos_3120_);
        v___x_3126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3125_);
        return v___x_3126_;
    } else {
        let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3127_ = crate::leanh::lean_box(0);
        return v___x_3127_;
    }
}
pub unsafe fn l_String_Slice_Pos_next_x3f___boxed(
    mut v_s_3128_: *mut crate::leanh::LeanObject,
    mut v_pos_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3130_ = l_String_Slice_Pos_next_x3f(v_s_3128_, v_pos_3129_);
    crate::leanh::lean_dec(v_pos_3129_);
    crate::leanh::lean_dec_ref(v_s_3128_);
    return v_res_3130_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(
    mut v_msg_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3133_ = lean_panic_fn_borrowed(v___x_3132_, v_msg_3131_);
    return v___x_3133_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_next_x21_spec__0(
    mut v_s_3134_: *mut crate::leanh::LeanObject,
    mut v_msg_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3136_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_3135_);
    return v___x_3136_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(
    mut v_s_3137_: *mut crate::leanh::LeanObject,
    mut v_msg_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_3137_, v_msg_3138_);
    crate::leanh::lean_dec_ref(v_s_3137_);
    return v_res_3139_;
}
pub unsafe fn _init_l_String_Slice_Pos_next_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_String_Slice_Pos_next_x21___closed__1;
    v___x_3143_ = crate::leanh::lean_unsigned_to_nat(29);
    v___x_3144_ = crate::leanh::lean_unsigned_to_nat(1573);
    v___x_3145_ = l_String_Slice_Pos_next_x21___closed__0;
    v___x_3146_ = l_String_fromUTF8_x21___closed__1;
    v___x_3147_ = l_mkPanicMessageWithDecl(
        v___x_3146_,
        v___x_3145_,
        v___x_3144_,
        v___x_3143_,
        v___x_3142_,
    );
    return v___x_3147_;
}
pub unsafe fn l_String_Slice_Pos_next_x21(
    mut v_s_3148_: *mut crate::leanh::LeanObject,
    mut v_pos_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: u8 = 0;
    v_startInclusive_3150_ = crate::leanh::lean_ctor_get(v_s_3148_, 1);
    v_endExclusive_3151_ = crate::leanh::lean_ctor_get(v_s_3148_, 2);
    v___x_3152_ = lean_nat_sub(v_endExclusive_3151_, v_startInclusive_3150_);
    v___x_3153_ = lean_nat_dec_eq(v_pos_3149_, v___x_3152_);
    crate::leanh::lean_dec(v___x_3152_);
    if v___x_3153_ == 0 {
        let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3154_ = l_String_Slice_Pos_next___redArg(v_s_3148_, v_pos_3149_);
        return v___x_3154_;
    } else {
        let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3155_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_next_x21___closed__2),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_next_x21___closed__2_once),
            _init_l_String_Slice_Pos_next_x21___closed__2,
        );
        v___x_3156_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_3155_);
        return v___x_3156_;
    }
}
pub unsafe fn l_String_Slice_Pos_next_x21___boxed(
    mut v_s_3157_: *mut crate::leanh::LeanObject,
    mut v_pos_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_String_Slice_Pos_next_x21(v_s_3157_, v_pos_3158_);
    crate::leanh::lean_dec(v_pos_3158_);
    crate::leanh::lean_dec_ref(v_s_3157_);
    return v_res_3159_;
}
pub unsafe fn l_String_Slice_Pos_prevAux_go___redArg(
    mut v_s_3160_: *mut crate::leanh::LeanObject,
    mut v_off_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: u8 = 0;
    let mut v_zero_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3168_: u8 = 0;
    let mut v_one_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3162_ = crate::leanh::lean_ctor_get(v_s_3160_, 0);
                v_startInclusive_3163_ = crate::leanh::lean_ctor_get(v_s_3160_, 1);
                v___x_3164_ = lean_nat_add(v_startInclusive_3163_, v_off_3161_);
                v___x_3165_ = lean_string_get_byte_fast(v_str_3162_, v___x_3164_);
                v___x_3166_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_3165_);
                if v___x_3166_ == 0 {
                    v_zero_3167_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_3168_ = lean_nat_dec_eq(v_off_3161_, v_zero_3167_);
                    v_one_3169_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3170_ = lean_nat_sub(v_off_3161_, v_one_3169_);
                    crate::leanh::lean_dec(v_off_3161_);
                    v_off_3161_ = v_n_3170_;
                    state = 0;
                    continue;
                } else {
                    return v_off_3161_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_prevAux_go___redArg___boxed(
    mut v_s_3172_: *mut crate::leanh::LeanObject,
    mut v_off_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_3172_, v_off_3173_);
    crate::leanh::lean_dec_ref(v_s_3172_);
    return v_res_3174_;
}
pub unsafe fn l_String_Slice_Pos_prevAux_go(
    mut v_s_3175_: *mut crate::leanh::LeanObject,
    mut v_off_3176_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3178_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_3175_, v_off_3176_);
    return v___x_3178_;
}
pub unsafe fn l_String_Slice_Pos_prevAux_go___boxed(
    mut v_s_3179_: *mut crate::leanh::LeanObject,
    mut v_off_3180_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3182_ = l_String_Slice_Pos_prevAux_go(v_s_3179_, v_off_3180_, v_h_u2081_3181_);
    crate::leanh::lean_dec_ref(v_s_3179_);
    return v_res_3182_;
}
pub unsafe fn l_String_Slice_Pos_prevAux___redArg(
    mut v_s_3183_: *mut crate::leanh::LeanObject,
    mut v_pos_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3185_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3186_ = lean_nat_sub(v_pos_3184_, v___x_3185_);
    v___x_3187_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_3183_, v___x_3186_);
    return v___x_3187_;
}
pub unsafe fn l_String_Slice_Pos_prevAux___redArg___boxed(
    mut v_s_3188_: *mut crate::leanh::LeanObject,
    mut v_pos_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l_String_Slice_Pos_prevAux___redArg(v_s_3188_, v_pos_3189_);
    crate::leanh::lean_dec(v_pos_3189_);
    crate::leanh::lean_dec_ref(v_s_3188_);
    return v_res_3190_;
}
pub unsafe fn l_String_Slice_Pos_prevAux(
    mut v_s_3191_: *mut crate::leanh::LeanObject,
    mut v_pos_3192_: *mut crate::leanh::LeanObject,
    mut v_h_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3195_ = lean_nat_sub(v_pos_3192_, v___x_3194_);
    v___x_3196_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_3191_, v___x_3195_);
    return v___x_3196_;
}
pub unsafe fn l_String_Slice_Pos_prevAux___boxed(
    mut v_s_3197_: *mut crate::leanh::LeanObject,
    mut v_pos_3198_: *mut crate::leanh::LeanObject,
    mut v_h_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3200_ = l_String_Slice_Pos_prevAux(v_s_3197_, v_pos_3198_, v_h_3199_);
    crate::leanh::lean_dec(v_pos_3198_);
    crate::leanh::lean_dec_ref(v_s_3197_);
    return v_res_3200_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(
    mut v_off_3201_: *mut crate::leanh::LeanObject,
    mut v_h__1_3202_: *mut crate::leanh::LeanObject,
    mut v_h__2_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3205_: u8 = 0;
    v_zero_3204_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3205_ = lean_nat_dec_eq(v_off_3201_, v_zero_3204_);
    if v_isZero_3205_ == 1 {
        let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3203_);
        v___x_3206_ = crate::leanh::lean_apply_3(
            v_h__1_3202_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_3206_;
    } else {
        let mut v_one_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3202_);
        v_one_3207_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3208_ = lean_nat_sub(v_off_3201_, v_one_3207_);
        v___x_3209_ = crate::leanh::lean_apply_4(
            v_h__2_3203_,
            v_n_3208_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_3209_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(
    mut v_off_3210_: *mut crate::leanh::LeanObject,
    mut v_h__1_3211_: *mut crate::leanh::LeanObject,
    mut v_h__2_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3213_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_3210_, v_h__1_3211_, v_h__2_3212_);
    crate::leanh::lean_dec(v_off_3210_);
    return v_res_3213_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(
    mut v_s_3214_: *mut crate::leanh::LeanObject,
    mut v_motive_3215_: *mut crate::leanh::LeanObject,
    mut v_off_3216_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3217_: *mut crate::leanh::LeanObject,
    mut v_hbyte_3218_: *mut crate::leanh::LeanObject,
    mut v_this_3219_: *mut crate::leanh::LeanObject,
    mut v_h__1_3220_: *mut crate::leanh::LeanObject,
    mut v_h__2_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3223_: u8 = 0;
    v_zero_3222_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3223_ = lean_nat_dec_eq(v_off_3216_, v_zero_3222_);
    if v_isZero_3223_ == 1 {
        let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3221_);
        v___x_3224_ = crate::leanh::lean_apply_3(
            v_h__1_3220_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_3224_;
    } else {
        let mut v_one_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3220_);
        v_one_3225_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3226_ = lean_nat_sub(v_off_3216_, v_one_3225_);
        v___x_3227_ = crate::leanh::lean_apply_4(
            v_h__2_3221_,
            v_n_3226_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_3227_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(
    mut v_s_3228_: *mut crate::leanh::LeanObject,
    mut v_motive_3229_: *mut crate::leanh::LeanObject,
    mut v_off_3230_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3231_: *mut crate::leanh::LeanObject,
    mut v_hbyte_3232_: *mut crate::leanh::LeanObject,
    mut v_this_3233_: *mut crate::leanh::LeanObject,
    mut v_h__1_3234_: *mut crate::leanh::LeanObject,
    mut v_h__2_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ =
        l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(
            v_s_3228_,
            v_motive_3229_,
            v_off_3230_,
            v_h_u2081_3231_,
            v_hbyte_3232_,
            v_this_3233_,
            v_h__1_3234_,
            v_h__2_3235_,
        );
    crate::leanh::lean_dec(v_off_3230_);
    crate::leanh::lean_dec_ref(v_s_3228_);
    return v_res_3236_;
}
pub unsafe fn l_String_Slice_pos___redArg(
    mut v_off_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_3237_);
    return v_off_3237_;
}
pub unsafe fn l_String_Slice_pos___redArg___boxed(
    mut v_off_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3239_ = l_String_Slice_pos___redArg(v_off_3238_);
    crate::leanh::lean_dec(v_off_3238_);
    return v_res_3239_;
}
pub unsafe fn l_String_Slice_pos(
    mut v_s_3240_: *mut crate::leanh::LeanObject,
    mut v_off_3241_: *mut crate::leanh::LeanObject,
    mut v_h_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_3241_);
    return v_off_3241_;
}
pub unsafe fn l_String_Slice_pos___boxed(
    mut v_s_3243_: *mut crate::leanh::LeanObject,
    mut v_off_3244_: *mut crate::leanh::LeanObject,
    mut v_h_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3246_ = l_String_Slice_pos(v_s_3243_, v_off_3244_, v_h_3245_);
    crate::leanh::lean_dec(v_off_3244_);
    crate::leanh::lean_dec_ref(v_s_3243_);
    return v_res_3246_;
}
pub unsafe fn l_String_Slice_pos_x3f(
    mut v_s_3247_: *mut crate::leanh::LeanObject,
    mut v_off_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3249_: u8 = 0;
    v___x_3249_ = l_String_Pos_Raw_isValidForSlice(v_s_3247_, v_off_3248_);
    if v___x_3249_ == 0 {
        let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_off_3248_);
        v___x_3250_ = crate::leanh::lean_box(0);
        return v___x_3250_;
    } else {
        let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3251_, 0, v_off_3248_);
        return v___x_3251_;
    }
}
pub unsafe fn l_String_Slice_pos_x3f___boxed(
    mut v_s_3252_: *mut crate::leanh::LeanObject,
    mut v_off_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3254_ = l_String_Slice_pos_x3f(v_s_3252_, v_off_3253_);
    crate::leanh::lean_dec_ref(v_s_3252_);
    return v_res_3254_;
}
pub unsafe fn _init_l_String_Slice_pos_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = l_String_Slice_pos_x21___closed__1;
    v___x_3258_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3259_ = crate::leanh::lean_unsigned_to_nat(1661);
    v___x_3260_ = l_String_Slice_pos_x21___closed__0;
    v___x_3261_ = l_String_fromUTF8_x21___closed__1;
    v___x_3262_ = l_mkPanicMessageWithDecl(
        v___x_3261_,
        v___x_3260_,
        v___x_3259_,
        v___x_3258_,
        v___x_3257_,
    );
    return v___x_3262_;
}
pub unsafe fn l_String_Slice_pos_x21(
    mut v_s_3263_: *mut crate::leanh::LeanObject,
    mut v_off_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3265_: u8 = 0;
    v___x_3265_ = l_String_Pos_Raw_isValidForSlice(v_s_3263_, v_off_3264_);
    if v___x_3265_ == 0 {
        let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3266_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_pos_x21___closed__2),
            core::ptr::addr_of_mut!(l_String_Slice_pos_x21___closed__2_once),
            _init_l_String_Slice_pos_x21___closed__2,
        );
        v___x_3267_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_3266_);
        return v___x_3267_;
    } else {
        crate::leanh::lean_inc(v_off_3264_);
        return v_off_3264_;
    }
}
pub unsafe fn l_String_Slice_pos_x21___boxed(
    mut v_s_3268_: *mut crate::leanh::LeanObject,
    mut v_off_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_String_Slice_pos_x21(v_s_3268_, v_off_3269_);
    crate::leanh::lean_dec(v_off_3269_);
    crate::leanh::lean_dec_ref(v_s_3268_);
    return v_res_3270_;
}
pub unsafe fn l_String_Pos_next___boxed(
    mut v_s_3274_: *mut crate::leanh::LeanObject,
    mut v_pos_3275_: *mut crate::leanh::LeanObject,
    mut v_h_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = lean_string_utf8_next_fast(v_s_3274_, v_pos_3275_);
    crate::leanh::lean_dec(v_pos_3275_);
    crate::leanh::lean_dec_ref(v_s_3274_);
    return v_res_3277_;
}
pub unsafe fn l_String_Pos_next_x3f(
    mut v_s_3278_: *mut crate::leanh::LeanObject,
    mut v_pos_3279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3280_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3281_ = lean_string_utf8_byte_size(v_s_3278_);
                v___x_3282_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3282_, 0, v_s_3278_);
                crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3280_);
                crate::leanh::lean_ctor_set(v___x_3282_, 2, v___x_3281_);
                v___x_3283_ = l_String_Slice_Pos_next_x3f(v___x_3282_, v_pos_3279_);
                crate::leanh::lean_dec_ref_known(v___x_3282_, 3);
                if crate::leanh::lean_obj_tag(v___x_3283_) == 0 {
                    v___x_3284_ = crate::leanh::lean_box(0);
                    return v___x_3284_;
                } else {
                    v_val_3285_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                    v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3292_ == 0 {
                        v___x_3287_ = v___x_3283_;
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3285_);
                        crate::leanh::lean_dec(v___x_3283_);
                        v___x_3287_ = crate::leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3288_ == 0 {
                    v___x_3290_ = v___x_3287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_val_3285_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_next_x3f___boxed(
    mut v_s_3293_: *mut crate::leanh::LeanObject,
    mut v_pos_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_String_Pos_next_x3f(v_s_3293_, v_pos_3294_);
    crate::leanh::lean_dec(v_pos_3294_);
    return v_res_3295_;
}
pub unsafe fn l_String_Pos_next_x21(
    mut v_s_3296_: *mut crate::leanh::LeanObject,
    mut v_pos_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3299_ = lean_string_utf8_byte_size(v_s_3296_);
    v___x_3300_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3300_, 0, v_s_3296_);
    crate::leanh::lean_ctor_set(v___x_3300_, 1, v___x_3298_);
    crate::leanh::lean_ctor_set(v___x_3300_, 2, v___x_3299_);
    v___x_3301_ = l_String_Slice_Pos_next_x21(v___x_3300_, v_pos_3297_);
    crate::leanh::lean_dec_ref_known(v___x_3300_, 3);
    return v___x_3301_;
}
pub unsafe fn l_String_Pos_next_x21___boxed(
    mut v_s_3302_: *mut crate::leanh::LeanObject,
    mut v_pos_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_String_Pos_next_x21(v_s_3302_, v_pos_3303_);
    crate::leanh::lean_dec(v_pos_3303_);
    return v_res_3304_;
}
pub unsafe fn l_String_pos___redArg(
    mut v_off_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_3305_);
    return v_off_3305_;
}
pub unsafe fn l_String_pos___redArg___boxed(
    mut v_off_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_String_pos___redArg(v_off_3306_);
    crate::leanh::lean_dec(v_off_3306_);
    return v_res_3307_;
}
pub unsafe fn l_String_pos(
    mut v_s_3308_: *mut crate::leanh::LeanObject,
    mut v_off_3309_: *mut crate::leanh::LeanObject,
    mut v_h_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_3309_);
    return v_off_3309_;
}
pub unsafe fn l_String_pos___boxed(
    mut v_s_3311_: *mut crate::leanh::LeanObject,
    mut v_off_3312_: *mut crate::leanh::LeanObject,
    mut v_h_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_String_pos(v_s_3311_, v_off_3312_, v_h_3313_);
    crate::leanh::lean_dec(v_off_3312_);
    crate::leanh::lean_dec_ref(v_s_3311_);
    return v_res_3314_;
}
pub unsafe fn l_String_pos_x3f(
    mut v_s_3315_: *mut crate::leanh::LeanObject,
    mut v_off_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3317_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3318_ = lean_string_utf8_byte_size(v_s_3315_);
                v___x_3319_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3319_, 0, v_s_3315_);
                crate::leanh::lean_ctor_set(v___x_3319_, 1, v___x_3317_);
                crate::leanh::lean_ctor_set(v___x_3319_, 2, v___x_3318_);
                v___x_3320_ = l_String_Slice_pos_x3f(v___x_3319_, v_off_3316_);
                crate::leanh::lean_dec_ref_known(v___x_3319_, 3);
                if crate::leanh::lean_obj_tag(v___x_3320_) == 0 {
                    v___x_3321_ = crate::leanh::lean_box(0);
                    return v___x_3321_;
                } else {
                    v_val_3322_ = crate::leanh::lean_ctor_get(v___x_3320_, 0);
                    v_isSharedCheck_3329_ = (!crate::leanh::lean_is_exclusive(v___x_3320_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3324_ = v___x_3320_;
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3322_);
                        crate::leanh::lean_dec(v___x_3320_);
                        v___x_3324_ = crate::leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3325_ == 0 {
                    v___x_3327_ = v___x_3324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_val_3322_);
                    v___x_3327_ = v_reuseFailAlloc_3328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_pos_x21(
    mut v_s_3330_: *mut crate::leanh::LeanObject,
    mut v_off_3331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3332_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3333_ = lean_string_utf8_byte_size(v_s_3330_);
    v___x_3334_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3334_, 0, v_s_3330_);
    crate::leanh::lean_ctor_set(v___x_3334_, 1, v___x_3332_);
    crate::leanh::lean_ctor_set(v___x_3334_, 2, v___x_3333_);
    v___x_3335_ = l_String_Slice_pos_x21(v___x_3334_, v_off_3331_);
    crate::leanh::lean_dec_ref_known(v___x_3334_, 3);
    return v___x_3335_;
}
pub unsafe fn l_String_pos_x21___boxed(
    mut v_s_3336_: *mut crate::leanh::LeanObject,
    mut v_off_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_String_pos_x21(v_s_3336_, v_off_3337_);
    crate::leanh::lean_dec(v_off_3337_);
    return v_res_3338_;
}
pub unsafe fn l_String_Slice_Pos_cast___redArg(
    mut v_pos_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3339_);
    return v_pos_3339_;
}
pub unsafe fn l_String_Slice_Pos_cast___redArg___boxed(
    mut v_pos_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ = l_String_Slice_Pos_cast___redArg(v_pos_3340_);
    crate::leanh::lean_dec(v_pos_3340_);
    return v_res_3341_;
}
pub unsafe fn l_String_Slice_Pos_cast(
    mut v_s_3342_: *mut crate::leanh::LeanObject,
    mut v_t_3343_: *mut crate::leanh::LeanObject,
    mut v_pos_3344_: *mut crate::leanh::LeanObject,
    mut v_h_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3344_);
    return v_pos_3344_;
}
pub unsafe fn l_String_Slice_Pos_cast___boxed(
    mut v_s_3346_: *mut crate::leanh::LeanObject,
    mut v_t_3347_: *mut crate::leanh::LeanObject,
    mut v_pos_3348_: *mut crate::leanh::LeanObject,
    mut v_h_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_String_Slice_Pos_cast(v_s_3346_, v_t_3347_, v_pos_3348_, v_h_3349_);
    crate::leanh::lean_dec(v_pos_3348_);
    crate::leanh::lean_dec_ref(v_t_3347_);
    crate::leanh::lean_dec_ref(v_s_3346_);
    return v_res_3350_;
}
pub unsafe fn l_String_Pos_cast___redArg(
    mut v_pos_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3351_);
    return v_pos_3351_;
}
pub unsafe fn l_String_Pos_cast___redArg___boxed(
    mut v_pos_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_String_Pos_cast___redArg(v_pos_3352_);
    crate::leanh::lean_dec(v_pos_3352_);
    return v_res_3353_;
}
pub unsafe fn l_String_Pos_cast(
    mut v_s_3354_: *mut crate::leanh::LeanObject,
    mut v_t_3355_: *mut crate::leanh::LeanObject,
    mut v_pos_3356_: *mut crate::leanh::LeanObject,
    mut v_h_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3356_);
    return v_pos_3356_;
}
pub unsafe fn l_String_Pos_cast___boxed(
    mut v_s_3358_: *mut crate::leanh::LeanObject,
    mut v_t_3359_: *mut crate::leanh::LeanObject,
    mut v_pos_3360_: *mut crate::leanh::LeanObject,
    mut v_h_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3362_ = l_String_Pos_cast(v_s_3358_, v_t_3359_, v_pos_3360_, v_h_3361_);
    crate::leanh::lean_dec(v_pos_3360_);
    crate::leanh::lean_dec_ref(v_t_3359_);
    crate::leanh::lean_dec_ref(v_s_3358_);
    return v_res_3362_;
}
pub unsafe fn l_String_Pos_Raw_utf8GetAux(
    mut v_x_3363_: *mut crate::leanh::LeanObject,
    mut v_x_3364_: *mut crate::leanh::LeanObject,
    mut v_x_3365_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_3366_: u32 = 0;
    let mut v_head_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: u32 = 0;
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3363_) == 0 {
                    crate::leanh::lean_dec(v_x_3364_);
                    v___x_3366_ = 65;
                    return v___x_3366_;
                } else {
                    v_head_3367_ = crate::leanh::lean_ctor_get(v_x_3363_, 0);
                    v_tail_3368_ = crate::leanh::lean_ctor_get(v_x_3363_, 1);
                    v___x_3369_ = lean_nat_dec_eq(v_x_3364_, v_x_3365_);
                    if v___x_3369_ == 0 {
                        v___x_3370_ = crate::leanh::lean_unbox_uint32(v_head_3367_);
                        v___x_3371_ = l_Char_utf8Size(v___x_3370_);
                        v___x_3372_ = lean_nat_add(v_x_3364_, v___x_3371_);
                        crate::leanh::lean_dec(v___x_3371_);
                        crate::leanh::lean_dec(v_x_3364_);
                        v_x_3363_ = v_tail_3368_;
                        v_x_3364_ = v___x_3372_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3364_);
                        v___x_3374_ = crate::leanh::lean_unbox_uint32(v_head_3367_);
                        return v___x_3374_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_utf8GetAux___boxed(
    mut v_x_3375_: *mut crate::leanh::LeanObject,
    mut v_x_3376_: *mut crate::leanh::LeanObject,
    mut v_x_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3378_: u32 = 0;
    let mut v_r_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_String_Pos_Raw_utf8GetAux(v_x_3375_, v_x_3376_, v_x_3377_);
    crate::leanh::lean_dec(v_x_3377_);
    crate::leanh::lean_dec(v_x_3375_);
    v_r_3379_ = crate::leanh::lean_box_uint32(v_res_3378_);
    return v_r_3379_;
}
pub unsafe fn l_String_utf8GetAux(
    mut v_a_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_3383_: u32 = 0;
    v___x_3383_ = l_String_Pos_Raw_utf8GetAux(v_a_3380_, v_a_3381_, v_a_3382_);
    return v___x_3383_;
}
pub unsafe fn l_String_utf8GetAux___boxed(
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3387_: u32 = 0;
    let mut v_r_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_String_utf8GetAux(v_a_3384_, v_a_3385_, v_a_3386_);
    crate::leanh::lean_dec(v_a_3386_);
    crate::leanh::lean_dec(v_a_3384_);
    v_r_3388_ = crate::leanh::lean_box_uint32(v_res_3387_);
    return v_r_3388_;
}
pub unsafe fn l_String_Pos_Raw_get___boxed(
    mut v_s_3391_: *mut crate::leanh::LeanObject,
    mut v_p_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: u32 = 0;
    let mut v_r_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = lean_string_utf8_get(v_s_3391_, v_p_3392_);
    crate::leanh::lean_dec(v_p_3392_);
    crate::leanh::lean_dec_ref(v_s_3391_);
    v_r_3394_ = crate::leanh::lean_box_uint32(v_res_3393_);
    return v_r_3394_;
}
pub unsafe fn l_String_get___boxed(
    mut v_s_3397_: *mut crate::leanh::LeanObject,
    mut v_p_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3399_: u32 = 0;
    let mut v_r_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ = lean_string_utf8_get(v_s_3397_, v_p_3398_);
    crate::leanh::lean_dec(v_p_3398_);
    crate::leanh::lean_dec_ref(v_s_3397_);
    v_r_3400_ = crate::leanh::lean_box_uint32(v_res_3399_);
    return v_r_3400_;
}
pub unsafe fn l_String_Pos_Raw_utf8GetAux_x3f(
    mut v_x_3401_: *mut crate::leanh::LeanObject,
    mut v_x_3402_: *mut crate::leanh::LeanObject,
    mut v_x_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: u32 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3401_) == 0 {
                    crate::leanh::lean_dec(v_x_3402_);
                    v___x_3404_ = crate::leanh::lean_box(0);
                    return v___x_3404_;
                } else {
                    v_head_3405_ = crate::leanh::lean_ctor_get(v_x_3401_, 0);
                    v_tail_3406_ = crate::leanh::lean_ctor_get(v_x_3401_, 1);
                    v___x_3407_ = lean_nat_dec_eq(v_x_3402_, v_x_3403_);
                    if v___x_3407_ == 0 {
                        v___x_3408_ = crate::leanh::lean_unbox_uint32(v_head_3405_);
                        v___x_3409_ = l_Char_utf8Size(v___x_3408_);
                        v___x_3410_ = lean_nat_add(v_x_3402_, v___x_3409_);
                        crate::leanh::lean_dec(v___x_3409_);
                        crate::leanh::lean_dec(v_x_3402_);
                        v_x_3401_ = v_tail_3406_;
                        v_x_3402_ = v___x_3410_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3402_);
                        crate::leanh::lean_inc(v_head_3405_);
                        v___x_3412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3412_, 0, v_head_3405_);
                        return v___x_3412_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_utf8GetAux_x3f___boxed(
    mut v_x_3413_: *mut crate::leanh::LeanObject,
    mut v_x_3414_: *mut crate::leanh::LeanObject,
    mut v_x_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_3413_, v_x_3414_, v_x_3415_);
    crate::leanh::lean_dec(v_x_3415_);
    crate::leanh::lean_dec(v_x_3413_);
    return v_res_3416_;
}
pub unsafe fn l_String_utf8GetAux_x3f(
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_3417_, v_a_3418_, v_a_3419_);
    return v___x_3420_;
}
pub unsafe fn l_String_utf8GetAux_x3f___boxed(
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_a_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3424_ = l_String_utf8GetAux_x3f(v_a_3421_, v_a_3422_, v_a_3423_);
    crate::leanh::lean_dec(v_a_3423_);
    crate::leanh::lean_dec(v_a_3421_);
    return v_res_3424_;
}
pub unsafe fn l_String_Pos_Raw_get_x3f___boxed(
    mut v_a_00___x40___internal___hyg_3427_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3429_ = lean_string_utf8_get_opt(
        v_a_00___x40___internal___hyg_3427_,
        v_a_00___x40___internal___hyg_3428_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_3428_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_3427_);
    return v_res_3429_;
}
pub unsafe fn l_String_get_x3f___boxed(
    mut v_a_00___x40___internal___hyg_3432_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3434_ = lean_string_utf8_get_opt(
        v_a_00___x40___internal___hyg_3432_,
        v_a_00___x40___internal___hyg_3433_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_3433_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_3432_);
    return v_res_3434_;
}
pub unsafe fn l_String_Pos_Raw_get_x21___boxed(
    mut v_s_3437_: *mut crate::leanh::LeanObject,
    mut v_p_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3439_: u32 = 0;
    let mut v_r_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3439_ = lean_string_utf8_get_bang(v_s_3437_, v_p_3438_);
    crate::leanh::lean_dec(v_p_3438_);
    crate::leanh::lean_dec_ref(v_s_3437_);
    v_r_3440_ = crate::leanh::lean_box_uint32(v_res_3439_);
    return v_r_3440_;
}
pub unsafe fn l_String_get_x21___boxed(
    mut v_s_3443_: *mut crate::leanh::LeanObject,
    mut v_p_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3445_: u32 = 0;
    let mut v_r_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = lean_string_utf8_get_bang(v_s_3443_, v_p_3444_);
    crate::leanh::lean_dec(v_p_3444_);
    crate::leanh::lean_dec_ref(v_s_3443_);
    v_r_3446_ = crate::leanh::lean_box_uint32(v_res_3445_);
    return v_r_3446_;
}
pub unsafe fn l_String_Pos_Raw_utf8SetAux(
    mut v_c_x27_3447_: u32,
    mut v_x_3448_: *mut crate::leanh::LeanObject,
    mut v_x_3449_: *mut crate::leanh::LeanObject,
    mut v_x_3450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: u32 = 0;
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3448_) == 0 {
                    return v_x_3448_;
                } else {
                    v_head_3451_ = crate::leanh::lean_ctor_get(v_x_3448_, 0);
                    v_tail_3452_ = crate::leanh::lean_ctor_get(v_x_3448_, 1);
                    v_isSharedCheck_3468_ = (!crate::leanh::lean_is_exclusive(v_x_3448_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3454_ = v_x_3448_;
                        v_isShared_3455_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3452_);
                        crate::leanh::lean_inc(v_head_3451_);
                        crate::leanh::lean_dec(v_x_3448_);
                        v___x_3454_ = crate::leanh::lean_box(0);
                        v_isShared_3455_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3456_ = lean_nat_dec_eq(v_x_3449_, v_x_3450_);
                if v___x_3456_ == 0 {
                    v___x_3457_ = crate::leanh::lean_unbox_uint32(v_head_3451_);
                    v___x_3458_ = l_Char_utf8Size(v___x_3457_);
                    v___x_3459_ = lean_nat_add(v_x_3449_, v___x_3458_);
                    crate::leanh::lean_dec(v___x_3458_);
                    v___x_3460_ = l_String_Pos_Raw_utf8SetAux(
                        v_c_x27_3447_,
                        v_tail_3452_,
                        v___x_3459_,
                        v_x_3450_,
                    );
                    crate::leanh::lean_dec(v___x_3459_);
                    if v_isShared_3455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3454_, 1, v___x_3460_);
                        v___x_3462_ = v___x_3454_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3463_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_head_3451_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3460_);
                        v___x_3462_ = v_reuseFailAlloc_3463_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_head_3451_);
                    v___x_3464_ = crate::leanh::lean_box_uint32(v_c_x27_3447_);
                    if v_isShared_3455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3464_);
                        v___x_3466_ = v___x_3454_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3467_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_tail_3452_);
                        v___x_3466_ = v_reuseFailAlloc_3467_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3462_;
            }
            3 => {
                return v___x_3466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_utf8SetAux___boxed(
    mut v_c_x27_3469_: *mut crate::leanh::LeanObject,
    mut v_x_3470_: *mut crate::leanh::LeanObject,
    mut v_x_3471_: *mut crate::leanh::LeanObject,
    mut v_x_3472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_x27_boxed_3473_: u32 = 0;
    let mut v_res_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_x27_boxed_3473_ = crate::leanh::lean_unbox_uint32(v_c_x27_3469_);
    crate::leanh::lean_dec(v_c_x27_3469_);
    v_res_3474_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_3473_, v_x_3470_, v_x_3471_, v_x_3472_);
    crate::leanh::lean_dec(v_x_3472_);
    crate::leanh::lean_dec(v_x_3471_);
    return v_res_3474_;
}
pub unsafe fn l_String_utf8SetAux(
    mut v_c_x27_3475_: u32,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
    return v___x_3479_;
}
pub unsafe fn l_String_utf8SetAux___boxed(
    mut v_c_x27_3480_: *mut crate::leanh::LeanObject,
    mut v_a_3481_: *mut crate::leanh::LeanObject,
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_x27_boxed_3484_: u32 = 0;
    let mut v_res_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_x27_boxed_3484_ = crate::leanh::lean_unbox_uint32(v_c_x27_3480_);
    crate::leanh::lean_dec(v_c_x27_3480_);
    v_res_3485_ = l_String_utf8SetAux(v_c_x27_boxed_3484_, v_a_3481_, v_a_3482_, v_a_3483_);
    crate::leanh::lean_dec(v_a_3483_);
    crate::leanh::lean_dec(v_a_3482_);
    return v_res_3485_;
}
pub unsafe fn l_String_Slice_Pos_nextFast___redArg(
    mut v_s_3486_: *mut crate::leanh::LeanObject,
    mut v_pos_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3488_ = crate::leanh::lean_ctor_get(v_s_3486_, 0);
    v_startInclusive_3489_ = crate::leanh::lean_ctor_get(v_s_3486_, 1);
    v___x_3490_ = lean_nat_add(v_startInclusive_3489_, v_pos_3487_);
    v___x_3491_ = lean_string_utf8_next_fast(v_str_3488_, v___x_3490_);
    crate::leanh::lean_dec(v___x_3490_);
    v___x_3492_ = lean_nat_sub(v___x_3491_, v_startInclusive_3489_);
    return v___x_3492_;
}
pub unsafe fn l_String_Slice_Pos_nextFast___redArg___boxed(
    mut v_s_3493_: *mut crate::leanh::LeanObject,
    mut v_pos_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_String_Slice_Pos_nextFast___redArg(v_s_3493_, v_pos_3494_);
    crate::leanh::lean_dec(v_pos_3494_);
    crate::leanh::lean_dec_ref(v_s_3493_);
    return v_res_3495_;
}
pub unsafe fn l_String_Slice_Pos_nextFast(
    mut v_s_3496_: *mut crate::leanh::LeanObject,
    mut v_pos_3497_: *mut crate::leanh::LeanObject,
    mut v_h_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3499_ = crate::leanh::lean_ctor_get(v_s_3496_, 0);
    v_startInclusive_3500_ = crate::leanh::lean_ctor_get(v_s_3496_, 1);
    v___x_3501_ = lean_nat_add(v_startInclusive_3500_, v_pos_3497_);
    v___x_3502_ = lean_string_utf8_next_fast(v_str_3499_, v___x_3501_);
    crate::leanh::lean_dec(v___x_3501_);
    v___x_3503_ = lean_nat_sub(v___x_3502_, v_startInclusive_3500_);
    return v___x_3503_;
}
pub unsafe fn l_String_Slice_Pos_nextFast___boxed(
    mut v_s_3504_: *mut crate::leanh::LeanObject,
    mut v_pos_3505_: *mut crate::leanh::LeanObject,
    mut v_h_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_String_Slice_Pos_nextFast(v_s_3504_, v_pos_3505_, v_h_3506_);
    crate::leanh::lean_dec(v_pos_3505_);
    crate::leanh::lean_dec_ref(v_s_3504_);
    return v_res_3507_;
}
pub unsafe fn l_String_sliceTo(
    mut v_s_3508_: *mut crate::leanh::LeanObject,
    mut v_p_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3510_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3511_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3511_, 0, v_s_3508_);
    crate::leanh::lean_ctor_set(v___x_3511_, 1, v___x_3510_);
    crate::leanh::lean_ctor_set(v___x_3511_, 2, v_p_3509_);
    return v___x_3511_;
}
pub unsafe fn l_String_replaceEnd(
    mut v_s_3512_: *mut crate::leanh::LeanObject,
    mut v_p_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3515_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3515_, 0, v_s_3512_);
    crate::leanh::lean_ctor_set(v___x_3515_, 1, v___x_3514_);
    crate::leanh::lean_ctor_set(v___x_3515_, 2, v_p_3513_);
    return v___x_3515_;
}
pub unsafe fn l_String_sliceFrom(
    mut v_s_3516_: *mut crate::leanh::LeanObject,
    mut v_p_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = lean_string_utf8_byte_size(v_s_3516_);
    v___x_3519_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3519_, 0, v_s_3516_);
    crate::leanh::lean_ctor_set(v___x_3519_, 1, v_p_3517_);
    crate::leanh::lean_ctor_set(v___x_3519_, 2, v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_String_replaceStart(
    mut v_s_3520_: *mut crate::leanh::LeanObject,
    mut v_p_3521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3522_ = lean_string_utf8_byte_size(v_s_3520_);
    v___x_3523_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3523_, 0, v_s_3520_);
    crate::leanh::lean_ctor_set(v___x_3523_, 1, v_p_3521_);
    crate::leanh::lean_ctor_set(v___x_3523_, 2, v___x_3522_);
    return v___x_3523_;
}
pub unsafe fn l_String_slice___redArg(
    mut v_s_3524_: *mut crate::leanh::LeanObject,
    mut v_startInclusive_3525_: *mut crate::leanh::LeanObject,
    mut v_endExclusive_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3527_, 0, v_s_3524_);
    crate::leanh::lean_ctor_set(v___x_3527_, 1, v_startInclusive_3525_);
    crate::leanh::lean_ctor_set(v___x_3527_, 2, v_endExclusive_3526_);
    return v___x_3527_;
}
pub unsafe fn l_String_slice(
    mut v_s_3528_: *mut crate::leanh::LeanObject,
    mut v_startInclusive_3529_: *mut crate::leanh::LeanObject,
    mut v_endExclusive_3530_: *mut crate::leanh::LeanObject,
    mut v_h_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3532_, 0, v_s_3528_);
    crate::leanh::lean_ctor_set(v___x_3532_, 1, v_startInclusive_3529_);
    crate::leanh::lean_ctor_set(v___x_3532_, 2, v_endExclusive_3530_);
    return v___x_3532_;
}
pub unsafe fn l_String_slice_x3f(
    mut v_s_3533_: *mut crate::leanh::LeanObject,
    mut v_startInclusive_3534_: *mut crate::leanh::LeanObject,
    mut v_endExclusive_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3536_: u8 = 0;
    v___x_3536_ = lean_nat_dec_le(v_startInclusive_3534_, v_endExclusive_3535_);
    if v___x_3536_ == 0 {
        let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_endExclusive_3535_);
        crate::leanh::lean_dec(v_startInclusive_3534_);
        crate::leanh::lean_dec_ref(v_s_3533_);
        v___x_3537_ = crate::leanh::lean_box(0);
        return v___x_3537_;
    } else {
        let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3538_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3538_, 0, v_s_3533_);
        crate::leanh::lean_ctor_set(v___x_3538_, 1, v_startInclusive_3534_);
        crate::leanh::lean_ctor_set(v___x_3538_, 2, v_endExclusive_3535_);
        v___x_3539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3539_, 0, v___x_3538_);
        return v___x_3539_;
    }
}
pub unsafe fn l_String_slice_x21(
    mut v_s_3540_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3541_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3543_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3544_ = lean_string_utf8_byte_size(v_s_3540_);
    v___x_3545_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3545_, 0, v_s_3540_);
    crate::leanh::lean_ctor_set(v___x_3545_, 1, v___x_3543_);
    crate::leanh::lean_ctor_set(v___x_3545_, 2, v___x_3544_);
    v___x_3546_ = l_String_Slice_slice_x21(v___x_3545_, v_p_u2081_3541_, v_p_u2082_3542_);
    return v___x_3546_;
}
pub unsafe fn l_String_slice_x21___boxed(
    mut v_s_3547_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3548_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l_String_slice_x21(v_s_3547_, v_p_u2081_3548_, v_p_u2082_3549_);
    crate::leanh::lean_dec(v_p_u2082_3549_);
    crate::leanh::lean_dec(v_p_u2081_3548_);
    return v_res_3550_;
}
pub unsafe fn l_String_replaceStartEnd_x21(
    mut v_s_3551_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3552_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ = l_String_slice_x21(v_s_3551_, v_p_u2081_3552_, v_p_u2082_3553_);
    return v___x_3554_;
}
pub unsafe fn l_String_replaceStartEnd_x21___boxed(
    mut v_s_3555_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3556_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3558_ = l_String_replaceStartEnd_x21(v_s_3555_, v_p_u2081_3556_, v_p_u2082_3557_);
    crate::leanh::lean_dec(v_p_u2082_3557_);
    crate::leanh::lean_dec(v_p_u2081_3556_);
    return v_res_3558_;
}
pub unsafe fn l_String_Pos_ofSliceFrom___redArg(
    mut v_p_u2080_3559_: *mut crate::leanh::LeanObject,
    mut v_pos_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = lean_nat_add(v_p_u2080_3559_, v_pos_3560_);
    return v___x_3561_;
}
pub unsafe fn l_String_Pos_ofSliceFrom___redArg___boxed(
    mut v_p_u2080_3562_: *mut crate::leanh::LeanObject,
    mut v_pos_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_3562_, v_pos_3563_);
    crate::leanh::lean_dec(v_pos_3563_);
    crate::leanh::lean_dec(v_p_u2080_3562_);
    return v_res_3564_;
}
pub unsafe fn l_String_Pos_ofSliceFrom(
    mut v_s_3565_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3566_: *mut crate::leanh::LeanObject,
    mut v_pos_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = lean_nat_add(v_p_u2080_3566_, v_pos_3567_);
    return v___x_3568_;
}
pub unsafe fn l_String_Pos_ofSliceFrom___boxed(
    mut v_s_3569_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3570_: *mut crate::leanh::LeanObject,
    mut v_pos_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_String_Pos_ofSliceFrom(v_s_3569_, v_p_u2080_3570_, v_pos_3571_);
    crate::leanh::lean_dec(v_pos_3571_);
    crate::leanh::lean_dec(v_p_u2080_3570_);
    crate::leanh::lean_dec_ref(v_s_3569_);
    return v_res_3572_;
}
pub unsafe fn l_String_Pos_ofReplaceStart___redArg(
    mut v_p_u2080_3573_: *mut crate::leanh::LeanObject,
    mut v_pos_3574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = lean_nat_add(v_p_u2080_3573_, v_pos_3574_);
    return v___x_3575_;
}
pub unsafe fn l_String_Pos_ofReplaceStart___redArg___boxed(
    mut v_p_u2080_3576_: *mut crate::leanh::LeanObject,
    mut v_pos_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_3576_, v_pos_3577_);
    crate::leanh::lean_dec(v_pos_3577_);
    crate::leanh::lean_dec(v_p_u2080_3576_);
    return v_res_3578_;
}
pub unsafe fn l_String_Pos_ofReplaceStart(
    mut v_s_3579_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3580_: *mut crate::leanh::LeanObject,
    mut v_pos_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = lean_nat_add(v_p_u2080_3580_, v_pos_3581_);
    return v___x_3582_;
}
pub unsafe fn l_String_Pos_ofReplaceStart___boxed(
    mut v_s_3583_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3584_: *mut crate::leanh::LeanObject,
    mut v_pos_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l_String_Pos_ofReplaceStart(v_s_3583_, v_p_u2080_3584_, v_pos_3585_);
    crate::leanh::lean_dec(v_pos_3585_);
    crate::leanh::lean_dec(v_p_u2080_3584_);
    crate::leanh::lean_dec_ref(v_s_3583_);
    return v_res_3586_;
}
pub unsafe fn l_String_Pos_sliceFrom___redArg(
    mut v_p_u2080_3587_: *mut crate::leanh::LeanObject,
    mut v_pos_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3589_ = lean_nat_sub(v_pos_3588_, v_p_u2080_3587_);
    return v___x_3589_;
}
pub unsafe fn l_String_Pos_sliceFrom___redArg___boxed(
    mut v_p_u2080_3590_: *mut crate::leanh::LeanObject,
    mut v_pos_3591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3592_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_3590_, v_pos_3591_);
    crate::leanh::lean_dec(v_pos_3591_);
    crate::leanh::lean_dec(v_p_u2080_3590_);
    return v_res_3592_;
}
pub unsafe fn l_String_Pos_sliceFrom(
    mut v_s_3593_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3594_: *mut crate::leanh::LeanObject,
    mut v_pos_3595_: *mut crate::leanh::LeanObject,
    mut v_h_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = lean_nat_sub(v_pos_3595_, v_p_u2080_3594_);
    return v___x_3597_;
}
pub unsafe fn l_String_Pos_sliceFrom___boxed(
    mut v_s_3598_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3599_: *mut crate::leanh::LeanObject,
    mut v_pos_3600_: *mut crate::leanh::LeanObject,
    mut v_h_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3602_ = l_String_Pos_sliceFrom(v_s_3598_, v_p_u2080_3599_, v_pos_3600_, v_h_3601_);
    crate::leanh::lean_dec(v_pos_3600_);
    crate::leanh::lean_dec(v_p_u2080_3599_);
    crate::leanh::lean_dec_ref(v_s_3598_);
    return v_res_3602_;
}
pub unsafe fn l_String_Pos_toReplaceStart___redArg(
    mut v_p_u2080_3603_: *mut crate::leanh::LeanObject,
    mut v_pos_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3605_ = lean_nat_sub(v_pos_3604_, v_p_u2080_3603_);
    return v___x_3605_;
}
pub unsafe fn l_String_Pos_toReplaceStart___redArg___boxed(
    mut v_p_u2080_3606_: *mut crate::leanh::LeanObject,
    mut v_pos_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_3606_, v_pos_3607_);
    crate::leanh::lean_dec(v_pos_3607_);
    crate::leanh::lean_dec(v_p_u2080_3606_);
    return v_res_3608_;
}
pub unsafe fn l_String_Pos_toReplaceStart(
    mut v_s_3609_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3610_: *mut crate::leanh::LeanObject,
    mut v_pos_3611_: *mut crate::leanh::LeanObject,
    mut v_h_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ = lean_nat_sub(v_pos_3611_, v_p_u2080_3610_);
    return v___x_3613_;
}
pub unsafe fn l_String_Pos_toReplaceStart___boxed(
    mut v_s_3614_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3615_: *mut crate::leanh::LeanObject,
    mut v_pos_3616_: *mut crate::leanh::LeanObject,
    mut v_h_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_String_Pos_toReplaceStart(v_s_3614_, v_p_u2080_3615_, v_pos_3616_, v_h_3617_);
    crate::leanh::lean_dec(v_pos_3616_);
    crate::leanh::lean_dec(v_p_u2080_3615_);
    crate::leanh::lean_dec_ref(v_s_3614_);
    return v_res_3618_;
}
pub unsafe fn l_String_Pos_ofSliceTo___redArg(
    mut v_pos_3619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3619_);
    return v_pos_3619_;
}
pub unsafe fn l_String_Pos_ofSliceTo___redArg___boxed(
    mut v_pos_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3621_ = l_String_Pos_ofSliceTo___redArg(v_pos_3620_);
    crate::leanh::lean_dec(v_pos_3620_);
    return v_res_3621_;
}
pub unsafe fn l_String_Pos_ofSliceTo(
    mut v_s_3622_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3623_: *mut crate::leanh::LeanObject,
    mut v_pos_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3624_);
    return v_pos_3624_;
}
pub unsafe fn l_String_Pos_ofSliceTo___boxed(
    mut v_s_3625_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3626_: *mut crate::leanh::LeanObject,
    mut v_pos_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3628_ = l_String_Pos_ofSliceTo(v_s_3625_, v_p_u2080_3626_, v_pos_3627_);
    crate::leanh::lean_dec(v_pos_3627_);
    crate::leanh::lean_dec(v_p_u2080_3626_);
    crate::leanh::lean_dec_ref(v_s_3625_);
    return v_res_3628_;
}
pub unsafe fn l_String_Pos_ofReplaceEnd___redArg(
    mut v_pos_3629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3629_);
    return v_pos_3629_;
}
pub unsafe fn l_String_Pos_ofReplaceEnd___redArg___boxed(
    mut v_pos_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_3630_);
    crate::leanh::lean_dec(v_pos_3630_);
    return v_res_3631_;
}
pub unsafe fn l_String_Pos_ofReplaceEnd(
    mut v_s_3632_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3633_: *mut crate::leanh::LeanObject,
    mut v_pos_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3634_);
    return v_pos_3634_;
}
pub unsafe fn l_String_Pos_ofReplaceEnd___boxed(
    mut v_s_3635_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3636_: *mut crate::leanh::LeanObject,
    mut v_pos_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_String_Pos_ofReplaceEnd(v_s_3635_, v_p_u2080_3636_, v_pos_3637_);
    crate::leanh::lean_dec(v_pos_3637_);
    crate::leanh::lean_dec(v_p_u2080_3636_);
    crate::leanh::lean_dec_ref(v_s_3635_);
    return v_res_3638_;
}
pub unsafe fn l_String_Pos_sliceTo___redArg(
    mut v_pos_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3639_);
    return v_pos_3639_;
}
pub unsafe fn l_String_Pos_sliceTo___redArg___boxed(
    mut v_pos_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_String_Pos_sliceTo___redArg(v_pos_3640_);
    crate::leanh::lean_dec(v_pos_3640_);
    return v_res_3641_;
}
pub unsafe fn l_String_Pos_sliceTo(
    mut v_s_3642_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3643_: *mut crate::leanh::LeanObject,
    mut v_pos_3644_: *mut crate::leanh::LeanObject,
    mut v_h_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3644_);
    return v_pos_3644_;
}
pub unsafe fn l_String_Pos_sliceTo___boxed(
    mut v_s_3646_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3647_: *mut crate::leanh::LeanObject,
    mut v_pos_3648_: *mut crate::leanh::LeanObject,
    mut v_h_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_String_Pos_sliceTo(v_s_3646_, v_p_u2080_3647_, v_pos_3648_, v_h_3649_);
    crate::leanh::lean_dec(v_pos_3648_);
    crate::leanh::lean_dec(v_p_u2080_3647_);
    crate::leanh::lean_dec_ref(v_s_3646_);
    return v_res_3650_;
}
pub unsafe fn l_String_Pos_toReplaceEnd___redArg(
    mut v_pos_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3651_);
    return v_pos_3651_;
}
pub unsafe fn l_String_Pos_toReplaceEnd___redArg___boxed(
    mut v_pos_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3653_ = l_String_Pos_toReplaceEnd___redArg(v_pos_3652_);
    crate::leanh::lean_dec(v_pos_3652_);
    return v_res_3653_;
}
pub unsafe fn l_String_Pos_toReplaceEnd(
    mut v_s_3654_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3655_: *mut crate::leanh::LeanObject,
    mut v_pos_3656_: *mut crate::leanh::LeanObject,
    mut v_h_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_3656_);
    return v_pos_3656_;
}
pub unsafe fn l_String_Pos_toReplaceEnd___boxed(
    mut v_s_3658_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3659_: *mut crate::leanh::LeanObject,
    mut v_pos_3660_: *mut crate::leanh::LeanObject,
    mut v_h_3661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3662_ = l_String_Pos_toReplaceEnd(v_s_3658_, v_p_u2080_3659_, v_pos_3660_, v_h_3661_);
    crate::leanh::lean_dec(v_pos_3660_);
    crate::leanh::lean_dec(v_p_u2080_3659_);
    crate::leanh::lean_dec_ref(v_s_3658_);
    return v_res_3662_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice___redArg(
    mut v_p_u2080_3663_: *mut crate::leanh::LeanObject,
    mut v_pos_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = lean_nat_add(v_p_u2080_3663_, v_pos_3664_);
    return v___x_3665_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice___redArg___boxed(
    mut v_p_u2080_3666_: *mut crate::leanh::LeanObject,
    mut v_pos_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_3666_, v_pos_3667_);
    crate::leanh::lean_dec(v_pos_3667_);
    crate::leanh::lean_dec(v_p_u2080_3666_);
    return v_res_3668_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice(
    mut v_s_3669_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3670_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3671_: *mut crate::leanh::LeanObject,
    mut v_h_3672_: *mut crate::leanh::LeanObject,
    mut v_pos_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3674_ = lean_nat_add(v_p_u2080_3670_, v_pos_3673_);
    return v___x_3674_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice___boxed(
    mut v_s_3675_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3676_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3677_: *mut crate::leanh::LeanObject,
    mut v_h_3678_: *mut crate::leanh::LeanObject,
    mut v_pos_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_String_Slice_Pos_ofSlice(
        v_s_3675_,
        v_p_u2080_3676_,
        v_p_u2081_3677_,
        v_h_3678_,
        v_pos_3679_,
    );
    crate::leanh::lean_dec(v_pos_3679_);
    crate::leanh::lean_dec(v_p_u2081_3677_);
    crate::leanh::lean_dec(v_p_u2080_3676_);
    crate::leanh::lean_dec_ref(v_s_3675_);
    return v_res_3680_;
}
pub unsafe fn l_String_Pos_ofSlice___redArg(
    mut v_p_u2080_3681_: *mut crate::leanh::LeanObject,
    mut v_pos_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3683_ = lean_nat_add(v_p_u2080_3681_, v_pos_3682_);
    return v___x_3683_;
}
pub unsafe fn l_String_Pos_ofSlice___redArg___boxed(
    mut v_p_u2080_3684_: *mut crate::leanh::LeanObject,
    mut v_pos_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_String_Pos_ofSlice___redArg(v_p_u2080_3684_, v_pos_3685_);
    crate::leanh::lean_dec(v_pos_3685_);
    crate::leanh::lean_dec(v_p_u2080_3684_);
    return v_res_3686_;
}
pub unsafe fn l_String_Pos_ofSlice(
    mut v_s_3687_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3688_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3689_: *mut crate::leanh::LeanObject,
    mut v_h_3690_: *mut crate::leanh::LeanObject,
    mut v_pos_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = lean_nat_add(v_p_u2080_3688_, v_pos_3691_);
    return v___x_3692_;
}
pub unsafe fn l_String_Pos_ofSlice___boxed(
    mut v_s_3693_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3694_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3695_: *mut crate::leanh::LeanObject,
    mut v_h_3696_: *mut crate::leanh::LeanObject,
    mut v_pos_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_String_Pos_ofSlice(
        v_s_3693_,
        v_p_u2080_3694_,
        v_p_u2081_3695_,
        v_h_3696_,
        v_pos_3697_,
    );
    crate::leanh::lean_dec(v_pos_3697_);
    crate::leanh::lean_dec(v_p_u2081_3695_);
    crate::leanh::lean_dec(v_p_u2080_3694_);
    crate::leanh::lean_dec_ref(v_s_3693_);
    return v_res_3698_;
}
pub unsafe fn l_String_Slice_Pos_slice___redArg(
    mut v_pos_3699_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3701_ = lean_nat_sub(v_pos_3699_, v_p_u2080_3700_);
    return v___x_3701_;
}
pub unsafe fn l_String_Slice_Pos_slice___redArg___boxed(
    mut v_pos_3702_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3704_ = l_String_Slice_Pos_slice___redArg(v_pos_3702_, v_p_u2080_3703_);
    crate::leanh::lean_dec(v_p_u2080_3703_);
    crate::leanh::lean_dec(v_pos_3702_);
    return v_res_3704_;
}
pub unsafe fn l_String_Slice_Pos_slice(
    mut v_s_3705_: *mut crate::leanh::LeanObject,
    mut v_pos_3706_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3707_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3708_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3709_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_3710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = lean_nat_sub(v_pos_3706_, v_p_u2080_3707_);
    return v___x_3711_;
}
pub unsafe fn l_String_Slice_Pos_slice___boxed(
    mut v_s_3712_: *mut crate::leanh::LeanObject,
    mut v_pos_3713_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3714_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3715_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3716_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3718_ = l_String_Slice_Pos_slice(
        v_s_3712_,
        v_pos_3713_,
        v_p_u2080_3714_,
        v_p_u2081_3715_,
        v_h_u2081_3716_,
        v_h_u2082_3717_,
    );
    crate::leanh::lean_dec(v_p_u2081_3715_);
    crate::leanh::lean_dec(v_p_u2080_3714_);
    crate::leanh::lean_dec(v_pos_3713_);
    crate::leanh::lean_dec_ref(v_s_3712_);
    return v_res_3718_;
}
pub unsafe fn l_String_Pos_slice___redArg(
    mut v_pos_3719_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = lean_nat_sub(v_pos_3719_, v_p_u2080_3720_);
    return v___x_3721_;
}
pub unsafe fn l_String_Pos_slice___redArg___boxed(
    mut v_pos_3722_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_String_Pos_slice___redArg(v_pos_3722_, v_p_u2080_3723_);
    crate::leanh::lean_dec(v_p_u2080_3723_);
    crate::leanh::lean_dec(v_pos_3722_);
    return v_res_3724_;
}
pub unsafe fn l_String_Pos_slice(
    mut v_s_3725_: *mut crate::leanh::LeanObject,
    mut v_pos_3726_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3727_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3728_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3729_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3731_ = lean_nat_sub(v_pos_3726_, v_p_u2080_3727_);
    return v___x_3731_;
}
pub unsafe fn l_String_Pos_slice___boxed(
    mut v_s_3732_: *mut crate::leanh::LeanObject,
    mut v_pos_3733_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3734_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3735_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_3736_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_3737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_String_Pos_slice(
        v_s_3732_,
        v_pos_3733_,
        v_p_u2080_3734_,
        v_p_u2081_3735_,
        v_h_u2081_3736_,
        v_h_u2082_3737_,
    );
    crate::leanh::lean_dec(v_p_u2081_3735_);
    crate::leanh::lean_dec(v_p_u2080_3734_);
    crate::leanh::lean_dec(v_pos_3733_);
    crate::leanh::lean_dec_ref(v_s_3732_);
    return v_res_3738_;
}
pub unsafe fn _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ = l_String_Slice_Pos_sliceOrPanic___redArg___closed__1;
    v___x_3742_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3743_ = crate::leanh::lean_unsigned_to_nat(2676);
    v___x_3744_ = l_String_Slice_Pos_sliceOrPanic___redArg___closed__0;
    v___x_3745_ = l_String_fromUTF8_x21___closed__1;
    v___x_3746_ = l_mkPanicMessageWithDecl(
        v___x_3745_,
        v___x_3744_,
        v___x_3743_,
        v___x_3742_,
        v___x_3741_,
    );
    return v___x_3746_;
}
pub unsafe fn l_String_Slice_Pos_sliceOrPanic___redArg(
    mut v_pos_3747_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3748_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: u8 = 0;
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3754_ = lean_nat_dec_le(v_p_u2080_3748_, v_pos_3747_);
                if v___x_3754_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3755_ = lean_nat_dec_le(v_pos_3747_, v_p_u2081_3749_);
                    if v___x_3755_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3756_ = lean_nat_sub(v_pos_3747_, v_p_u2080_3748_);
                        return v___x_3756_;
                    }
                }
            }
            1 => {
                v___x_3751_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3752_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once
                    ),
                    _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2,
                );
                v___x_3753_ = l_panic___redArg(v___x_3751_, v___x_3752_);
                return v___x_3753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_sliceOrPanic___redArg___boxed(
    mut v_pos_3757_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3758_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ =
        l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_3757_, v_p_u2080_3758_, v_p_u2081_3759_);
    crate::leanh::lean_dec(v_p_u2081_3759_);
    crate::leanh::lean_dec(v_p_u2080_3758_);
    crate::leanh::lean_dec(v_pos_3757_);
    return v_res_3760_;
}
pub unsafe fn l_String_Slice_Pos_sliceOrPanic(
    mut v_s_3761_: *mut crate::leanh::LeanObject,
    mut v_pos_3762_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3763_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3764_: *mut crate::leanh::LeanObject,
    mut v_h_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = lean_nat_dec_le(v_p_u2080_3763_, v_pos_3762_);
                if v___x_3770_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3771_ = lean_nat_dec_le(v_pos_3762_, v_p_u2081_3764_);
                    if v___x_3771_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3772_ = lean_nat_sub(v_pos_3762_, v_p_u2080_3763_);
                        return v___x_3772_;
                    }
                }
            }
            1 => {
                v___x_3767_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3768_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once
                    ),
                    _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2,
                );
                v___x_3769_ = l_panic___redArg(v___x_3767_, v___x_3768_);
                return v___x_3769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_sliceOrPanic___boxed(
    mut v_s_3773_: *mut crate::leanh::LeanObject,
    mut v_pos_3774_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3775_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3776_: *mut crate::leanh::LeanObject,
    mut v_h_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_String_Slice_Pos_sliceOrPanic(
        v_s_3773_,
        v_pos_3774_,
        v_p_u2080_3775_,
        v_p_u2081_3776_,
        v_h_3777_,
    );
    crate::leanh::lean_dec(v_p_u2081_3776_);
    crate::leanh::lean_dec(v_p_u2080_3775_);
    crate::leanh::lean_dec(v_pos_3774_);
    crate::leanh::lean_dec_ref(v_s_3773_);
    return v_res_3778_;
}
pub unsafe fn l_String_Pos_sliceOrPanic___redArg(
    mut v_pos_3779_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3780_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3786_ = lean_nat_dec_le(v_p_u2080_3780_, v_pos_3779_);
                if v___x_3786_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3787_ = lean_nat_dec_le(v_pos_3779_, v_p_u2081_3781_);
                    if v___x_3787_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3788_ = lean_nat_sub(v_pos_3779_, v_p_u2080_3780_);
                        return v___x_3788_;
                    }
                }
            }
            1 => {
                v___x_3783_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3784_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once
                    ),
                    _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2,
                );
                v___x_3785_ = l_panic___redArg(v___x_3783_, v___x_3784_);
                return v___x_3785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_sliceOrPanic___redArg___boxed(
    mut v_pos_3789_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3790_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_String_Pos_sliceOrPanic___redArg(v_pos_3789_, v_p_u2080_3790_, v_p_u2081_3791_);
    crate::leanh::lean_dec(v_p_u2081_3791_);
    crate::leanh::lean_dec(v_p_u2080_3790_);
    crate::leanh::lean_dec(v_pos_3789_);
    return v_res_3792_;
}
pub unsafe fn l_String_Pos_sliceOrPanic(
    mut v_s_3793_: *mut crate::leanh::LeanObject,
    mut v_pos_3794_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3795_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3796_: *mut crate::leanh::LeanObject,
    mut v_h_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: u8 = 0;
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_nat_dec_le(v_p_u2080_3795_, v_pos_3794_);
                if v___x_3802_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3803_ = lean_nat_dec_le(v_pos_3794_, v_p_u2081_3796_);
                    if v___x_3803_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3804_ = lean_nat_sub(v_pos_3794_, v_p_u2080_3795_);
                        return v___x_3804_;
                    }
                }
            }
            1 => {
                v___x_3799_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3800_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_sliceOrPanic___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once
                    ),
                    _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2,
                );
                v___x_3801_ = l_panic___redArg(v___x_3799_, v___x_3800_);
                return v___x_3801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_sliceOrPanic___boxed(
    mut v_s_3805_: *mut crate::leanh::LeanObject,
    mut v_pos_3806_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3807_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3808_: *mut crate::leanh::LeanObject,
    mut v_h_3809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3810_ = l_String_Pos_sliceOrPanic(
        v_s_3805_,
        v_pos_3806_,
        v_p_u2080_3807_,
        v_p_u2081_3808_,
        v_h_3809_,
    );
    crate::leanh::lean_dec(v_p_u2081_3808_);
    crate::leanh::lean_dec(v_p_u2080_3807_);
    crate::leanh::lean_dec(v_pos_3806_);
    crate::leanh::lean_dec_ref(v_s_3805_);
    return v_res_3810_;
}
pub unsafe fn _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_String_Slice_slice_x21___closed__1;
    v___x_3813_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3814_ = crate::leanh::lean_unsigned_to_nat(2700);
    v___x_3815_ = l_String_Slice_Pos_ofSlice_x21___redArg___closed__0;
    v___x_3816_ = l_String_fromUTF8_x21___closed__1;
    v___x_3817_ = l_mkPanicMessageWithDecl(
        v___x_3816_,
        v___x_3815_,
        v___x_3814_,
        v___x_3813_,
        v___x_3812_,
    );
    return v___x_3817_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice_x21___redArg(
    mut v_p_u2080_3818_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3819_: *mut crate::leanh::LeanObject,
    mut v_pos_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: u8 = 0;
    v___x_3821_ = lean_nat_dec_le(v_p_u2080_3818_, v_p_u2081_3819_);
    if v___x_3821_ == 0 {
        let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3822_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3823_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once),
            _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1,
        );
        v___x_3824_ = l_panic___redArg(v___x_3822_, v___x_3823_);
        return v___x_3824_;
    } else {
        let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3825_ = lean_nat_add(v_p_u2080_3818_, v_pos_3820_);
        return v___x_3825_;
    }
}
pub unsafe fn l_String_Slice_Pos_ofSlice_x21___redArg___boxed(
    mut v_p_u2080_3826_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3827_: *mut crate::leanh::LeanObject,
    mut v_pos_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3829_ =
        l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_3826_, v_p_u2081_3827_, v_pos_3828_);
    crate::leanh::lean_dec(v_pos_3828_);
    crate::leanh::lean_dec(v_p_u2081_3827_);
    crate::leanh::lean_dec(v_p_u2080_3826_);
    return v_res_3829_;
}
pub unsafe fn l_String_Slice_Pos_ofSlice_x21(
    mut v_s_3830_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3831_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3832_: *mut crate::leanh::LeanObject,
    mut v_pos_3833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3834_: u8 = 0;
    v___x_3834_ = lean_nat_dec_le(v_p_u2080_3831_, v_p_u2081_3832_);
    if v___x_3834_ == 0 {
        let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3835_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3836_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once),
            _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1,
        );
        v___x_3837_ = l_panic___redArg(v___x_3835_, v___x_3836_);
        return v___x_3837_;
    } else {
        let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3838_ = lean_nat_add(v_p_u2080_3831_, v_pos_3833_);
        return v___x_3838_;
    }
}
pub unsafe fn l_String_Slice_Pos_ofSlice_x21___boxed(
    mut v_s_3839_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3840_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3841_: *mut crate::leanh::LeanObject,
    mut v_pos_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3843_ =
        l_String_Slice_Pos_ofSlice_x21(v_s_3839_, v_p_u2080_3840_, v_p_u2081_3841_, v_pos_3842_);
    crate::leanh::lean_dec(v_pos_3842_);
    crate::leanh::lean_dec(v_p_u2081_3841_);
    crate::leanh::lean_dec(v_p_u2080_3840_);
    crate::leanh::lean_dec_ref(v_s_3839_);
    return v_res_3843_;
}
pub unsafe fn l_String_Pos_ofSlice_x21___redArg(
    mut v_p_u2080_3844_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3845_: *mut crate::leanh::LeanObject,
    mut v_pos_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: u8 = 0;
    v___x_3847_ = lean_nat_dec_le(v_p_u2080_3844_, v_p_u2081_3845_);
    if v___x_3847_ == 0 {
        let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3848_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3849_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once),
            _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1,
        );
        v___x_3850_ = l_panic___redArg(v___x_3848_, v___x_3849_);
        return v___x_3850_;
    } else {
        let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3851_ = lean_nat_add(v_p_u2080_3844_, v_pos_3846_);
        return v___x_3851_;
    }
}
pub unsafe fn l_String_Pos_ofSlice_x21___redArg___boxed(
    mut v_p_u2080_3852_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3853_: *mut crate::leanh::LeanObject,
    mut v_pos_3854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3855_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_3852_, v_p_u2081_3853_, v_pos_3854_);
    crate::leanh::lean_dec(v_pos_3854_);
    crate::leanh::lean_dec(v_p_u2081_3853_);
    crate::leanh::lean_dec(v_p_u2080_3852_);
    return v_res_3855_;
}
pub unsafe fn l_String_Pos_ofSlice_x21(
    mut v_s_3856_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3857_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3858_: *mut crate::leanh::LeanObject,
    mut v_pos_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3860_: u8 = 0;
    v___x_3860_ = lean_nat_dec_le(v_p_u2080_3857_, v_p_u2081_3858_);
    if v___x_3860_ == 0 {
        let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3861_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3862_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once),
            _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1,
        );
        v___x_3863_ = l_panic___redArg(v___x_3861_, v___x_3862_);
        return v___x_3863_;
    } else {
        let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3864_ = lean_nat_add(v_p_u2080_3857_, v_pos_3859_);
        return v___x_3864_;
    }
}
pub unsafe fn l_String_Pos_ofSlice_x21___boxed(
    mut v_s_3865_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3866_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3867_: *mut crate::leanh::LeanObject,
    mut v_pos_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ =
        l_String_Pos_ofSlice_x21(v_s_3865_, v_p_u2080_3866_, v_p_u2081_3867_, v_pos_3868_);
    crate::leanh::lean_dec(v_pos_3868_);
    crate::leanh::lean_dec(v_p_u2081_3867_);
    crate::leanh::lean_dec(v_p_u2080_3866_);
    crate::leanh::lean_dec_ref(v_s_3865_);
    return v_res_3869_;
}
pub unsafe fn _init_l_String_Slice_Pos_slice_x21___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3872_ = l_String_Slice_Pos_slice_x21___redArg___closed__1;
    v___x_3873_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3874_ = crate::leanh::lean_unsigned_to_nat(2718);
    v___x_3875_ = l_String_Slice_Pos_slice_x21___redArg___closed__0;
    v___x_3876_ = l_String_fromUTF8_x21___closed__1;
    v___x_3877_ = l_mkPanicMessageWithDecl(
        v___x_3876_,
        v___x_3875_,
        v___x_3874_,
        v___x_3873_,
        v___x_3872_,
    );
    return v___x_3877_;
}
pub unsafe fn l_String_Slice_Pos_slice_x21___redArg(
    mut v_pos_3878_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3879_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: u8 = 0;
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3885_ = lean_nat_dec_le(v_p_u2080_3879_, v_pos_3878_);
                if v___x_3885_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3886_ = lean_nat_dec_le(v_pos_3878_, v_p_u2081_3880_);
                    if v___x_3886_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3887_ = lean_nat_sub(v_pos_3878_, v_p_u2080_3879_);
                        return v___x_3887_;
                    }
                }
            }
            1 => {
                v___x_3882_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3883_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2_once),
                    _init_l_String_Slice_Pos_slice_x21___redArg___closed__2,
                );
                v___x_3884_ = l_panic___redArg(v___x_3882_, v___x_3883_);
                return v___x_3884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_slice_x21___redArg___boxed(
    mut v_pos_3888_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3889_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3891_ =
        l_String_Slice_Pos_slice_x21___redArg(v_pos_3888_, v_p_u2080_3889_, v_p_u2081_3890_);
    crate::leanh::lean_dec(v_p_u2081_3890_);
    crate::leanh::lean_dec(v_p_u2080_3889_);
    crate::leanh::lean_dec(v_pos_3888_);
    return v_res_3891_;
}
pub unsafe fn l_String_Slice_Pos_slice_x21(
    mut v_s_3892_: *mut crate::leanh::LeanObject,
    mut v_pos_3893_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3894_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: u8 = 0;
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3900_ = lean_nat_dec_le(v_p_u2080_3894_, v_pos_3893_);
                if v___x_3900_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3901_ = lean_nat_dec_le(v_pos_3893_, v_p_u2081_3895_);
                    if v___x_3901_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3902_ = lean_nat_sub(v_pos_3893_, v_p_u2080_3894_);
                        return v___x_3902_;
                    }
                }
            }
            1 => {
                v___x_3897_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3898_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2_once),
                    _init_l_String_Slice_Pos_slice_x21___redArg___closed__2,
                );
                v___x_3899_ = l_panic___redArg(v___x_3897_, v___x_3898_);
                return v___x_3899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_slice_x21___boxed(
    mut v_s_3903_: *mut crate::leanh::LeanObject,
    mut v_pos_3904_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3905_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3907_ =
        l_String_Slice_Pos_slice_x21(v_s_3903_, v_pos_3904_, v_p_u2080_3905_, v_p_u2081_3906_);
    crate::leanh::lean_dec(v_p_u2081_3906_);
    crate::leanh::lean_dec(v_p_u2080_3905_);
    crate::leanh::lean_dec(v_pos_3904_);
    crate::leanh::lean_dec_ref(v_s_3903_);
    return v_res_3907_;
}
pub unsafe fn l_String_Pos_slice_x21___redArg(
    mut v_pos_3908_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3909_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: u8 = 0;
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3915_ = lean_nat_dec_le(v_p_u2080_3909_, v_pos_3908_);
                if v___x_3915_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3916_ = lean_nat_dec_le(v_pos_3908_, v_p_u2081_3910_);
                    if v___x_3916_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3917_ = lean_nat_sub(v_pos_3908_, v_p_u2080_3909_);
                        return v___x_3917_;
                    }
                }
            }
            1 => {
                v___x_3912_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3913_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2_once),
                    _init_l_String_Slice_Pos_slice_x21___redArg___closed__2,
                );
                v___x_3914_ = l_panic___redArg(v___x_3912_, v___x_3913_);
                return v___x_3914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_slice_x21___redArg___boxed(
    mut v_pos_3918_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3919_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3921_ = l_String_Pos_slice_x21___redArg(v_pos_3918_, v_p_u2080_3919_, v_p_u2081_3920_);
    crate::leanh::lean_dec(v_p_u2081_3920_);
    crate::leanh::lean_dec(v_p_u2080_3919_);
    crate::leanh::lean_dec(v_pos_3918_);
    return v_res_3921_;
}
pub unsafe fn l_String_Pos_slice_x21(
    mut v_s_3922_: *mut crate::leanh::LeanObject,
    mut v_pos_3923_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3924_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3930_ = lean_nat_dec_le(v_p_u2080_3924_, v_pos_3923_);
                if v___x_3930_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3931_ = lean_nat_dec_le(v_pos_3923_, v_p_u2081_3925_);
                    if v___x_3931_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3932_ = lean_nat_sub(v_pos_3923_, v_p_u2080_3924_);
                        return v___x_3932_;
                    }
                }
            }
            1 => {
                v___x_3927_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3928_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_String_Slice_Pos_slice_x21___redArg___closed__2_once),
                    _init_l_String_Slice_Pos_slice_x21___redArg___closed__2,
                );
                v___x_3929_ = l_panic___redArg(v___x_3927_, v___x_3928_);
                return v___x_3929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_slice_x21___boxed(
    mut v_s_3933_: *mut crate::leanh::LeanObject,
    mut v_pos_3934_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3935_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3937_ = l_String_Pos_slice_x21(v_s_3933_, v_pos_3934_, v_p_u2080_3935_, v_p_u2081_3936_);
    crate::leanh::lean_dec(v_p_u2081_3936_);
    crate::leanh::lean_dec(v_p_u2080_3935_);
    crate::leanh::lean_dec(v_pos_3934_);
    crate::leanh::lean_dec_ref(v_s_3933_);
    return v_res_3937_;
}
pub unsafe fn l_String_Slice_extract(
    mut v_s_3938_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3939_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3941_ = crate::leanh::lean_ctor_get(v_s_3938_, 0);
    v_startInclusive_3942_ = crate::leanh::lean_ctor_get(v_s_3938_, 1);
    v___x_3943_ = lean_nat_add(v_startInclusive_3942_, v_p_u2080_3939_);
    v___x_3944_ = lean_nat_add(v_startInclusive_3942_, v_p_u2081_3940_);
    v___x_3945_ = lean_string_utf8_extract(v_str_3941_, v___x_3943_, v___x_3944_);
    crate::leanh::lean_dec(v___x_3944_);
    crate::leanh::lean_dec(v___x_3943_);
    return v___x_3945_;
}
pub unsafe fn l_String_Slice_extract___boxed(
    mut v_s_3946_: *mut crate::leanh::LeanObject,
    mut v_p_u2080_3947_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3949_ = l_String_Slice_extract(v_s_3946_, v_p_u2080_3947_, v_p_u2081_3948_);
    crate::leanh::lean_dec(v_p_u2081_3948_);
    crate::leanh::lean_dec(v_p_u2080_3947_);
    crate::leanh::lean_dec_ref(v_s_3946_);
    return v_res_3949_;
}
pub unsafe fn l_String_Slice_Pos_nextn(
    mut v_s_3950_: *mut crate::leanh::LeanObject,
    mut v_p_3951_: *mut crate::leanh::LeanObject,
    mut v_n_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v_one_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3953_ = crate::leanh::lean_ctor_get(v_s_3950_, 0);
                v_startInclusive_3954_ = crate::leanh::lean_ctor_get(v_s_3950_, 1);
                v_endExclusive_3955_ = crate::leanh::lean_ctor_get(v_s_3950_, 2);
                v_zero_3956_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3957_ = lean_nat_dec_eq(v_n_3952_, v_zero_3956_);
                if v_isZero_3957_ == 1 {
                    crate::leanh::lean_dec(v_n_3952_);
                    return v_p_3951_;
                } else {
                    v___x_3958_ = lean_nat_sub(v_endExclusive_3955_, v_startInclusive_3954_);
                    v___x_3959_ = lean_nat_dec_eq(v_p_3951_, v___x_3958_);
                    crate::leanh::lean_dec(v___x_3958_);
                    v_one_3960_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3961_ = lean_nat_sub(v_n_3952_, v_one_3960_);
                    crate::leanh::lean_dec(v_n_3952_);
                    if v___x_3959_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v_isZero_3957_ == 0 {
                            crate::leanh::lean_dec(v_n_3961_);
                            return v_p_3951_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3963_ = lean_nat_add(v_startInclusive_3954_, v_p_3951_);
                crate::leanh::lean_dec(v_p_3951_);
                v___x_3964_ = lean_string_utf8_next_fast(v_str_3953_, v___x_3963_);
                crate::leanh::lean_dec(v___x_3963_);
                v___x_3965_ = lean_nat_sub(v___x_3964_, v_startInclusive_3954_);
                v_p_3951_ = v___x_3965_;
                v_n_3952_ = v_n_3961_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_nextn___boxed(
    mut v_s_3967_: *mut crate::leanh::LeanObject,
    mut v_p_3968_: *mut crate::leanh::LeanObject,
    mut v_n_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_String_Slice_Pos_nextn(v_s_3967_, v_p_3968_, v_n_3969_);
    crate::leanh::lean_dec_ref(v_s_3967_);
    return v_res_3970_;
}
pub unsafe fn l_String_Pos_nextn(
    mut v_s_3971_: *mut crate::leanh::LeanObject,
    mut v_p_3972_: *mut crate::leanh::LeanObject,
    mut v_n_3973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3974_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3975_ = lean_string_utf8_byte_size(v_s_3971_);
    v___x_3976_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3976_, 0, v_s_3971_);
    crate::leanh::lean_ctor_set(v___x_3976_, 1, v___x_3974_);
    crate::leanh::lean_ctor_set(v___x_3976_, 2, v___x_3975_);
    v___x_3977_ = l_String_Slice_Pos_nextn(v___x_3976_, v_p_3972_, v_n_3973_);
    crate::leanh::lean_dec_ref_known(v___x_3976_, 3);
    return v___x_3977_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(
    mut v_n_3978_: *mut crate::leanh::LeanObject,
    mut v_h__1_3979_: *mut crate::leanh::LeanObject,
    mut v_h__2_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3982_: u8 = 0;
    v_zero_3981_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3982_ = lean_nat_dec_eq(v_n_3978_, v_zero_3981_);
    if v_isZero_3982_ == 1 {
        let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3980_);
        v___x_3983_ = crate::leanh::lean_box(0);
        v___x_3984_ = crate::leanh::lean_apply_1(v_h__1_3979_, v___x_3983_);
        return v___x_3984_;
    } else {
        let mut v_one_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3979_);
        v_one_3985_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3986_ = lean_nat_sub(v_n_3978_, v_one_3985_);
        v___x_3987_ = crate::leanh::lean_apply_1(v_h__2_3980_, v_n_3986_);
        return v___x_3987_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(
    mut v_n_3988_: *mut crate::leanh::LeanObject,
    mut v_h__1_3989_: *mut crate::leanh::LeanObject,
    mut v_h__2_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ =
        l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(
            v_n_3988_,
            v_h__1_3989_,
            v_h__2_3990_,
        );
    crate::leanh::lean_dec(v_n_3988_);
    return v_res_3991_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(
    mut v_motive_3992_: *mut crate::leanh::LeanObject,
    mut v_n_3993_: *mut crate::leanh::LeanObject,
    mut v_h__1_3994_: *mut crate::leanh::LeanObject,
    mut v_h__2_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3997_: u8 = 0;
    v_zero_3996_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3997_ = lean_nat_dec_eq(v_n_3993_, v_zero_3996_);
    if v_isZero_3997_ == 1 {
        let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3995_);
        v___x_3998_ = crate::leanh::lean_box(0);
        v___x_3999_ = crate::leanh::lean_apply_1(v_h__1_3994_, v___x_3998_);
        return v___x_3999_;
    } else {
        let mut v_one_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3994_);
        v_one_4000_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_4001_ = lean_nat_sub(v_n_3993_, v_one_4000_);
        v___x_4002_ = crate::leanh::lean_apply_1(v_h__2_3995_, v_n_4001_);
        return v___x_4002_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(
    mut v_motive_4003_: *mut crate::leanh::LeanObject,
    mut v_n_4004_: *mut crate::leanh::LeanObject,
    mut v_h__1_4005_: *mut crate::leanh::LeanObject,
    mut v_h__2_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4007_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(
        v_motive_4003_,
        v_n_4004_,
        v_h__1_4005_,
        v_h__2_4006_,
    );
    crate::leanh::lean_dec(v_n_4004_);
    return v_res_4007_;
}
pub unsafe fn l_String_Pos_Raw_next___boxed(
    mut v_s_4010_: *mut crate::leanh::LeanObject,
    mut v_p_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4012_ = lean_string_utf8_next(v_s_4010_, v_p_4011_);
    crate::leanh::lean_dec(v_p_4011_);
    crate::leanh::lean_dec_ref(v_s_4010_);
    return v_res_4012_;
}
pub unsafe fn l_String_next___boxed(
    mut v_s_4015_: *mut crate::leanh::LeanObject,
    mut v_p_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = lean_string_utf8_next(v_s_4015_, v_p_4016_);
    crate::leanh::lean_dec(v_p_4016_);
    crate::leanh::lean_dec_ref(v_s_4015_);
    return v_res_4017_;
}
pub unsafe fn l_String_Pos_Raw_utf8PrevAux(
    mut v_x_4018_: *mut crate::leanh::LeanObject,
    mut v_x_4019_: *mut crate::leanh::LeanObject,
    mut v_x_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: u32 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_x27_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4018_) == 0 {
                    crate::leanh::lean_dec(v_x_4019_);
                    v___x_4021_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4022_ = lean_nat_sub(v_x_4020_, v___x_4021_);
                    return v___x_4022_;
                } else {
                    v_head_4023_ = crate::leanh::lean_ctor_get(v_x_4018_, 0);
                    v_tail_4024_ = crate::leanh::lean_ctor_get(v_x_4018_, 1);
                    v___x_4025_ = crate::leanh::lean_unbox_uint32(v_head_4023_);
                    v___x_4026_ = l_Char_utf8Size(v___x_4025_);
                    v_i_x27_4027_ = lean_nat_add(v_x_4019_, v___x_4026_);
                    crate::leanh::lean_dec(v___x_4026_);
                    v___x_4028_ = lean_nat_dec_le(v_x_4020_, v_i_x27_4027_);
                    if v___x_4028_ == 0 {
                        crate::leanh::lean_dec(v_x_4019_);
                        v_x_4018_ = v_tail_4024_;
                        v_x_4019_ = v_i_x27_4027_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_x27_4027_);
                        return v_x_4019_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_utf8PrevAux___boxed(
    mut v_x_4030_: *mut crate::leanh::LeanObject,
    mut v_x_4031_: *mut crate::leanh::LeanObject,
    mut v_x_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4033_ = l_String_Pos_Raw_utf8PrevAux(v_x_4030_, v_x_4031_, v_x_4032_);
    crate::leanh::lean_dec(v_x_4032_);
    crate::leanh::lean_dec(v_x_4030_);
    return v_res_4033_;
}
pub unsafe fn l_String_utf8PrevAux(
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_String_Pos_Raw_utf8PrevAux(v_a_4034_, v_a_4035_, v_a_4036_);
    return v___x_4037_;
}
pub unsafe fn l_String_utf8PrevAux___boxed(
    mut v_a_4038_: *mut crate::leanh::LeanObject,
    mut v_a_4039_: *mut crate::leanh::LeanObject,
    mut v_a_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_String_utf8PrevAux(v_a_4038_, v_a_4039_, v_a_4040_);
    crate::leanh::lean_dec(v_a_4040_);
    crate::leanh::lean_dec(v_a_4038_);
    return v_res_4041_;
}
pub unsafe fn l_String_Pos_Raw_prev___boxed(
    mut v_a_00___x40___internal___hyg_4044_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ = lean_string_utf8_prev(
        v_a_00___x40___internal___hyg_4044_,
        v_a_00___x40___internal___hyg_4045_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4045_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_4044_);
    return v_res_4046_;
}
pub unsafe fn l_String_prev___boxed(
    mut v_a_00___x40___internal___hyg_4049_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ = lean_string_utf8_prev(
        v_a_00___x40___internal___hyg_4049_,
        v_a_00___x40___internal___hyg_4050_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4050_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_4049_);
    return v_res_4051_;
}
pub unsafe fn l_String_Pos_Raw_atEnd___boxed(
    mut v_a_00___x40___internal___hyg_4054_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4056_: u8 = 0;
    let mut v_r_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4056_ = lean_string_utf8_at_end(
        v_a_00___x40___internal___hyg_4054_,
        v_a_00___x40___internal___hyg_4055_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4055_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_4054_);
    v_r_4057_ = crate::leanh::lean_box((v_res_4056_) as usize);
    return v_r_4057_;
}
pub unsafe fn l_String_atEnd___boxed(
    mut v_a_00___x40___internal___hyg_4060_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4062_: u8 = 0;
    let mut v_r_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = lean_string_utf8_at_end(
        v_a_00___x40___internal___hyg_4060_,
        v_a_00___x40___internal___hyg_4061_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4061_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_4060_);
    v_r_4063_ = crate::leanh::lean_box((v_res_4062_) as usize);
    return v_r_4063_;
}
pub unsafe fn l_String_Pos_Raw_get_x27___boxed(
    mut v_s_4067_: *mut crate::leanh::LeanObject,
    mut v_p_4068_: *mut crate::leanh::LeanObject,
    mut v_h_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4070_: u32 = 0;
    let mut v_r_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4070_ = lean_string_utf8_get_fast(v_s_4067_, v_p_4068_);
    crate::leanh::lean_dec(v_p_4068_);
    crate::leanh::lean_dec_ref(v_s_4067_);
    v_r_4071_ = crate::leanh::lean_box_uint32(v_res_4070_);
    return v_r_4071_;
}
pub unsafe fn l_String_get_x27___boxed(
    mut v_s_4075_: *mut crate::leanh::LeanObject,
    mut v_p_4076_: *mut crate::leanh::LeanObject,
    mut v_h_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4078_: u32 = 0;
    let mut v_r_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4078_ = lean_string_utf8_get_fast(v_s_4075_, v_p_4076_);
    crate::leanh::lean_dec(v_p_4076_);
    crate::leanh::lean_dec_ref(v_s_4075_);
    v_r_4079_ = crate::leanh::lean_box_uint32(v_res_4078_);
    return v_r_4079_;
}
pub unsafe fn l_String_Pos_Raw_next_x27___boxed(
    mut v_s_4083_: *mut crate::leanh::LeanObject,
    mut v_p_4084_: *mut crate::leanh::LeanObject,
    mut v_h_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = lean_string_utf8_next_fast(v_s_4083_, v_p_4084_);
    crate::leanh::lean_dec(v_p_4084_);
    crate::leanh::lean_dec_ref(v_s_4083_);
    return v_res_4086_;
}
pub unsafe fn l_String_next_x27___boxed(
    mut v_s_4090_: *mut crate::leanh::LeanObject,
    mut v_p_4091_: *mut crate::leanh::LeanObject,
    mut v_h_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4093_ = lean_string_utf8_next_fast(v_s_4090_, v_p_4091_);
    crate::leanh::lean_dec(v_p_4091_);
    crate::leanh::lean_dec_ref(v_s_4090_);
    return v_res_4093_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(
    mut v_x_4094_: *mut crate::leanh::LeanObject,
    mut v_x_4095_: *mut crate::leanh::LeanObject,
    mut v_x_4096_: *mut crate::leanh::LeanObject,
    mut v_h__1_4097_: *mut crate::leanh::LeanObject,
    mut v_h__2_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4094_) == 0 {
        let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4098_);
        v___x_4099_ = crate::leanh::lean_apply_2(v_h__1_4097_, v_x_4095_, v_x_4096_);
        return v___x_4099_;
    } else {
        let mut v_head_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4097_);
        v_head_4100_ = crate::leanh::lean_ctor_get(v_x_4094_, 0);
        crate::leanh::lean_inc(v_head_4100_);
        v_tail_4101_ = crate::leanh::lean_ctor_get(v_x_4094_, 1);
        crate::leanh::lean_inc(v_tail_4101_);
        crate::leanh::lean_dec_ref_known(v_x_4094_, 2);
        v___x_4102_ = crate::leanh::lean_apply_4(
            v_h__2_4098_,
            v_head_4100_,
            v_tail_4101_,
            v_x_4095_,
            v_x_4096_,
        );
        return v___x_4102_;
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(
    mut v_motive_4103_: *mut crate::leanh::LeanObject,
    mut v_x_4104_: *mut crate::leanh::LeanObject,
    mut v_x_4105_: *mut crate::leanh::LeanObject,
    mut v_x_4106_: *mut crate::leanh::LeanObject,
    mut v_h__1_4107_: *mut crate::leanh::LeanObject,
    mut v_h__2_4108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4104_) == 0 {
        let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4108_);
        v___x_4109_ = crate::leanh::lean_apply_2(v_h__1_4107_, v_x_4105_, v_x_4106_);
        return v___x_4109_;
    } else {
        let mut v_head_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4107_);
        v_head_4110_ = crate::leanh::lean_ctor_get(v_x_4104_, 0);
        crate::leanh::lean_inc(v_head_4110_);
        v_tail_4111_ = crate::leanh::lean_ctor_get(v_x_4104_, 1);
        crate::leanh::lean_inc(v_tail_4111_);
        crate::leanh::lean_dec_ref_known(v_x_4104_, 2);
        v___x_4112_ = crate::leanh::lean_apply_4(
            v_h__2_4108_,
            v_head_4110_,
            v_tail_4111_,
            v_x_4105_,
            v_x_4106_,
        );
        return v___x_4112_;
    }
}
pub unsafe fn l_String_firstDiffPos_loop(
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v_b_4114_: *mut crate::leanh::LeanObject,
    mut v_stopPos_4115_: *mut crate::leanh::LeanObject,
    mut v_i_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: u32 = 0;
    let mut v___x_4119_: u32 = 0;
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4117_ = lean_nat_dec_lt(v_i_4116_, v_stopPos_4115_);
                if v___x_4117_ == 0 {
                    return v_i_4116_;
                } else {
                    v___x_4118_ = lean_string_utf8_get(v_a_4113_, v_i_4116_);
                    v___x_4119_ = lean_string_utf8_get(v_b_4114_, v_i_4116_);
                    v___x_4120_ = lean_uint32_dec_eq(v___x_4118_, v___x_4119_);
                    if v___x_4120_ == 0 {
                        return v_i_4116_;
                    } else {
                        v___x_4121_ = lean_string_utf8_next(v_a_4113_, v_i_4116_);
                        crate::leanh::lean_dec(v_i_4116_);
                        v_i_4116_ = v___x_4121_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_firstDiffPos_loop___boxed(
    mut v_a_4123_: *mut crate::leanh::LeanObject,
    mut v_b_4124_: *mut crate::leanh::LeanObject,
    mut v_stopPos_4125_: *mut crate::leanh::LeanObject,
    mut v_i_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_String_firstDiffPos_loop(v_a_4123_, v_b_4124_, v_stopPos_4125_, v_i_4126_);
    crate::leanh::lean_dec(v_stopPos_4125_);
    crate::leanh::lean_dec_ref(v_b_4124_);
    crate::leanh::lean_dec_ref(v_a_4123_);
    return v_res_4127_;
}
pub unsafe fn l_String_firstDiffPos(
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_b_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4134_ = lean_string_utf8_byte_size(v_a_4128_);
                v___x_4135_ = lean_string_utf8_byte_size(v_b_4129_);
                v___x_4136_ = lean_nat_dec_le(v___x_4134_, v___x_4135_);
                if v___x_4136_ == 0 {
                    v___y_4131_ = v___x_4135_;
                    state = 1;
                    continue;
                } else {
                    v___y_4131_ = v___x_4134_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4132_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4133_ =
                    l_String_firstDiffPos_loop(v_a_4128_, v_b_4129_, v___y_4131_, v___x_4132_);
                crate::leanh::lean_dec(v___y_4131_);
                return v___x_4133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_firstDiffPos___boxed(
    mut v_a_4137_: *mut crate::leanh::LeanObject,
    mut v_b_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4139_ = l_String_firstDiffPos(v_a_4137_, v_b_4138_);
    crate::leanh::lean_dec_ref(v_b_4138_);
    crate::leanh::lean_dec_ref(v_a_4137_);
    return v_res_4139_;
}
pub unsafe fn l_String_Pos_Raw_extract_go_u2082(
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v___x_4148_: u8 = 0;
    let mut v___x_4149_: u32 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4140_) == 0 {
                    return v_a_4140_;
                } else {
                    v_head_4143_ = crate::leanh::lean_ctor_get(v_a_4140_, 0);
                    v_tail_4144_ = crate::leanh::lean_ctor_get(v_a_4140_, 1);
                    v_isSharedCheck_4157_ = (!crate::leanh::lean_is_exclusive(v_a_4140_)) as u8;
                    if v_isSharedCheck_4157_ == 0 {
                        v___x_4146_ = v_a_4140_;
                        v_isShared_4147_ = v_isSharedCheck_4157_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4144_);
                        crate::leanh::lean_inc(v_head_4143_);
                        crate::leanh::lean_dec(v_a_4140_);
                        v___x_4146_ = crate::leanh::lean_box(0);
                        v_isShared_4147_ = v_isSharedCheck_4157_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4148_ = lean_nat_dec_eq(v_a_4141_, v_a_4142_);
                if v___x_4148_ == 0 {
                    v___x_4149_ = crate::leanh::lean_unbox_uint32(v_head_4143_);
                    v___x_4150_ = l_Char_utf8Size(v___x_4149_);
                    v___x_4151_ = lean_nat_add(v_a_4141_, v___x_4150_);
                    crate::leanh::lean_dec(v___x_4150_);
                    v___x_4152_ =
                        l_String_Pos_Raw_extract_go_u2082(v_tail_4144_, v___x_4151_, v_a_4142_);
                    crate::leanh::lean_dec(v___x_4151_);
                    if v_isShared_4147_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4146_, 1, v___x_4152_);
                        v___x_4154_ = v___x_4146_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_head_4143_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4152_);
                        v___x_4154_ = v_reuseFailAlloc_4155_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4146_);
                    crate::leanh::lean_dec(v_tail_4144_);
                    crate::leanh::lean_dec(v_head_4143_);
                    v___x_4156_ = crate::leanh::lean_box(0);
                    return v___x_4156_;
                }
            }
            2 => {
                return v___x_4154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_extract_go_u2082___boxed(
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_String_Pos_Raw_extract_go_u2082(v_a_4158_, v_a_4159_, v_a_4160_);
    crate::leanh::lean_dec(v_a_4160_);
    crate::leanh::lean_dec(v_a_4159_);
    return v_res_4161_;
}
pub unsafe fn l_String_Pos_Raw_extract_go_u2081(
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: u32 = 0;
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4162_) == 0 {
                    crate::leanh::lean_dec(v_a_4163_);
                    return v_a_4162_;
                } else {
                    v_head_4166_ = crate::leanh::lean_ctor_get(v_a_4162_, 0);
                    v_tail_4167_ = crate::leanh::lean_ctor_get(v_a_4162_, 1);
                    v___x_4168_ = lean_nat_dec_eq(v_a_4163_, v_a_4164_);
                    if v___x_4168_ == 0 {
                        crate::leanh::lean_inc(v_tail_4167_);
                        crate::leanh::lean_inc(v_head_4166_);
                        crate::leanh::lean_dec_ref_known(v_a_4162_, 2);
                        v___x_4169_ = crate::leanh::lean_unbox_uint32(v_head_4166_);
                        crate::leanh::lean_dec(v_head_4166_);
                        v___x_4170_ = l_Char_utf8Size(v___x_4169_);
                        v___x_4171_ = lean_nat_add(v_a_4163_, v___x_4170_);
                        crate::leanh::lean_dec(v___x_4170_);
                        crate::leanh::lean_dec(v_a_4163_);
                        v_a_4162_ = v_tail_4167_;
                        v_a_4163_ = v___x_4171_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4173_ =
                            l_String_Pos_Raw_extract_go_u2082(v_a_4162_, v_a_4163_, v_a_4165_);
                        crate::leanh::lean_dec(v_a_4163_);
                        return v___x_4173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_extract_go_u2081___boxed(
    mut v_a_4174_: *mut crate::leanh::LeanObject,
    mut v_a_4175_: *mut crate::leanh::LeanObject,
    mut v_a_4176_: *mut crate::leanh::LeanObject,
    mut v_a_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ = l_String_Pos_Raw_extract_go_u2081(v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
    crate::leanh::lean_dec(v_a_4177_);
    crate::leanh::lean_dec(v_a_4176_);
    return v_res_4178_;
}
pub unsafe fn l_String_Pos_Raw_extract___boxed(
    mut v_a_00___x40___internal___hyg_4182_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4183_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = lean_string_utf8_extract(
        v_a_00___x40___internal___hyg_4182_,
        v_a_00___x40___internal___hyg_4183_,
        v_a_00___x40___internal___hyg_4184_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4184_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_4183_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_4182_);
    return v_res_4185_;
}
pub unsafe fn l_String_Pos_Raw_offsetOfPosAux(
    mut v_s_4186_: *mut crate::leanh::LeanObject,
    mut v_pos_4187_: *mut crate::leanh::LeanObject,
    mut v_i_4188_: *mut crate::leanh::LeanObject,
    mut v_offset_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4190_: u8 = 0;
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4190_ = lean_nat_dec_le(v_pos_4187_, v_i_4188_);
                if v___x_4190_ == 0 {
                    v___x_4191_ = lean_string_utf8_at_end(v_s_4186_, v_i_4188_);
                    if v___x_4191_ == 0 {
                        v___x_4192_ = lean_string_utf8_next(v_s_4186_, v_i_4188_);
                        crate::leanh::lean_dec(v_i_4188_);
                        v___x_4193_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4194_ = lean_nat_add(v_offset_4189_, v___x_4193_);
                        crate::leanh::lean_dec(v_offset_4189_);
                        v_i_4188_ = v___x_4192_;
                        v_offset_4189_ = v___x_4194_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4188_);
                        return v_offset_4189_;
                    }
                } else {
                    crate::leanh::lean_dec(v_i_4188_);
                    return v_offset_4189_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_offsetOfPosAux___boxed(
    mut v_s_4196_: *mut crate::leanh::LeanObject,
    mut v_pos_4197_: *mut crate::leanh::LeanObject,
    mut v_i_4198_: *mut crate::leanh::LeanObject,
    mut v_offset_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ =
        l_String_Pos_Raw_offsetOfPosAux(v_s_4196_, v_pos_4197_, v_i_4198_, v_offset_4199_);
    crate::leanh::lean_dec(v_pos_4197_);
    crate::leanh::lean_dec_ref(v_s_4196_);
    return v_res_4200_;
}
pub unsafe fn l_String_Pos_Raw_offsetOfPos(
    mut v_s_4201_: *mut crate::leanh::LeanObject,
    mut v_pos_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4204_ = l_String_Pos_Raw_offsetOfPosAux(v_s_4201_, v_pos_4202_, v___x_4203_, v___x_4203_);
    return v___x_4204_;
}
pub unsafe fn l_String_Pos_Raw_offsetOfPos___boxed(
    mut v_s_4205_: *mut crate::leanh::LeanObject,
    mut v_pos_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_String_Pos_Raw_offsetOfPos(v_s_4205_, v_pos_4206_);
    crate::leanh::lean_dec(v_pos_4206_);
    crate::leanh::lean_dec_ref(v_s_4205_);
    return v_res_4207_;
}
pub unsafe fn l_String_offsetOfPos(
    mut v_s_4208_: *mut crate::leanh::LeanObject,
    mut v_pos_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4211_ = l_String_Pos_Raw_offsetOfPosAux(v_s_4208_, v_pos_4209_, v___x_4210_, v___x_4210_);
    return v___x_4211_;
}
pub unsafe fn l_String_offsetOfPos___boxed(
    mut v_s_4212_: *mut crate::leanh::LeanObject,
    mut v_pos_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_String_offsetOfPos(v_s_4212_, v_pos_4213_);
    crate::leanh::lean_dec(v_pos_4213_);
    crate::leanh::lean_dec_ref(v_s_4212_);
    return v_res_4214_;
}
pub unsafe fn lean_string_offsetofpos(
    mut v_s_4215_: *mut crate::leanh::LeanObject,
    mut v_pos_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4218_ = l_String_Pos_Raw_offsetOfPosAux(v_s_4215_, v_pos_4216_, v___x_4217_, v___x_4217_);
    crate::leanh::lean_dec(v_pos_4216_);
    crate::leanh::lean_dec_ref(v_s_4215_);
    return v___x_4218_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(
    mut v_s1_4219_: *mut crate::leanh::LeanObject,
    mut v_s2_4220_: *mut crate::leanh::LeanObject,
    mut v_off1_4221_: *mut crate::leanh::LeanObject,
    mut v_off2_4222_: *mut crate::leanh::LeanObject,
    mut v_stop1_4223_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: u8 = 0;
    let mut v_c_u2081_4226_: u32 = 0;
    let mut v_c_u2082_4227_: u32 = 0;
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4224_ = lean_nat_dec_lt(v_off1_4221_, v_stop1_4223_);
                if v___x_4224_ == 0 {
                    crate::leanh::lean_dec(v_off2_4222_);
                    crate::leanh::lean_dec(v_off1_4221_);
                    v___x_4225_ = 1;
                    return v___x_4225_;
                } else {
                    v_c_u2081_4226_ = lean_string_utf8_get(v_s1_4219_, v_off1_4221_);
                    v_c_u2082_4227_ = lean_string_utf8_get(v_s2_4220_, v_off2_4222_);
                    v___x_4228_ = lean_uint32_dec_eq(v_c_u2081_4226_, v_c_u2082_4227_);
                    if v___x_4228_ == 0 {
                        crate::leanh::lean_dec(v_off2_4222_);
                        crate::leanh::lean_dec(v_off1_4221_);
                        return v___x_4228_;
                    } else {
                        v___x_4229_ = l_Char_utf8Size(v_c_u2081_4226_);
                        v___x_4230_ = lean_nat_add(v_off1_4221_, v___x_4229_);
                        crate::leanh::lean_dec(v___x_4229_);
                        crate::leanh::lean_dec(v_off1_4221_);
                        v___x_4231_ = l_Char_utf8Size(v_c_u2082_4227_);
                        v___x_4232_ = lean_nat_add(v_off2_4222_, v___x_4231_);
                        crate::leanh::lean_dec(v___x_4231_);
                        crate::leanh::lean_dec(v_off2_4222_);
                        v_off1_4221_ = v___x_4230_;
                        v_off2_4222_ = v___x_4232_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(
    mut v_s1_4234_: *mut crate::leanh::LeanObject,
    mut v_s2_4235_: *mut crate::leanh::LeanObject,
    mut v_off1_4236_: *mut crate::leanh::LeanObject,
    mut v_off2_4237_: *mut crate::leanh::LeanObject,
    mut v_stop1_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4239_: u8 = 0;
    let mut v_r_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(
        v_s1_4234_,
        v_s2_4235_,
        v_off1_4236_,
        v_off2_4237_,
        v_stop1_4238_,
    );
    crate::leanh::lean_dec(v_stop1_4238_);
    crate::leanh::lean_dec_ref(v_s2_4235_);
    crate::leanh::lean_dec_ref(v_s1_4234_);
    v_r_4240_ = crate::leanh::lean_box((v_res_4239_) as usize);
    return v_r_4240_;
}
pub unsafe fn l_String_Pos_Raw_substrEq(
    mut v_s1_4241_: *mut crate::leanh::LeanObject,
    mut v_pos1_4242_: *mut crate::leanh::LeanObject,
    mut v_s2_4243_: *mut crate::leanh::LeanObject,
    mut v_pos2_4244_: *mut crate::leanh::LeanObject,
    mut v_sz_4245_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4247_: u8 = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4250_ = lean_nat_add(v_pos1_4242_, v_sz_4245_);
                v___x_4251_ = lean_string_utf8_byte_size(v_s1_4241_);
                v___x_4252_ = lean_nat_dec_le(v___x_4250_, v___x_4251_);
                crate::leanh::lean_dec(v___x_4250_);
                if v___x_4252_ == 0 {
                    v___y_4247_ = v___x_4252_;
                    state = 1;
                    continue;
                } else {
                    v___x_4253_ = lean_nat_add(v_pos2_4244_, v_sz_4245_);
                    v___x_4254_ = lean_string_utf8_byte_size(v_s2_4243_);
                    v___x_4255_ = lean_nat_dec_le(v___x_4253_, v___x_4254_);
                    crate::leanh::lean_dec(v___x_4253_);
                    v___y_4247_ = v___x_4255_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4247_ == 0 {
                    crate::leanh::lean_dec(v_pos2_4244_);
                    crate::leanh::lean_dec(v_pos1_4242_);
                    return v___y_4247_;
                } else {
                    v___x_4248_ = lean_nat_add(v_pos1_4242_, v_sz_4245_);
                    v___x_4249_ =
                        l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(
                            v_s1_4241_,
                            v_s2_4243_,
                            v_pos1_4242_,
                            v_pos2_4244_,
                            v___x_4248_,
                        );
                    crate::leanh::lean_dec(v___x_4248_);
                    return v___x_4249_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_Raw_substrEq___boxed(
    mut v_s1_4256_: *mut crate::leanh::LeanObject,
    mut v_pos1_4257_: *mut crate::leanh::LeanObject,
    mut v_s2_4258_: *mut crate::leanh::LeanObject,
    mut v_pos2_4259_: *mut crate::leanh::LeanObject,
    mut v_sz_4260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4261_: u8 = 0;
    let mut v_r_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4261_ = l_String_Pos_Raw_substrEq(
        v_s1_4256_,
        v_pos1_4257_,
        v_s2_4258_,
        v_pos2_4259_,
        v_sz_4260_,
    );
    crate::leanh::lean_dec(v_sz_4260_);
    crate::leanh::lean_dec_ref(v_s2_4258_);
    crate::leanh::lean_dec_ref(v_s1_4256_);
    v_r_4262_ = crate::leanh::lean_box((v_res_4261_) as usize);
    return v_r_4262_;
}
pub unsafe fn l_String_substrEq(
    mut v_s1_4263_: *mut crate::leanh::LeanObject,
    mut v_pos1_4264_: *mut crate::leanh::LeanObject,
    mut v_s2_4265_: *mut crate::leanh::LeanObject,
    mut v_pos2_4266_: *mut crate::leanh::LeanObject,
    mut v_sz_4267_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4268_: u8 = 0;
    v___x_4268_ = l_String_Pos_Raw_substrEq(
        v_s1_4263_,
        v_pos1_4264_,
        v_s2_4265_,
        v_pos2_4266_,
        v_sz_4267_,
    );
    return v___x_4268_;
}
pub unsafe fn l_String_substrEq___boxed(
    mut v_s1_4269_: *mut crate::leanh::LeanObject,
    mut v_pos1_4270_: *mut crate::leanh::LeanObject,
    mut v_s2_4271_: *mut crate::leanh::LeanObject,
    mut v_pos2_4272_: *mut crate::leanh::LeanObject,
    mut v_sz_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4274_: u8 = 0;
    let mut v_r_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4274_ = l_String_substrEq(
        v_s1_4269_,
        v_pos1_4270_,
        v_s2_4271_,
        v_pos2_4272_,
        v_sz_4273_,
    );
    crate::leanh::lean_dec(v_sz_4273_);
    crate::leanh::lean_dec_ref(v_s2_4271_);
    crate::leanh::lean_dec_ref(v_s1_4269_);
    v_r_4275_ = crate::leanh::lean_box((v_res_4274_) as usize);
    return v_r_4275_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_4276_: *mut crate::leanh::LeanObject,
    mut v_x_4277_: *mut crate::leanh::LeanObject,
    mut v_h__1_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4279_ = crate::leanh::lean_apply_2(v_h__1_4278_, v_x_4276_, v_x_4277_);
    return v___x_4279_;
}
pub unsafe fn l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_4280_: *mut crate::leanh::LeanObject,
    mut v_x_4281_: *mut crate::leanh::LeanObject,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
    mut v_h__1_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = crate::leanh::lean_apply_2(v_h__1_4283_, v_x_4281_, v_x_4282_);
    return v___x_4284_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Decode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_String_instLT = _init_l_String_instLT();
    crate::leanh::lean_mark_persistent(l_String_instLT);
    l_String_instLE = _init_l_String_instLE();
    crate::leanh::lean_mark_persistent(l_String_instLE);
    l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1 =
        _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Decode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Basic(builtin);
}
