// Lean compiler output
// Module: Init.System.Uri
// Imports: Init.System.FilePath Init.Data.String.TakeDrop Init.Data.String.Modify Init.Data.String.Search Init.Omega Init.System.Platform Init.While Init.Data.String.Length Init.Data.Iterators.Combinators.Take
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_byte_array_fget, lean_byte_array_push,
    lean_byte_array_size, lean_byte_array_uget, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_append,
    lean_string_from_utf8_unchecked, lean_string_memcmp, lean_string_push, lean_string_to_utf8,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set,
    lean_string_validate_utf8, lean_uint8_add, lean_uint8_dec_eq, lean_uint8_dec_le,
    lean_uint8_mod, lean_uint8_of_nat, lean_uint8_shift_left, lean_uint8_shift_right,
    lean_uint8_sub, lean_uint8_to_nat, lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint32_dec_lt, lean_uint32_to_nat, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Take::{
    initialize_Init_Data_Iterators_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Take,
};
use crate::r#gen::Init::Data::Repr::l_hexDigitRepr;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_ByteArray_empty, l_Char_utf8Size};
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, l_System_FilePath_normalize,
    runtime_initialize_Init_System_FilePath,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
pub static mut l_System_Uri_UriEscape_zero: u8 = 0;
pub static mut l_System_Uri_UriEscape_nine: u8 = 0;
pub static mut l_System_Uri_UriEscape_lettera: u8 = 0;
pub static mut l_System_Uri_UriEscape_letterf: u8 = 0;
pub static mut l_System_Uri_UriEscape_letterA: u8 = 0;
pub static mut l_System_Uri_UriEscape_letterF: u8 = 0;
pub static l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0_value:
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
static mut l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_System_Uri_UriEscape_decodeUri___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_Uri_UriEscape_decodeUri___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_System_Uri_UriEscape_decodeUri___closed__1_value: leanh::LeanStringObject<23> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_System_Uri_UriEscape_decodeUri___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_UriEscape_decodeUri___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_System_Uri_UriEscape_decodeUri___closed__2_value: leanh::LeanStringObject<17> =
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
            83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0,
        ],
    };
static mut l_System_Uri_UriEscape_decodeUri___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_UriEscape_decodeUri___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_System_Uri_UriEscape_decodeUri___closed__3_value: leanh::LeanStringObject<21> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_System_Uri_UriEscape_decodeUri___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_UriEscape_decodeUri___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_System_Uri_UriEscape_decodeUri___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_Uri_UriEscape_decodeUri___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_Uri_UriEscape_rfc3986ReservedChars: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [37, 0]};
static mut l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value
) as *mut leanh::LeanObject;
pub static l_System_Uri_pathToUri___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [102, 105, 108, 101, 58, 47, 47, 47, 0],
    };
static mut l_System_Uri_pathToUri___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_pathToUri___closed__0_value) as *mut leanh::LeanObject;
pub static l_System_Uri_pathToUri___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [47, 0],
    };
static mut l_System_Uri_pathToUri___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_pathToUri___closed__1_value) as *mut leanh::LeanObject;
static mut l_System_Uri_pathToUri___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_Uri_pathToUri___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_System_Uri_pathToUri___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [102, 105, 108, 101, 58, 47, 47, 0],
    };
static mut l_System_Uri_pathToUri___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_System_Uri_pathToUri___closed__3_value) as *mut leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_System_Uri_UriEscape_zero() -> u8 {
    let mut v___x_705_: u8 = 0;
    v___x_705_ = 48;
    return v___x_705_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_nine() -> u8 {
    let mut v___x_706_: u8 = 0;
    v___x_706_ = 57;
    return v___x_706_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_lettera() -> u8 {
    let mut v___x_707_: u8 = 0;
    v___x_707_ = 97;
    return v___x_707_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_letterf() -> u8 {
    let mut v___x_708_: u8 = 0;
    v___x_708_ = 102;
    return v___x_708_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_letterA() -> u8 {
    let mut v___x_709_: u8 = 0;
    v___x_709_ = 65;
    return v___x_709_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_letterF() -> u8 {
    let mut v___x_710_: u8 = 0;
    v___x_710_ = 70;
    return v___x_710_;
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(
    mut v_c_711_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_713_: u8 = 0;
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: u8 = 0;
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: u8 = 0;
    let mut v___x_729_: u8 = 0;
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: u8 = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: u8 = 0;
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_734_ = 48;
                v___x_735_ = lean_uint8_dec_le(v___x_734_, v_c_711_);
                if v___x_735_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_736_ = 57;
                    v___x_737_ = lean_uint8_dec_le(v_c_711_, v___x_736_);
                    if v___x_737_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_738_ = lean_uint8_sub(v_c_711_, v___x_734_);
                        v___x_739_ = leanh::lean_box((v___x_738_) as usize);
                        v___x_740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_740_, 0, v___x_739_);
                        return v___x_740_;
                    }
                }
            }
            1 => {
                v___x_713_ = 65;
                v___x_714_ = lean_uint8_dec_le(v___x_713_, v_c_711_);
                if v___x_714_ == 0 {
                    v___x_715_ = leanh::lean_box(0);
                    return v___x_715_;
                } else {
                    v___x_716_ = 70;
                    v___x_717_ = lean_uint8_dec_le(v_c_711_, v___x_716_);
                    if v___x_717_ == 0 {
                        v___x_718_ = leanh::lean_box(0);
                        return v___x_718_;
                    } else {
                        v___x_719_ = lean_uint8_sub(v_c_711_, v___x_713_);
                        v___x_720_ = 10;
                        v___x_721_ = lean_uint8_add(v___x_719_, v___x_720_);
                        v___x_722_ = leanh::lean_box((v___x_721_) as usize);
                        v___x_723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_723_, 0, v___x_722_);
                        return v___x_723_;
                    }
                }
            }
            2 => {
                v___x_725_ = 97;
                v___x_726_ = lean_uint8_dec_le(v___x_725_, v_c_711_);
                if v___x_726_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_727_ = 102;
                    v___x_728_ = lean_uint8_dec_le(v_c_711_, v___x_727_);
                    if v___x_728_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_729_ = lean_uint8_sub(v_c_711_, v___x_725_);
                        v___x_730_ = 10;
                        v___x_731_ = lean_uint8_add(v___x_729_, v___x_730_);
                        v___x_732_ = leanh::lean_box((v___x_731_) as usize);
                        v___x_733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_733_, 0, v___x_732_);
                        return v___x_733_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(
    mut v_c_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_742_: u8 = 0;
    let mut v_res_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_742_ = (leanh::lean_unbox(v_c_741_) as u8);
    v_res_743_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(
        v_c_boxed_742_,
    );
    return v_res_743_;
}
pub unsafe fn l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(
    mut v_msg_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0;
    v___x_747_ = lean_panic_fn_borrowed(v___x_746_, v_msg_745_);
    return v___x_747_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(
    mut v_len_748_: *mut leanh::LeanObject,
    mut v_rawBytes_749_: *mut leanh::LeanObject,
    mut v_a_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_755_: u8 = 0;
    let mut v___x_756_: u8 = 0;
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_percent_760_: u8 = 0;
    let mut v___x_761_: u8 = 0;
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: u8 = 0;
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: u8 = 0;
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: u8 = 0;
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_751_ = leanh::lean_ctor_get(v_a_750_, 0);
                v_snd_752_ = leanh::lean_ctor_get(v_a_750_, 1);
                v_isSharedCheck_810_ = (!leanh::lean_is_exclusive(v_a_750_)) as u8;
                if v_isSharedCheck_810_ == 0 {
                    v___x_754_ = v_a_750_;
                    v_isShared_755_ = v_isSharedCheck_810_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_752_);
                    leanh::lean_inc(v_fst_751_);
                    leanh::lean_dec(v_a_750_);
                    v___x_754_ = leanh::lean_box(0);
                    v_isShared_755_ = v_isSharedCheck_810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_756_ = lean_nat_dec_lt(v_snd_752_, v_len_748_);
                if v___x_756_ == 0 {
                    if v_isShared_755_ == 0 {
                        v___x_758_ = v___x_754_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_759_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_759_, 0, v_fst_751_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_752_);
                        v___x_758_ = v_reuseFailAlloc_759_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_percent_760_ = 37;
                    v___x_761_ = lean_byte_array_fget(v_rawBytes_749_, v_snd_752_);
                    v___x_770_ = lean_uint8_dec_eq(v___x_761_, v_percent_760_);
                    if v___x_770_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_771_ = leanh::lean_unsigned_to_nat(1);
                        v___x_772_ = lean_nat_add(v_snd_752_, v___x_771_);
                        v___x_773_ = lean_nat_dec_lt(v___x_772_, v_len_748_);
                        if v___x_773_ == 0 {
                            leanh::lean_dec(v___x_772_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_754_);
                            v___x_774_ = lean_byte_array_fget(v_rawBytes_749_, v___x_772_);
                            leanh::lean_dec(v___x_772_);
                            v___x_775_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_774_);
                            if leanh::lean_obj_tag(v___x_775_) == 1 {
                                v_val_776_ = leanh::lean_ctor_get(v___x_775_, 0);
                                leanh::lean_inc(v_val_776_);
                                leanh::lean_dec_ref_known(v___x_775_, 1);
                                v___x_777_ = leanh::lean_unsigned_to_nat(2);
                                v___x_778_ = lean_nat_add(v_snd_752_, v___x_777_);
                                v___x_779_ = lean_nat_dec_lt(v___x_778_, v_len_748_);
                                if v___x_779_ == 0 {
                                    leanh::lean_dec(v_val_776_);
                                    leanh::lean_dec(v_snd_752_);
                                    v___x_780_ = lean_byte_array_push(v_fst_751_, v___x_761_);
                                    v___x_781_ = lean_byte_array_push(v___x_780_, v___x_774_);
                                    v___x_782_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_782_, 0, v___x_781_);
                                    leanh::lean_ctor_set(v___x_782_, 1, v___x_778_);
                                    v_a_750_ = v___x_782_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_784_ = lean_byte_array_fget(v_rawBytes_749_, v___x_778_);
                                    leanh::lean_dec(v___x_778_);
                                    v___x_785_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_784_);
                                    if leanh::lean_obj_tag(v___x_785_) == 1 {
                                        v_val_786_ = leanh::lean_ctor_get(v___x_785_, 0);
                                        leanh::lean_inc(v_val_786_);
                                        leanh::lean_dec_ref_known(v___x_785_, 1);
                                        v___x_787_ = 4;
                                        v___x_788_ = (leanh::lean_unbox(v_val_776_) as u8);
                                        leanh::lean_dec(v_val_776_);
                                        v___x_789_ = lean_uint8_shift_left(v___x_788_, v___x_787_);
                                        v___x_790_ = (leanh::lean_unbox(v_val_786_) as u8);
                                        leanh::lean_dec(v_val_786_);
                                        v___x_791_ = lean_uint8_add(v___x_789_, v___x_790_);
                                        v___x_792_ = lean_byte_array_push(v_fst_751_, v___x_791_);
                                        v___x_793_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_794_ = lean_nat_add(v_snd_752_, v___x_793_);
                                        leanh::lean_dec(v_snd_752_);
                                        v___x_795_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_795_, 0, v___x_792_);
                                        leanh::lean_ctor_set(v___x_795_, 1, v___x_794_);
                                        v_a_750_ = v___x_795_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_785_);
                                        leanh::lean_dec(v_val_776_);
                                        v___x_797_ = lean_byte_array_push(v_fst_751_, v___x_761_);
                                        v___x_798_ = lean_byte_array_push(v___x_797_, v___x_774_);
                                        v___x_799_ = lean_byte_array_push(v___x_798_, v___x_784_);
                                        v___x_800_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_801_ = lean_nat_add(v_snd_752_, v___x_800_);
                                        leanh::lean_dec(v_snd_752_);
                                        v___x_802_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_802_, 0, v___x_799_);
                                        leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
                                        v_a_750_ = v___x_802_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_775_);
                                v___x_804_ = lean_byte_array_push(v_fst_751_, v___x_761_);
                                v___x_805_ = lean_byte_array_push(v___x_804_, v___x_774_);
                                v___x_806_ = leanh::lean_unsigned_to_nat(2);
                                v___x_807_ = lean_nat_add(v_snd_752_, v___x_806_);
                                leanh::lean_dec(v_snd_752_);
                                v___x_808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_808_, 0, v___x_805_);
                                leanh::lean_ctor_set(v___x_808_, 1, v___x_807_);
                                v_a_750_ = v___x_808_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_758_;
            }
            3 => {
                v___x_763_ = lean_byte_array_push(v_fst_751_, v___x_761_);
                v___x_764_ = leanh::lean_unsigned_to_nat(1);
                v___x_765_ = lean_nat_add(v_snd_752_, v___x_764_);
                leanh::lean_dec(v_snd_752_);
                if v_isShared_755_ == 0 {
                    leanh::lean_ctor_set(v___x_754_, 1, v___x_765_);
                    leanh::lean_ctor_set(v___x_754_, 0, v___x_763_);
                    v___x_767_ = v___x_754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_769_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_765_);
                    v___x_767_ = v_reuseFailAlloc_769_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_750_ = v___x_767_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg___boxed(
    mut v_len_811_: *mut leanh::LeanObject,
    mut v_rawBytes_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_811_, v_rawBytes_812_, v_a_813_);
    leanh::lean_dec_ref(v_rawBytes_812_);
    leanh::lean_dec(v_len_811_);
    return v_res_814_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_decodeUri___closed__0() -> *mut leanh::LeanObject
{
    let mut v_i_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decoded_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_815_ = leanh::lean_unsigned_to_nat(0);
    v_decoded_816_ = l_ByteArray_empty;
    v___x_817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_817_, 0, v_decoded_816_);
    leanh::lean_ctor_set(v___x_817_, 1, v_i_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_decodeUri___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_System_Uri_UriEscape_decodeUri___closed__3;
    v___x_822_ = leanh::lean_unsigned_to_nat(46);
    v___x_823_ = leanh::lean_unsigned_to_nat(193);
    v___x_824_ = l_System_Uri_UriEscape_decodeUri___closed__2;
    v___x_825_ = l_System_Uri_UriEscape_decodeUri___closed__1;
    v___x_826_ =
        l_mkPanicMessageWithDecl(v___x_825_, v___x_824_, v___x_823_, v___x_822_, v___x_821_);
    return v___x_826_;
}
pub unsafe fn l_System_Uri_UriEscape_decodeUri(
    mut v_uri_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rawBytes_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: u8 = 0;
    v_rawBytes_828_ = lean_string_to_utf8(v_uri_827_);
    v_len_829_ = lean_byte_array_size(v_rawBytes_828_);
    v___x_830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_decodeUri___closed__0),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_decodeUri___closed__0_once),
        _init_l_System_Uri_UriEscape_decodeUri___closed__0,
    );
    v___x_831_ = l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_829_, v_rawBytes_828_, v___x_830_);
    leanh::lean_dec_ref(v_rawBytes_828_);
    v_fst_832_ = leanh::lean_ctor_get(v___x_831_, 0);
    leanh::lean_inc(v_fst_832_);
    leanh::lean_dec_ref(v___x_831_);
    v___x_833_ = lean_string_validate_utf8(v_fst_832_);
    if v___x_833_ == 0 {
        let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_832_);
        v___x_834_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_System_Uri_UriEscape_decodeUri___closed__4),
            core::ptr::addr_of_mut!(l_System_Uri_UriEscape_decodeUri___closed__4_once),
            _init_l_System_Uri_UriEscape_decodeUri___closed__4,
        );
        v___x_835_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(v___x_834_);
        return v___x_835_;
    } else {
        let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_836_ = lean_string_from_utf8_unchecked(v_fst_832_);
        return v___x_836_;
    }
}
pub unsafe fn l_System_Uri_UriEscape_decodeUri___boxed(
    mut v_uri_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_System_Uri_UriEscape_decodeUri(v_uri_837_);
    leanh::lean_dec_ref(v_uri_837_);
    return v_res_838_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(
    mut v_len_839_: *mut leanh::LeanObject,
    mut v_rawBytes_840_: *mut leanh::LeanObject,
    mut v_inst_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_839_, v_rawBytes_840_, v_a_842_);
    return v___x_843_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(
    mut v_len_844_: *mut leanh::LeanObject,
    mut v_rawBytes_845_: *mut leanh::LeanObject,
    mut v_inst_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ =
        l___private_Init_While_0__whileM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(
            v_len_844_,
            v_rawBytes_845_,
            v_inst_846_,
            v_a_847_,
        );
    leanh::lean_dec_ref(v_rawBytes_845_);
    leanh::lean_dec(v_len_844_);
    return v_res_848_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_849_: u32 = 0;
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = 32;
    v___x_850_ = leanh::lean_box_uint32(v___x_849_);
    return v___x_850_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = leanh::lean_box(0);
    v___x_852_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
    v___x_853_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_853_, 0, v___x_852_);
    leanh::lean_ctor_set(v___x_853_, 1, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_854_: u32 = 0;
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = 37;
    v___x_855_ = leanh::lean_box_uint32(v___x_854_);
    return v___x_855_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0,
    );
    v___x_857_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
    v___x_858_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_858_, 0, v___x_857_);
    leanh::lean_ctor_set(v___x_858_, 1, v___x_856_);
    return v___x_858_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_859_: u32 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = 42;
    v___x_860_ = leanh::lean_box_uint32(v___x_859_);
    return v___x_860_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1,
    );
    v___x_862_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
    v___x_863_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
    leanh::lean_ctor_set(v___x_863_, 1, v___x_861_);
    return v___x_863_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_864_: u32 = 0;
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = 41;
    v___x_865_ = leanh::lean_box_uint32(v___x_864_);
    return v___x_865_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2,
    );
    v___x_867_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
    v___x_868_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_868_, 0, v___x_867_);
    leanh::lean_ctor_set(v___x_868_, 1, v___x_866_);
    return v___x_868_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_869_: u32 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = 40;
    v___x_870_ = leanh::lean_box_uint32(v___x_869_);
    return v___x_870_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3,
    );
    v___x_872_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
    v___x_873_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
    leanh::lean_ctor_set(v___x_873_, 1, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_874_: u32 = 0;
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = 39;
    v___x_875_ = leanh::lean_box_uint32(v___x_874_);
    return v___x_875_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4,
    );
    v___x_877_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
    v___x_878_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
    leanh::lean_ctor_set(v___x_878_, 1, v___x_876_);
    return v___x_878_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_879_: u32 = 0;
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = 33;
    v___x_880_ = leanh::lean_box_uint32(v___x_879_);
    return v___x_880_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5,
    );
    v___x_882_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
    v___x_883_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_883_, 0, v___x_882_);
    leanh::lean_ctor_set(v___x_883_, 1, v___x_881_);
    return v___x_883_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_884_: u32 = 0;
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = 44;
    v___x_885_ = leanh::lean_box_uint32(v___x_884_);
    return v___x_885_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6,
    );
    v___x_887_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
    v___x_888_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
    leanh::lean_ctor_set(v___x_888_, 1, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_889_: u32 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = 36;
    v___x_890_ = leanh::lean_box_uint32(v___x_889_);
    return v___x_890_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7,
    );
    v___x_892_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
    v___x_893_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_893_, 0, v___x_892_);
    leanh::lean_ctor_set(v___x_893_, 1, v___x_891_);
    return v___x_893_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_894_: u32 = 0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = 43;
    v___x_895_ = leanh::lean_box_uint32(v___x_894_);
    return v___x_895_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8,
    );
    v___x_897_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
    v___x_898_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_898_, 0, v___x_897_);
    leanh::lean_ctor_set(v___x_898_, 1, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_899_: u32 = 0;
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = 61;
    v___x_900_ = leanh::lean_box_uint32(v___x_899_);
    return v___x_900_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9,
    );
    v___x_902_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
    v___x_903_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_903_, 0, v___x_902_);
    leanh::lean_ctor_set(v___x_903_, 1, v___x_901_);
    return v___x_903_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_904_: u32 = 0;
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = 38;
    v___x_905_ = leanh::lean_box_uint32(v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10,
    );
    v___x_907_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
    v___x_908_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_908_, 0, v___x_907_);
    leanh::lean_ctor_set(v___x_908_, 1, v___x_906_);
    return v___x_908_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_909_: u32 = 0;
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = 64;
    v___x_910_ = leanh::lean_box_uint32(v___x_909_);
    return v___x_910_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11,
    );
    v___x_912_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
    v___x_913_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_913_, 0, v___x_912_);
    leanh::lean_ctor_set(v___x_913_, 1, v___x_911_);
    return v___x_913_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_914_: u32 = 0;
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = 93;
    v___x_915_ = leanh::lean_box_uint32(v___x_914_);
    return v___x_915_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_916_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12,
    );
    v___x_917_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
    v___x_918_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_918_, 0, v___x_917_);
    leanh::lean_ctor_set(v___x_918_, 1, v___x_916_);
    return v___x_918_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_919_: u32 = 0;
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = 91;
    v___x_920_ = leanh::lean_box_uint32(v___x_919_);
    return v___x_920_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13,
    );
    v___x_922_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
    v___x_923_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    leanh::lean_ctor_set(v___x_923_, 1, v___x_921_);
    return v___x_923_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_924_: u32 = 0;
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = 35;
    v___x_925_ = leanh::lean_box_uint32(v___x_924_);
    return v___x_925_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14,
    );
    v___x_927_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
    v___x_928_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_928_, 0, v___x_927_);
    leanh::lean_ctor_set(v___x_928_, 1, v___x_926_);
    return v___x_928_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_929_: u32 = 0;
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_929_ = 63;
    v___x_930_ = leanh::lean_box_uint32(v___x_929_);
    return v___x_930_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15,
    );
    v___x_932_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
    v___x_933_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_933_, 0, v___x_932_);
    leanh::lean_ctor_set(v___x_933_, 1, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_934_: u32 = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = 58;
    v___x_935_ = leanh::lean_box_uint32(v___x_934_);
    return v___x_935_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16,
    );
    v___x_937_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
    v___x_938_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_938_, 0, v___x_937_);
    leanh::lean_ctor_set(v___x_938_, 1, v___x_936_);
    return v___x_938_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_939_: u32 = 0;
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = 59;
    v___x_940_ = leanh::lean_box_uint32(v___x_939_);
    return v___x_940_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17,
    );
    v___x_942_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
    v___x_943_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_943_, 0, v___x_942_);
    leanh::lean_ctor_set(v___x_943_, 1, v___x_941_);
    return v___x_943_;
}
pub unsafe fn _init_l_System_Uri_UriEscape_rfc3986ReservedChars() -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18),
        core::ptr::addr_of_mut!(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once),
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18,
    );
    return v___x_944_;
}
pub unsafe fn l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(
    mut v_s_945_: *mut leanh::LeanObject,
    mut v_p_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_948_: u32 = 0;
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: u32 = 0;
    let mut v___x_956_: u32 = 0;
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: u32 = 0;
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: u32 = 0;
    let mut v___x_961_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_953_ = lean_string_utf8_byte_size(v_s_945_);
                v___x_954_ = lean_nat_dec_eq(v_p_946_, v___x_953_);
                if v___x_954_ == 0 {
                    v___x_955_ = lean_string_utf8_get_fast(v_s_945_, v_p_946_);
                    v___x_956_ = 97;
                    v___x_957_ = lean_uint32_dec_le(v___x_956_, v___x_955_);
                    if v___x_957_ == 0 {
                        v___y_948_ = v___x_955_;
                        state = 1;
                        continue;
                    } else {
                        v___x_958_ = 122;
                        v___x_959_ = lean_uint32_dec_le(v___x_955_, v___x_958_);
                        if v___x_959_ == 0 {
                            v___y_948_ = v___x_955_;
                            state = 1;
                            continue;
                        } else {
                            v___x_960_ = 4294967264;
                            v___x_961_ = lean_uint32_add(v___x_955_, v___x_960_);
                            v___y_948_ = v___x_961_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_p_946_);
                    return v_s_945_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_946_);
                v___x_949_ = lean_string_utf8_set(v_s_945_, v_p_946_, v___y_948_);
                v___x_950_ = l_Char_utf8Size(v___y_948_);
                v___x_951_ = lean_nat_add(v_p_946_, v___x_950_);
                leanh::lean_dec(v___x_950_);
                leanh::lean_dec(v_p_946_);
                v_s_945_ = v___x_949_;
                v_p_946_ = v___x_951_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(
    mut v_c_962_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: u8 = 0;
    let mut v_d2_965_: u8 = 0;
    let mut v_d1_966_: u8 = 0;
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = 16;
    v___x_964_ = 4;
    v_d2_965_ = lean_uint8_shift_right(v_c_962_, v___x_964_);
    v_d1_966_ = lean_uint8_mod(v_c_962_, v___x_963_);
    v___x_967_ = lean_uint8_to_nat(v_d2_965_);
    v___x_968_ = l_hexDigitRepr(v___x_967_);
    v___x_969_ = lean_uint8_to_nat(v_d1_966_);
    v___x_970_ = l_hexDigitRepr(v___x_969_);
    v___x_971_ = lean_string_append(v___x_968_, v___x_970_);
    leanh::lean_dec_ref(v___x_970_);
    v___x_972_ = leanh::lean_unsigned_to_nat(0);
    v___x_973_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_971_, v___x_972_);
    return v___x_973_;
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(
    mut v_c_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_975_: u8 = 0;
    let mut v_res_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_975_ = (leanh::lean_unbox(v_c_974_) as u8);
    v_res_976_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(
        v_c_boxed_975_,
    );
    return v_res_976_;
}
pub unsafe fn l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(
    mut v_a_977_: u32,
    mut v_x_978_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_979_: u8 = 0;
    let mut v_head_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u32 = 0;
    let mut v___x_983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_978_) == 0 {
                    v___x_979_ = 0;
                    return v___x_979_;
                } else {
                    v_head_980_ = leanh::lean_ctor_get(v_x_978_, 0);
                    v_tail_981_ = leanh::lean_ctor_get(v_x_978_, 1);
                    v___x_982_ = leanh::lean_unbox_uint32(v_head_980_);
                    v___x_983_ = lean_uint32_dec_eq(v_a_977_, v___x_982_);
                    if v___x_983_ == 0 {
                        v_x_978_ = v_tail_981_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_983_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(
    mut v_a_985_: *mut leanh::LeanObject,
    mut v_x_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_987_: u32 = 0;
    let mut v_res_988_: u8 = 0;
    let mut v_r_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_987_ = leanh::lean_unbox_uint32(v_a_985_);
    leanh::lean_dec(v_a_985_);
    v_res_988_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(
        v_a_boxed_987_,
        v_x_986_,
    );
    leanh::lean_dec(v_x_986_);
    v_r_989_ = leanh::lean_box((v_res_988_) as usize);
    return v_r_989_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(
    mut v_as_991_: *mut leanh::LeanObject,
    mut v_i_992_: usize,
    mut v_stop_993_: usize,
    mut v_b_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: usize = 0;
    let mut v___x_1002_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_995_ = lean_usize_dec_eq(v_i_992_, v_stop_993_);
                if v___x_995_ == 0 {
                    v___x_996_ = lean_byte_array_uget(v_as_991_, v_i_992_);
                    v___x_997_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0;
                    v___x_998_ = lean_string_append(v_b_994_, v___x_997_);
                    v___x_999_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_996_);
                    v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
                    leanh::lean_dec_ref(v___x_999_);
                    v___x_1001_ = 1usize;
                    v___x_1002_ = lean_usize_add(v_i_992_, v___x_1001_);
                    v_i_992_ = v___x_1002_;
                    v_b_994_ = v___x_1000_;
                    state = 0;
                    continue;
                } else {
                    return v_b_994_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(
    mut v_as_1004_: *mut leanh::LeanObject,
    mut v_i_1005_: *mut leanh::LeanObject,
    mut v_stop_1006_: *mut leanh::LeanObject,
    mut v_b_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1008_: usize = 0;
    let mut v_stop_boxed_1009_: usize = 0;
    let mut v_res_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1008_ = leanh::lean_unbox_usize(v_i_1005_);
    leanh::lean_dec(v_i_1005_);
    v_stop_boxed_1009_ = leanh::lean_unbox_usize(v_stop_1006_);
    leanh::lean_dec(v_stop_1006_);
    v_res_1010_ =
        l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(
            v_as_1004_,
            v_i_boxed_1008_,
            v_stop_boxed_1009_,
            v_b_1007_,
        );
    leanh::lean_dec_ref(v_as_1004_);
    return v_res_1010_;
}
pub unsafe fn l_System_Uri_UriEscape_uriEscapeAsciiChar(
    mut v_c_1011_: u32,
) -> *mut leanh::LeanObject {
    let mut v___y_1013_: u8 = 0;
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: usize = 0;
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: usize = 0;
    let mut v___x_1028_: usize = 0;
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1039_: u32 = 0;
    let mut v___x_1040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1037_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
                v___x_1038_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(
                    v_c_1011_,
                    v___x_1037_,
                );
                if v___x_1038_ == 0 {
                    v___x_1039_ = 32;
                    v___x_1040_ = lean_uint32_dec_lt(v_c_1011_, v___x_1039_);
                    v___y_1013_ = v___x_1040_;
                    state = 1;
                    continue;
                } else {
                    v___y_1013_ = v___x_1038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1013_ == 0 {
                    v___x_1014_ = lean_uint32_to_nat(v_c_1011_);
                    v___x_1015_ = leanh::lean_unsigned_to_nat(127);
                    v___x_1016_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
                    leanh::lean_dec(v___x_1014_);
                    if v___x_1016_ == 0 {
                        v___x_1017_ =
                            l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0;
                        v___x_1018_ = lean_string_push(v___x_1017_, v_c_1011_);
                        v___x_1019_ = lean_string_to_utf8(v___x_1018_);
                        leanh::lean_dec_ref(v___x_1018_);
                        v___x_1020_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1021_ = lean_byte_array_size(v___x_1019_);
                        v___x_1022_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
                        if v___x_1022_ == 0 {
                            leanh::lean_dec_ref(v___x_1019_);
                            return v___x_1017_;
                        } else {
                            v___x_1023_ = lean_nat_dec_le(v___x_1021_, v___x_1021_);
                            if v___x_1023_ == 0 {
                                if v___x_1022_ == 0 {
                                    leanh::lean_dec_ref(v___x_1019_);
                                    return v___x_1017_;
                                } else {
                                    v___x_1024_ = 0usize;
                                    v___x_1025_ = lean_usize_of_nat(v___x_1021_);
                                    v___x_1026_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_1019_, v___x_1024_, v___x_1025_, v___x_1017_);
                                    leanh::lean_dec_ref(v___x_1019_);
                                    return v___x_1026_;
                                }
                            } else {
                                v___x_1027_ = 0usize;
                                v___x_1028_ = lean_usize_of_nat(v___x_1021_);
                                v___x_1029_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_1019_, v___x_1027_, v___x_1028_, v___x_1017_);
                                leanh::lean_dec_ref(v___x_1019_);
                                return v___x_1029_;
                            }
                        }
                    } else {
                        v___x_1030_ =
                            l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0;
                        v___x_1031_ = lean_string_push(v___x_1030_, v_c_1011_);
                        return v___x_1031_;
                    }
                } else {
                    v___x_1032_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0;
                    v___x_1033_ = lean_uint32_to_nat(v_c_1011_);
                    v___x_1034_ = lean_uint8_of_nat(v___x_1033_);
                    leanh::lean_dec(v___x_1033_);
                    v___x_1035_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_1034_);
                    v___x_1036_ = lean_string_append(v___x_1032_, v___x_1035_);
                    leanh::lean_dec_ref(v___x_1035_);
                    return v___x_1036_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(
    mut v_c_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1042_: u32 = 0;
    let mut v_res_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1042_ = leanh::lean_unbox_uint32(v_c_1041_);
    leanh::lean_dec(v_c_1041_);
    v_res_1043_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_boxed_1042_);
    return v_res_1043_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(
    mut v___x_1044_: *mut leanh::LeanObject,
    mut v_uri_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_b_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: u32 = 0;
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1048_ = leanh::lean_ctor_get(v___x_1044_, 1);
                v_endExclusive_1049_ = leanh::lean_ctor_get(v___x_1044_, 2);
                v___x_1050_ = lean_nat_sub(v_endExclusive_1049_, v_startInclusive_1048_);
                v___x_1051_ = lean_nat_dec_eq(v_a_1046_, v___x_1050_);
                leanh::lean_dec(v___x_1050_);
                if v___x_1051_ == 0 {
                    v___x_1052_ = lean_string_utf8_get_fast(v_uri_1045_, v_a_1046_);
                    v___x_1053_ = lean_string_utf8_next_fast(v_uri_1045_, v_a_1046_);
                    leanh::lean_dec(v_a_1046_);
                    v___x_1054_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v___x_1052_);
                    v___x_1055_ = lean_string_append(v_b_1047_, v___x_1054_);
                    leanh::lean_dec_ref(v___x_1054_);
                    v_a_1046_ = v___x_1053_;
                    v_b_1047_ = v___x_1055_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1046_);
                    return v_b_1047_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(
    mut v___x_1057_: *mut leanh::LeanObject,
    mut v_uri_1058_: *mut leanh::LeanObject,
    mut v_a_1059_: *mut leanh::LeanObject,
    mut v_b_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(
        v___x_1057_,
        v_uri_1058_,
        v_a_1059_,
        v_b_1060_,
    );
    leanh::lean_dec_ref(v_uri_1058_);
    leanh::lean_dec_ref(v___x_1057_);
    return v_res_1061_;
}
pub unsafe fn l_System_Uri_escapeUri(
    mut v_uri_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0;
    v___x_1064_ = leanh::lean_unsigned_to_nat(0);
    v___x_1065_ = lean_string_utf8_byte_size(v_uri_1062_);
    leanh::lean_inc_ref(v_uri_1062_);
    v___x_1066_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1066_, 0, v_uri_1062_);
    leanh::lean_ctor_set(v___x_1066_, 1, v___x_1064_);
    leanh::lean_ctor_set(v___x_1066_, 2, v___x_1065_);
    v___x_1067_ = l_String_Slice_positions(v___x_1066_);
    v___x_1068_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(
        v___x_1066_,
        v_uri_1062_,
        v___x_1067_,
        v___x_1063_,
    );
    leanh::lean_dec_ref(v_uri_1062_);
    leanh::lean_dec_ref_known(v___x_1066_, 3);
    return v___x_1068_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(
    mut v___x_1069_: *mut leanh::LeanObject,
    mut v_uri_1070_: *mut leanh::LeanObject,
    mut v_inst_1071_: *mut leanh::LeanObject,
    mut v_R_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_b_1074_: *mut leanh::LeanObject,
    mut v_c_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(
        v___x_1069_,
        v_uri_1070_,
        v_a_1073_,
        v_b_1074_,
    );
    return v___x_1076_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(
    mut v___x_1077_: *mut leanh::LeanObject,
    mut v_uri_1078_: *mut leanh::LeanObject,
    mut v_inst_1079_: *mut leanh::LeanObject,
    mut v_R_1080_: *mut leanh::LeanObject,
    mut v_a_1081_: *mut leanh::LeanObject,
    mut v_b_1082_: *mut leanh::LeanObject,
    mut v_c_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(
        v___x_1077_,
        v_uri_1078_,
        v_inst_1079_,
        v_R_1080_,
        v_a_1081_,
        v_b_1082_,
        v_c_1083_,
    );
    leanh::lean_dec_ref(v_uri_1078_);
    leanh::lean_dec_ref(v___x_1077_);
    return v_res_1084_;
}
pub unsafe fn l_System_Uri_unescapeUri(
    mut v_s_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_System_Uri_UriEscape_decodeUri(v_s_1085_);
    return v___x_1086_;
}
pub unsafe fn l_System_Uri_unescapeUri___boxed(
    mut v_s_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_System_Uri_unescapeUri(v_s_1087_);
    leanh::lean_dec_ref(v_s_1087_);
    return v_res_1088_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(
    mut v___x_1089_: *mut leanh::LeanObject,
    mut v_uri_1090_: *mut leanh::LeanObject,
    mut v_a_1091_: *mut leanh::LeanObject,
    mut v_b_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_countdown_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: u8 = 0;
    let mut v_startInclusive_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u32 = 0;
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_1093_ = leanh::lean_ctor_get(v_a_1091_, 0);
                v_inner_1094_ = leanh::lean_ctor_get(v_a_1091_, 1);
                v_isSharedCheck_1113_ = (!leanh::lean_is_exclusive(v_a_1091_)) as u8;
                if v_isSharedCheck_1113_ == 0 {
                    v___x_1096_ = v_a_1091_;
                    v_isShared_1097_ = v_isSharedCheck_1113_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inner_1094_);
                    leanh::lean_inc(v_countdown_1093_);
                    leanh::lean_dec(v_a_1091_);
                    v___x_1096_ = leanh::lean_box(0);
                    v_isShared_1097_ = v_isSharedCheck_1113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1098_ = leanh::lean_unsigned_to_nat(1);
                v___x_1099_ = lean_nat_dec_eq(v_countdown_1093_, v___x_1098_);
                if v___x_1099_ == 0 {
                    v_startInclusive_1100_ = leanh::lean_ctor_get(v___x_1089_, 1);
                    v_endExclusive_1101_ = leanh::lean_ctor_get(v___x_1089_, 2);
                    v___x_1102_ = lean_nat_sub(v_endExclusive_1101_, v_startInclusive_1100_);
                    v___x_1103_ = lean_nat_dec_eq(v_inner_1094_, v___x_1102_);
                    leanh::lean_dec(v___x_1102_);
                    if v___x_1103_ == 0 {
                        v___x_1104_ = lean_string_utf8_next_fast(v_uri_1090_, v_inner_1094_);
                        v___x_1105_ = lean_string_utf8_get_fast(v_uri_1090_, v_inner_1094_);
                        leanh::lean_dec(v_inner_1094_);
                        v___x_1106_ = lean_nat_sub(v_countdown_1093_, v___x_1098_);
                        leanh::lean_dec(v_countdown_1093_);
                        if v_isShared_1097_ == 0 {
                            leanh::lean_ctor_set(v___x_1096_, 1, v___x_1104_);
                            leanh::lean_ctor_set(v___x_1096_, 0, v___x_1106_);
                            v___x_1108_ = v___x_1096_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1112_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1104_);
                            v___x_1108_ = v_reuseFailAlloc_1112_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1096_);
                        leanh::lean_dec(v_inner_1094_);
                        leanh::lean_dec(v_countdown_1093_);
                        return v_b_1092_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1096_);
                    leanh::lean_dec(v_inner_1094_);
                    leanh::lean_dec(v_countdown_1093_);
                    return v_b_1092_;
                }
            }
            2 => {
                v___x_1109_ = leanh::lean_box_uint32(v___x_1105_);
                v___x_1110_ = lean_array_push(v_b_1092_, v___x_1109_);
                v_a_1091_ = v___x_1108_;
                v_b_1092_ = v___x_1110_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(
    mut v___x_1114_: *mut leanh::LeanObject,
    mut v_uri_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
    mut v_b_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_1114_, v_uri_1115_, v_a_1116_, v_b_1117_);
    leanh::lean_dec_ref(v_uri_1115_);
    leanh::lean_dec_ref(v___x_1114_);
    return v_res_1118_;
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(
    mut v_uri_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = leanh::lean_unsigned_to_nat(0);
    v___x_1123_ = lean_string_utf8_byte_size(v_uri_1121_);
    leanh::lean_inc_ref(v_uri_1121_);
    v___x_1124_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1124_, 0, v_uri_1121_);
    leanh::lean_ctor_set(v___x_1124_, 1, v___x_1122_);
    leanh::lean_ctor_set(v___x_1124_, 2, v___x_1123_);
    v___x_1125_ = l_String_Slice_positions(v___x_1124_);
    v___x_1126_ = leanh::lean_unsigned_to_nat(3);
    v___x_1127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    leanh::lean_ctor_set(v___x_1127_, 1, v___x_1125_);
    v___x_1128_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0;
    v___x_1129_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_1124_, v_uri_1121_, v___x_1127_, v___x_1128_);
    leanh::lean_dec_ref_known(v___x_1124_, 3);
    v___x_1130_ = lean_array_to_list(v___x_1129_);
    if leanh::lean_obj_tag(v___x_1130_) == 1 {
        let mut v_tail_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1131_ = leanh::lean_ctor_get(v___x_1130_, 1);
        leanh::lean_inc(v_tail_1131_);
        if leanh::lean_obj_tag(v_tail_1131_) == 1 {
            let mut v_head_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: u32 = 0;
            let mut v___x_1136_: u32 = 0;
            let mut v___x_1137_: u8 = 0;
            v_head_1132_ = leanh::lean_ctor_get(v___x_1130_, 0);
            leanh::lean_inc(v_head_1132_);
            leanh::lean_dec_ref_known(v___x_1130_, 2);
            v_head_1133_ = leanh::lean_ctor_get(v_tail_1131_, 0);
            leanh::lean_inc(v_head_1133_);
            v_tail_1134_ = leanh::lean_ctor_get(v_tail_1131_, 1);
            leanh::lean_inc(v_tail_1134_);
            leanh::lean_dec_ref_known(v_tail_1131_, 2);
            v___x_1135_ = 58;
            v___x_1136_ = leanh::lean_unbox_uint32(v_head_1133_);
            leanh::lean_dec(v_head_1133_);
            v___x_1137_ = lean_uint32_dec_eq(v___x_1136_, v___x_1135_);
            if v___x_1137_ == 0 {
                leanh::lean_dec(v_tail_1134_);
                leanh::lean_dec(v_head_1132_);
                return v_uri_1121_;
            } else {
                if leanh::lean_obj_tag(v_tail_1134_) == 0 {
                    let mut v___x_1138_: u32 = 0;
                    let mut v___x_1139_: u32 = 0;
                    let mut v___x_1140_: u8 = 0;
                    v___x_1138_ = 65;
                    v___x_1139_ = leanh::lean_unbox_uint32(v_head_1132_);
                    v___x_1140_ = lean_uint32_dec_le(v___x_1138_, v___x_1139_);
                    if v___x_1140_ == 0 {
                        leanh::lean_dec(v_head_1132_);
                        return v_uri_1121_;
                    } else {
                        let mut v___x_1141_: u32 = 0;
                        let mut v___x_1142_: u32 = 0;
                        let mut v___x_1143_: u8 = 0;
                        v___x_1141_ = 90;
                        v___x_1142_ = leanh::lean_unbox_uint32(v_head_1132_);
                        leanh::lean_dec(v_head_1132_);
                        v___x_1143_ = lean_uint32_dec_le(v___x_1142_, v___x_1141_);
                        if v___x_1143_ == 0 {
                            return v_uri_1121_;
                        } else {
                            let mut v___x_1144_: u32 = 0;
                            let mut v___x_1145_: u8 = 0;
                            v___x_1144_ = lean_string_utf8_get(v_uri_1121_, v___x_1122_);
                            v___x_1145_ = lean_uint32_dec_le(v___x_1138_, v___x_1144_);
                            if v___x_1145_ == 0 {
                                let mut v___x_1146_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_1146_ =
                                    lean_string_utf8_set(v_uri_1121_, v___x_1122_, v___x_1144_);
                                return v___x_1146_;
                            } else {
                                let mut v___x_1147_: u8 = 0;
                                v___x_1147_ = lean_uint32_dec_le(v___x_1144_, v___x_1141_);
                                if v___x_1147_ == 0 {
                                    let mut v___x_1148_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_1148_ =
                                        lean_string_utf8_set(v_uri_1121_, v___x_1122_, v___x_1144_);
                                    return v___x_1148_;
                                } else {
                                    let mut v___x_1149_: u32 = 0;
                                    let mut v___x_1150_: u32 = 0;
                                    let mut v___x_1151_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_1149_ = 32;
                                    v___x_1150_ = lean_uint32_add(v___x_1144_, v___x_1149_);
                                    v___x_1151_ =
                                        lean_string_utf8_set(v_uri_1121_, v___x_1122_, v___x_1150_);
                                    return v___x_1151_;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_tail_1134_);
                    leanh::lean_dec(v_head_1132_);
                    return v_uri_1121_;
                }
            }
        } else {
            leanh::lean_dec_ref_known(v___x_1130_, 2);
            leanh::lean_dec(v_tail_1131_);
            return v_uri_1121_;
        }
    } else {
        leanh::lean_dec(v___x_1130_);
        return v_uri_1121_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(
    mut v___x_1152_: *mut leanh::LeanObject,
    mut v_uri_1153_: *mut leanh::LeanObject,
    mut v_inst_1154_: *mut leanh::LeanObject,
    mut v_R_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
    mut v_b_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_1152_, v_uri_1153_, v_a_1156_, v_b_1157_);
    return v___x_1158_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(
    mut v___x_1159_: *mut leanh::LeanObject,
    mut v_uri_1160_: *mut leanh::LeanObject,
    mut v_inst_1161_: *mut leanh::LeanObject,
    mut v_R_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_b_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(v___x_1159_, v_uri_1160_, v_inst_1161_, v_R_1162_, v_a_1163_, v_b_1164_);
    leanh::lean_dec_ref(v_uri_1160_);
    leanh::lean_dec_ref(v___x_1159_);
    return v_res_1165_;
}
pub unsafe fn l_String_mapAux___at___00System_Uri_pathToUri_spec__0(
    mut v_s_1166_: *mut leanh::LeanObject,
    mut v_p_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1169_: u32 = 0;
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: u32 = 0;
    let mut v___x_1177_: u32 = 0;
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1174_ = lean_string_utf8_byte_size(v_s_1166_);
                v___x_1175_ = lean_nat_dec_eq(v_p_1167_, v___x_1174_);
                if v___x_1175_ == 0 {
                    v___x_1176_ = lean_string_utf8_get_fast(v_s_1166_, v_p_1167_);
                    v___x_1177_ = 92;
                    v___x_1178_ = lean_uint32_dec_eq(v___x_1176_, v___x_1177_);
                    if v___x_1178_ == 0 {
                        v___y_1169_ = v___x_1176_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1179_ = 47;
                        v___y_1169_ = v___x_1179_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_1167_);
                    return v_s_1166_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_1167_);
                v___x_1170_ = lean_string_utf8_set(v_s_1166_, v_p_1167_, v___y_1169_);
                v___x_1171_ = l_Char_utf8Size(v___y_1169_);
                v___x_1172_ = lean_nat_add(v_p_1167_, v___x_1171_);
                leanh::lean_dec(v___x_1171_);
                leanh::lean_dec(v_p_1167_);
                v_s_1166_ = v___x_1170_;
                v_p_1167_ = v___x_1172_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_System_Uri_pathToUri___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_System_Uri_pathToUri___closed__1;
    v___x_1183_ = lean_string_utf8_byte_size(v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_System_Uri_pathToUri(
    mut v_fname_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    let mut v_uri_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_1205_ = l_System_FilePath_normalize(v_fname_1185_);
                v___x_1206_ = l_System_Platform_isWindows;
                if v___x_1206_ == 0 {
                    v_uri_1191_ = v_uri_1205_;
                    state = 2;
                    continue;
                } else {
                    v_uri_1207_ =
                        l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(v_uri_1205_);
                    v___x_1208_ = leanh::lean_unsigned_to_nat(0);
                    v_uri_1209_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(
                        v_uri_1207_,
                        v___x_1208_,
                    );
                    v_uri_1191_ = v_uri_1209_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1188_ = l_System_Uri_pathToUri___closed__0;
                v___x_1189_ = lean_string_append(v___x_1188_, v___y_1187_);
                leanh::lean_dec_ref(v___y_1187_);
                return v___x_1189_;
            }
            2 => {
                v___x_1192_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0;
                v___x_1193_ = leanh::lean_unsigned_to_nat(0);
                v___x_1194_ = lean_string_utf8_byte_size(v_uri_1191_);
                leanh::lean_inc_ref(v_uri_1191_);
                v___x_1195_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1195_, 0, v_uri_1191_);
                leanh::lean_ctor_set(v___x_1195_, 1, v___x_1193_);
                leanh::lean_ctor_set(v___x_1195_, 2, v___x_1194_);
                v___x_1196_ = l_String_Slice_positions(v___x_1195_);
                v_uri_1197_ =
                    l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(
                        v___x_1195_,
                        v_uri_1191_,
                        v___x_1196_,
                        v___x_1192_,
                    );
                leanh::lean_dec_ref(v_uri_1191_);
                leanh::lean_dec_ref_known(v___x_1195_, 3);
                v___x_1198_ = l_System_Uri_pathToUri___closed__1;
                v___x_1199_ = lean_string_utf8_byte_size(v_uri_1197_);
                v___x_1200_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_System_Uri_pathToUri___closed__2),
                    core::ptr::addr_of_mut!(l_System_Uri_pathToUri___closed__2_once),
                    _init_l_System_Uri_pathToUri___closed__2,
                );
                v___x_1201_ = lean_nat_dec_le(v___x_1200_, v___x_1199_);
                if v___x_1201_ == 0 {
                    v___y_1187_ = v_uri_1197_;
                    state = 1;
                    continue;
                } else {
                    v___x_1202_ = lean_string_memcmp(
                        v_uri_1197_,
                        v___x_1198_,
                        v___x_1193_,
                        v___x_1193_,
                        v___x_1200_,
                    );
                    if v___x_1202_ == 0 {
                        v___y_1187_ = v_uri_1197_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1203_ = l_System_Uri_pathToUri___closed__3;
                        v___x_1204_ = lean_string_append(v___x_1203_, v_uri_1197_);
                        leanh::lean_dec_ref(v_uri_1197_);
                        return v___x_1204_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(
    mut v_p_1210_: *mut leanh::LeanObject,
    mut v_a_1211_: *mut leanh::LeanObject,
    mut v_b_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_countdown_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1217_: u8 = 0;
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v_str_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u32 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_1213_ = leanh::lean_ctor_get(v_a_1211_, 0);
                v_inner_1214_ = leanh::lean_ctor_get(v_a_1211_, 1);
                v_isSharedCheck_1236_ = (!leanh::lean_is_exclusive(v_a_1211_)) as u8;
                if v_isSharedCheck_1236_ == 0 {
                    v___x_1216_ = v_a_1211_;
                    v_isShared_1217_ = v_isSharedCheck_1236_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inner_1214_);
                    leanh::lean_inc(v_countdown_1213_);
                    leanh::lean_dec(v_a_1211_);
                    v___x_1216_ = leanh::lean_box(0);
                    v_isShared_1217_ = v_isSharedCheck_1236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1218_ = leanh::lean_unsigned_to_nat(1);
                v___x_1219_ = lean_nat_dec_eq(v_countdown_1213_, v___x_1218_);
                if v___x_1219_ == 0 {
                    v_str_1220_ = leanh::lean_ctor_get(v_p_1210_, 0);
                    v_startInclusive_1221_ = leanh::lean_ctor_get(v_p_1210_, 1);
                    v_endExclusive_1222_ = leanh::lean_ctor_get(v_p_1210_, 2);
                    v___x_1223_ = lean_nat_sub(v_endExclusive_1222_, v_startInclusive_1221_);
                    v___x_1224_ = lean_nat_dec_eq(v_inner_1214_, v___x_1223_);
                    leanh::lean_dec(v___x_1223_);
                    if v___x_1224_ == 0 {
                        v___x_1225_ = lean_nat_add(v_startInclusive_1221_, v_inner_1214_);
                        leanh::lean_dec(v_inner_1214_);
                        v___x_1226_ = lean_string_utf8_next_fast(v_str_1220_, v___x_1225_);
                        v___x_1227_ = lean_nat_sub(v___x_1226_, v_startInclusive_1221_);
                        v___x_1228_ = lean_string_utf8_get_fast(v_str_1220_, v___x_1225_);
                        leanh::lean_dec(v___x_1225_);
                        v___x_1229_ = lean_nat_sub(v_countdown_1213_, v___x_1218_);
                        leanh::lean_dec(v_countdown_1213_);
                        if v_isShared_1217_ == 0 {
                            leanh::lean_ctor_set(v___x_1216_, 1, v___x_1227_);
                            leanh::lean_ctor_set(v___x_1216_, 0, v___x_1229_);
                            v___x_1231_ = v___x_1216_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1235_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1229_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1227_);
                            v___x_1231_ = v_reuseFailAlloc_1235_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1216_);
                        leanh::lean_dec(v_inner_1214_);
                        leanh::lean_dec(v_countdown_1213_);
                        return v_b_1212_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1216_);
                    leanh::lean_dec(v_inner_1214_);
                    leanh::lean_dec(v_countdown_1213_);
                    return v_b_1212_;
                }
            }
            2 => {
                v___x_1232_ = leanh::lean_box_uint32(v___x_1228_);
                v___x_1233_ = lean_array_push(v_b_1212_, v___x_1232_);
                v_a_1211_ = v___x_1231_;
                v_b_1212_ = v___x_1233_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(
    mut v_p_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_b_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1240_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_1237_, v_a_1238_, v_b_1239_);
    leanh::lean_dec_ref(v_p_1237_);
    return v_res_1240_;
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(
    mut v_p_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: u32 = 0;
    let mut v___x_1252_: u32 = 0;
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: u32 = 0;
    let mut v___x_1256_: u8 = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u32 = 0;
    let mut v___x_1259_: u32 = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1262_: u8 = 0;
    let mut v_str_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u32 = 0;
    let mut v___x_1281_: u32 = 0;
    let mut v___x_1282_: u8 = 0;
    let mut v_head_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: u32 = 0;
    let mut v___x_1287_: u32 = 0;
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: u32 = 0;
    let mut v___x_1290_: u32 = 0;
    let mut v___x_1291_: u8 = 0;
    let mut v_head_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: u32 = 0;
    let mut v___x_1295_: u32 = 0;
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1297_: u32 = 0;
    let mut v___x_1298_: u32 = 0;
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: u32 = 0;
    let mut v___x_1301_: u32 = 0;
    let mut v___x_1302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1272_ = l_String_Slice_positions(v_p_1241_);
                v___x_1273_ = leanh::lean_unsigned_to_nat(4);
                v___x_1274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1274_, 0, v___x_1273_);
                leanh::lean_ctor_set(v___x_1274_, 1, v___x_1272_);
                v___x_1275_ =
                    l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0;
                v___x_1276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_1241_, v___x_1274_, v___x_1275_);
                v___x_1277_ = lean_array_to_list(v___x_1276_);
                if leanh::lean_obj_tag(v___x_1277_) == 1 {
                    v_head_1278_ = leanh::lean_ctor_get(v___x_1277_, 0);
                    leanh::lean_inc(v_head_1278_);
                    v_tail_1279_ = leanh::lean_ctor_get(v___x_1277_, 1);
                    leanh::lean_inc(v_tail_1279_);
                    leanh::lean_dec_ref_known(v___x_1277_, 2);
                    v___x_1280_ = 47;
                    v___x_1281_ = leanh::lean_unbox_uint32(v_head_1278_);
                    leanh::lean_dec(v_head_1278_);
                    v___x_1282_ = lean_uint32_dec_eq(v___x_1281_, v___x_1280_);
                    if v___x_1282_ == 0 {
                        leanh::lean_dec(v_tail_1279_);
                        state = 3;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v_tail_1279_) == 1 {
                            v_head_1283_ = leanh::lean_ctor_get(v_tail_1279_, 0);
                            leanh::lean_inc(v_head_1283_);
                            v_tail_1284_ = leanh::lean_ctor_get(v_tail_1279_, 1);
                            leanh::lean_inc(v_tail_1284_);
                            leanh::lean_dec_ref_known(v_tail_1279_, 2);
                            if leanh::lean_obj_tag(v_tail_1284_) == 1 {
                                v_head_1292_ = leanh::lean_ctor_get(v_tail_1284_, 0);
                                leanh::lean_inc(v_head_1292_);
                                v_tail_1293_ = leanh::lean_ctor_get(v_tail_1284_, 1);
                                leanh::lean_inc(v_tail_1293_);
                                leanh::lean_dec_ref_known(v_tail_1284_, 2);
                                v___x_1294_ = 58;
                                v___x_1295_ = leanh::lean_unbox_uint32(v_head_1292_);
                                leanh::lean_dec(v_head_1292_);
                                v___x_1296_ = lean_uint32_dec_eq(v___x_1295_, v___x_1294_);
                                if v___x_1296_ == 0 {
                                    leanh::lean_dec(v_tail_1293_);
                                    leanh::lean_dec(v_head_1283_);
                                    state = 3;
                                    continue;
                                } else {
                                    if leanh::lean_obj_tag(v_tail_1293_) == 0 {
                                        v___x_1297_ = 65;
                                        v___x_1298_ = leanh::lean_unbox_uint32(v_head_1283_);
                                        v___x_1299_ = lean_uint32_dec_le(v___x_1297_, v___x_1298_);
                                        if v___x_1299_ == 0 {
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_1300_ = 90;
                                            v___x_1301_ =
                                                leanh::lean_unbox_uint32(v_head_1283_);
                                            v___x_1302_ =
                                                lean_uint32_dec_le(v___x_1301_, v___x_1300_);
                                            if v___x_1302_ == 0 {
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_head_1283_);
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_tail_1293_);
                                        leanh::lean_dec(v_head_1283_);
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_tail_1284_);
                                leanh::lean_dec(v_head_1283_);
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_tail_1279_);
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1277_);
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_str_1243_ = leanh::lean_ctor_get(v_p_1241_, 0);
                v_startInclusive_1244_ = leanh::lean_ctor_get(v_p_1241_, 1);
                v_endExclusive_1245_ = leanh::lean_ctor_get(v_p_1241_, 2);
                v___x_1246_ = leanh::lean_unsigned_to_nat(1);
                v___x_1247_ = leanh::lean_unsigned_to_nat(0);
                v___x_1248_ = l_String_Slice_Pos_nextn(v_p_1241_, v___x_1247_, v___x_1246_);
                v___x_1249_ = lean_nat_add(v_startInclusive_1244_, v___x_1248_);
                leanh::lean_dec(v___x_1248_);
                v___x_1250_ =
                    lean_string_utf8_extract(v_str_1243_, v___x_1249_, v_endExclusive_1245_);
                leanh::lean_dec(v___x_1249_);
                v___x_1251_ = lean_string_utf8_get(v___x_1250_, v___x_1247_);
                v___x_1252_ = 97;
                v___x_1253_ = lean_uint32_dec_le(v___x_1252_, v___x_1251_);
                if v___x_1253_ == 0 {
                    v___x_1254_ = lean_string_utf8_set(v___x_1250_, v___x_1247_, v___x_1251_);
                    return v___x_1254_;
                } else {
                    v___x_1255_ = 122;
                    v___x_1256_ = lean_uint32_dec_le(v___x_1251_, v___x_1255_);
                    if v___x_1256_ == 0 {
                        v___x_1257_ = lean_string_utf8_set(v___x_1250_, v___x_1247_, v___x_1251_);
                        return v___x_1257_;
                    } else {
                        v___x_1258_ = 4294967264;
                        v___x_1259_ = lean_uint32_add(v___x_1251_, v___x_1258_);
                        v___x_1260_ = lean_string_utf8_set(v___x_1250_, v___x_1247_, v___x_1259_);
                        return v___x_1260_;
                    }
                }
            }
            2 => {
                if v___y_1262_ == 0 {
                    v_str_1263_ = leanh::lean_ctor_get(v_p_1241_, 0);
                    v_startInclusive_1264_ = leanh::lean_ctor_get(v_p_1241_, 1);
                    v_endExclusive_1265_ = leanh::lean_ctor_get(v_p_1241_, 2);
                    v___x_1266_ = lean_string_utf8_extract(
                        v_str_1263_,
                        v_startInclusive_1264_,
                        v_endExclusive_1265_,
                    );
                    return v___x_1266_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_str_1268_ = leanh::lean_ctor_get(v_p_1241_, 0);
                v_startInclusive_1269_ = leanh::lean_ctor_get(v_p_1241_, 1);
                v_endExclusive_1270_ = leanh::lean_ctor_get(v_p_1241_, 2);
                v___x_1271_ = lean_string_utf8_extract(
                    v_str_1268_,
                    v_startInclusive_1269_,
                    v_endExclusive_1270_,
                );
                return v___x_1271_;
            }
            4 => {
                v___x_1286_ = 97;
                v___x_1287_ = leanh::lean_unbox_uint32(v_head_1283_);
                v___x_1288_ = lean_uint32_dec_le(v___x_1286_, v___x_1287_);
                if v___x_1288_ == 0 {
                    leanh::lean_dec(v_head_1283_);
                    v___y_1262_ = v___x_1288_;
                    state = 2;
                    continue;
                } else {
                    v___x_1289_ = 122;
                    v___x_1290_ = leanh::lean_unbox_uint32(v_head_1283_);
                    leanh::lean_dec(v_head_1283_);
                    v___x_1291_ = lean_uint32_dec_le(v___x_1290_, v___x_1289_);
                    v___y_1262_ = v___x_1291_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(
    mut v_p_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_1303_);
    leanh::lean_dec_ref(v_p_1303_);
    return v_res_1304_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(
    mut v_p_1305_: *mut leanh::LeanObject,
    mut v_inst_1306_: *mut leanh::LeanObject,
    mut v_R_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
    mut v_b_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_1305_, v_a_1308_, v_b_1309_);
    return v___x_1310_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(
    mut v_p_1311_: *mut leanh::LeanObject,
    mut v_inst_1312_: *mut leanh::LeanObject,
    mut v_R_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_b_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(v_p_1311_, v_inst_1312_, v_R_1313_, v_a_1314_, v_b_1315_);
    leanh::lean_dec_ref(v_p_1311_);
    return v_res_1316_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = l_System_Uri_pathToUri___closed__3;
    v___x_1318_ = lean_string_utf8_byte_size(v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(
    mut v_s_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    v___x_1320_ = l_System_Uri_pathToUri___closed__3;
    v___x_1321_ = lean_string_utf8_byte_size(v_s_1319_);
    v___x_1322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0);
    v___x_1323_ = lean_nat_dec_le(v___x_1322_, v___x_1321_);
    if v___x_1323_ == 0 {
        let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1319_);
        v___x_1324_ = leanh::lean_box(0);
        return v___x_1324_;
    } else {
        let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: u8 = 0;
        v___x_1325_ = leanh::lean_unsigned_to_nat(0);
        v___x_1326_ = lean_string_memcmp(
            v_s_1319_,
            v___x_1320_,
            v___x_1325_,
            v___x_1325_,
            v___x_1322_,
        );
        if v___x_1326_ == 0 {
            let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1319_);
            v___x_1327_ = leanh::lean_box(0);
            return v___x_1327_;
        } else {
            let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1319_);
            v___x_1328_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1328_, 0, v_s_1319_);
            leanh::lean_ctor_set(v___x_1328_, 1, v___x_1325_);
            leanh::lean_ctor_set(v___x_1328_, 2, v___x_1321_);
            v___x_1329_ = l_String_Slice_pos_x21(v___x_1328_, v___x_1322_);
            leanh::lean_dec_ref_known(v___x_1328_, 3);
            v___x_1330_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1330_, 0, v_s_1319_);
            leanh::lean_ctor_set(v___x_1330_, 1, v___x_1329_);
            leanh::lean_ctor_set(v___x_1330_, 2, v___x_1321_);
            v___x_1331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
            return v___x_1331_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(
    mut v_s_1332_: *mut leanh::LeanObject,
    mut v_pat_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1334_ =
        l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v_s_1332_);
    return v___x_1334_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(
    mut v_s_1335_: *mut leanh::LeanObject,
    mut v_pat_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(
        v_s_1335_,
        v_pat_1336_,
    );
    leanh::lean_dec_ref(v_pat_1336_);
    return v_res_1337_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(
    mut v_s_1338_: *mut leanh::LeanObject,
    mut v_pos_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: u32 = 0;
    let mut v___x_1348_: u32 = 0;
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1340_ = leanh::lean_ctor_get(v_s_1338_, 0);
                v_startInclusive_1341_ = leanh::lean_ctor_get(v_s_1338_, 1);
                v_endExclusive_1342_ = leanh::lean_ctor_get(v_s_1338_, 2);
                v___x_1343_ = lean_nat_add(v_startInclusive_1341_, v_pos_1339_);
                v___x_1344_ = leanh::lean_unsigned_to_nat(0);
                v___x_1345_ = lean_nat_sub(v_endExclusive_1342_, v___x_1343_);
                v___x_1346_ = lean_nat_dec_eq(v___x_1344_, v___x_1345_);
                leanh::lean_dec(v___x_1345_);
                if v___x_1346_ == 0 {
                    v___x_1347_ = lean_string_utf8_get_fast(v_str_1340_, v___x_1343_);
                    v___x_1348_ = 47;
                    v___x_1349_ = lean_uint32_dec_eq(v___x_1347_, v___x_1348_);
                    if v___x_1349_ == 0 {
                        v___x_1350_ = lean_string_utf8_next_fast(v_str_1340_, v___x_1343_);
                        v___x_1351_ = lean_nat_sub(v___x_1350_, v___x_1343_);
                        leanh::lean_dec(v___x_1343_);
                        v___x_1352_ = lean_nat_add(v_pos_1339_, v___x_1351_);
                        leanh::lean_dec(v___x_1351_);
                        v___x_1353_ = lean_nat_dec_lt(v_pos_1339_, v___x_1352_);
                        if v___x_1353_ == 0 {
                            leanh::lean_dec(v___x_1352_);
                            return v_pos_1339_;
                        } else {
                            leanh::lean_dec(v_pos_1339_);
                            v_pos_1339_ = v___x_1352_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1343_);
                        return v_pos_1339_;
                    }
                } else {
                    leanh::lean_dec(v___x_1343_);
                    return v_pos_1339_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(
    mut v_s_1355_: *mut leanh::LeanObject,
    mut v_pos_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1357_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(
        v_s_1355_,
        v_pos_1356_,
    );
    leanh::lean_dec_ref(v_s_1355_);
    return v_res_1357_;
}
pub unsafe fn l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(
    mut v_s_1358_: *mut leanh::LeanObject,
    mut v_p_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1361_: u32 = 0;
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1368_: u32 = 0;
    let mut v___x_1369_: u32 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1366_ = lean_string_utf8_byte_size(v_s_1358_);
                v___x_1367_ = lean_nat_dec_eq(v_p_1359_, v___x_1366_);
                if v___x_1367_ == 0 {
                    v___x_1368_ = lean_string_utf8_get_fast(v_s_1358_, v_p_1359_);
                    v___x_1369_ = 47;
                    v___x_1370_ = lean_uint32_dec_eq(v___x_1368_, v___x_1369_);
                    if v___x_1370_ == 0 {
                        v___y_1361_ = v___x_1368_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1371_ = 92;
                        v___y_1361_ = v___x_1371_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_1359_);
                    return v_s_1358_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_1359_);
                v___x_1362_ = lean_string_utf8_set(v_s_1358_, v_p_1359_, v___y_1361_);
                v___x_1363_ = l_Char_utf8Size(v___y_1361_);
                v___x_1364_ = lean_nat_add(v_p_1359_, v___x_1363_);
                leanh::lean_dec(v___x_1363_);
                leanh::lean_dec(v_p_1359_);
                v_s_1358_ = v___x_1362_;
                v_p_1359_ = v___x_1364_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_Uri_fileUriToPath_x3f(
    mut v_uri_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v_str_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_unused_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1373_ = l_System_Uri_UriEscape_decodeUri(v_uri_1372_);
                v___x_1374_ =
                    l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(
                        v___x_1373_,
                    );
                if leanh::lean_obj_tag(v___x_1374_) == 0 {
                    v___x_1375_ = leanh::lean_box(0);
                    return v___x_1375_;
                } else {
                    v_val_1376_ = leanh::lean_ctor_get(v___x_1374_, 0);
                    v_isSharedCheck_1406_ = (!leanh::lean_is_exclusive(v___x_1374_)) as u8;
                    if v_isSharedCheck_1406_ == 0 {
                        v___x_1378_ = v___x_1374_;
                        v_isShared_1379_ = v_isSharedCheck_1406_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1376_);
                        leanh::lean_dec(v___x_1374_);
                        v___x_1378_ = leanh::lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_1380_ = leanh::lean_ctor_get(v_val_1376_, 0);
                leanh::lean_inc_ref(v_str_1380_);
                v_startInclusive_1381_ = leanh::lean_ctor_get(v_val_1376_, 1);
                leanh::lean_inc(v_startInclusive_1381_);
                v_endExclusive_1382_ = leanh::lean_ctor_get(v_val_1376_, 2);
                leanh::lean_inc(v_endExclusive_1382_);
                v___x_1383_ = leanh::lean_unsigned_to_nat(0);
                v___x_1384_ =
                    l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(
                        v_val_1376_,
                        v___x_1383_,
                    );
                v_isSharedCheck_1402_ = (!leanh::lean_is_exclusive(v_val_1376_)) as u8;
                if v_isSharedCheck_1402_ == 0 {
                    v_unused_1403_ = leanh::lean_ctor_get(v_val_1376_, 2);
                    leanh::lean_dec(v_unused_1403_);
                    v_unused_1404_ = leanh::lean_ctor_get(v_val_1376_, 1);
                    leanh::lean_dec(v_unused_1404_);
                    v_unused_1405_ = leanh::lean_ctor_get(v_val_1376_, 0);
                    leanh::lean_dec(v_unused_1405_);
                    v___x_1386_ = v_val_1376_;
                    v_isShared_1387_ = v_isSharedCheck_1402_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1376_);
                    v___x_1386_ = leanh::lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1388_ = lean_nat_add(v_startInclusive_1381_, v___x_1384_);
                leanh::lean_dec(v___x_1384_);
                leanh::lean_dec(v_startInclusive_1381_);
                v___x_1389_ = l_System_Platform_isWindows;
                if v___x_1389_ == 0 {
                    leanh::lean_del_object(v___x_1386_);
                    v___x_1390_ =
                        lean_string_utf8_extract(v_str_1380_, v___x_1388_, v_endExclusive_1382_);
                    leanh::lean_dec(v_endExclusive_1382_);
                    leanh::lean_dec(v___x_1388_);
                    leanh::lean_dec_ref(v_str_1380_);
                    if v_isShared_1379_ == 0 {
                        leanh::lean_ctor_set(v___x_1378_, 0, v___x_1390_);
                        v___x_1392_ = v___x_1378_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
                        v___x_1392_ = v_reuseFailAlloc_1393_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1387_ == 0 {
                        leanh::lean_ctor_set(v___x_1386_, 1, v___x_1388_);
                        v_p_1395_ = v___x_1386_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1401_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_str_1380_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1388_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1401_,
                            2,
                            v_endExclusive_1382_,
                        );
                        v_p_1395_ = v_reuseFailAlloc_1401_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1392_;
            }
            4 => {
                v___x_1396_ =
                    l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_1395_);
                leanh::lean_dec_ref(v_p_1395_);
                v___x_1397_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(
                    v___x_1396_,
                    v___x_1383_,
                );
                if v_isShared_1379_ == 0 {
                    leanh::lean_ctor_set(v___x_1378_, 0, v___x_1397_);
                    v___x_1399_ = v___x_1378_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_Uri_fileUriToPath_x3f___boxed(
    mut v_uri_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_System_Uri_fileUriToPath_x3f(v_uri_1407_);
    leanh::lean_dec_ref(v_uri_1407_);
    return v_res_1408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_Uri(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_System_Uri_UriEscape_zero = _init_l_System_Uri_UriEscape_zero();
    l_System_Uri_UriEscape_nine = _init_l_System_Uri_UriEscape_nine();
    l_System_Uri_UriEscape_lettera = _init_l_System_Uri_UriEscape_lettera();
    l_System_Uri_UriEscape_letterf = _init_l_System_Uri_UriEscape_letterf();
    l_System_Uri_UriEscape_letterA = _init_l_System_Uri_UriEscape_letterA();
    l_System_Uri_UriEscape_letterF = _init_l_System_Uri_UriEscape_letterF();
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1 =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1();
    leanh::lean_mark_persistent(
        l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1,
    );
    l_System_Uri_UriEscape_rfc3986ReservedChars =
        _init_l_System_Uri_UriEscape_rfc3986ReservedChars();
    leanh::lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_Uri(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_Uri(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Uri(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_System_Uri(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_System_Uri(builtin);
}