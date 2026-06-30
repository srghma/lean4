// Lean compiler output
// Module: Std.Http.Data.URI.Encoding
// Imports: Init.Grind Init.While Init.Data.SInt.Lemmas Init.Data.UInt.Lemmas Init.Data.UInt.Bitwise Init.Data.Array.Lemmas Init.Data.String.Basic Std.Http.Internal.Char
use crate::ffi::{
    lean_array_get_size, lean_byte_array_copy_slice, lean_byte_array_data, lean_byte_array_fget,
    lean_byte_array_hash, lean_byte_array_push, lean_byte_array_size, lean_byte_array_uget,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_string_from_utf8_unchecked, lean_string_to_utf8, lean_string_validate_utf8,
    lean_uint8_add, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint8_dec_lt, lean_uint8_land,
    lean_uint8_shift_left, lean_uint8_shift_right, lean_uint8_sub, lean_uint32_to_uint8,
    lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any;
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{
    l_ByteArray_decEq___boxed, l_ByteArray_hash___boxed,
};
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::SInt::Lemmas::{
    initialize_Init_Data_SInt_Lemmas, runtime_initialize_Init_Data_SInt_Lemmas,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::UInt::Bitwise::{
    initialize_Init_Data_UInt_Bitwise, runtime_initialize_Init_Data_UInt_Bitwise,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::l_ByteArray_empty;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Std::Http::Internal::Char::{
    initialize_Std_Http_Internal_Char, runtime_initialize_Std_Http_Internal_Char,
};
static mut l_Std_Http_URI_isEncodedChar___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__0: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__1: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__2: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__3: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__4: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__5: u8 = 0;
static mut l_Std_Http_URI_isEncodedChar___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedChar___closed__6: u8 = 0;
static mut l_Std_Http_URI_isEncodedQueryChar___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_isEncodedQueryChar___closed__0: u8 = 0;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 85, 82, 73, 46, 69, 110, 99,
        111, 100, 105, 110, 103, 0,
    ],
};
static mut l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1_value:
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 69, 110, 99, 111, 100, 101, 100,
        83, 116, 114, 105, 110, 103, 46, 111, 102, 66, 121, 116, 101, 65, 114, 114, 97, 121, 33, 0,
    ],
};
static mut l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 101, 110, 99, 111, 100, 101, 100, 32, 115, 116, 114,
        105, 110, 103, 0,
    ],
};
static mut l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_EncodedString_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedString_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedString_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_instToString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedString_decode___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_EncodedString_instRepr___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedString_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedString_instBEq___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedString_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_instBEq___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedString_instHashable___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedString_instHashable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedString_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 69, 110, 99, 111, 100, 101, 100,
        81, 117, 101, 114, 121, 83, 116, 114, 105, 110, 103, 46, 111, 102, 66, 121, 116, 101, 65,
        114, 114, 97, 121, 33, 0,
    ],
};
static mut l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 101, 110, 99, 111, 100, 101, 100, 32, 113, 117, 101,
        114, 121, 32, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0: u8 = 0;
pub static l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0_value:
    leanh::LeanScalarArray<1> = leanh::LeanScalarArray {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + 1) as u16,
        other: 1,
        tag: 248,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [0],
};
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1: u64 = 0;
pub static l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2_value:
    leanh::LeanScalarArray<1> = leanh::LeanScalarArray {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + 1) as u16,
        other: 1,
        tag: 248,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [1],
};
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16: u8 = 0;
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17: u8 = 0;
pub static l_Std_Http_URI_EncodedSegment_encode___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedSegment_encode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedSegment_encode___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0: u8 = 0;
static mut l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1: u8 = 0;
pub static l_Std_Http_URI_EncodedFragment_encode___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedFragment_encode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedFragment_encode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedUserInfo_encode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_URI_EncodedQueryParam_encode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__0() -> u8 {
    let mut v___x_1284_: u32 = 0;
    let mut v___x_1285_: u8 = 0;
    v___x_1284_ = 37;
    v___x_1285_ = lean_uint32_to_uint8(v___x_1284_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__1() -> u8 {
    let mut v___x_1286_: u32 = 0;
    let mut v___x_1287_: u8 = 0;
    v___x_1286_ = 65;
    v___x_1287_ = lean_uint32_to_uint8(v___x_1286_);
    return v___x_1287_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__2() -> u8 {
    let mut v___x_1288_: u32 = 0;
    let mut v___x_1289_: u8 = 0;
    v___x_1288_ = 70;
    v___x_1289_ = lean_uint32_to_uint8(v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__3() -> u8 {
    let mut v___x_1290_: u32 = 0;
    let mut v___x_1291_: u8 = 0;
    v___x_1290_ = 97;
    v___x_1291_ = lean_uint32_to_uint8(v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__4() -> u8 {
    let mut v___x_1292_: u32 = 0;
    let mut v___x_1293_: u8 = 0;
    v___x_1292_ = 102;
    v___x_1293_ = lean_uint32_to_uint8(v___x_1292_);
    return v___x_1293_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__5() -> u8 {
    let mut v___x_1294_: u32 = 0;
    let mut v___x_1295_: u8 = 0;
    v___x_1294_ = 48;
    v___x_1295_ = lean_uint32_to_uint8(v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedChar___closed__6() -> u8 {
    let mut v___x_1296_: u32 = 0;
    let mut v___x_1297_: u8 = 0;
    v___x_1296_ = 57;
    v___x_1297_ = lean_uint32_to_uint8(v___x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_Http_URI_isEncodedChar(
    mut v_rule_1298_: *mut leanh::LeanObject,
    mut v_c_1299_: u8,
) -> u8 {
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: u8 = 0;
    let mut v___y_1303_: u8 = 0;
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: u8 = 0;
    let mut v___y_1307_: u8 = 0;
    let mut v___x_1308_: u8 = 0;
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1310_: u8 = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v___y_1313_: u8 = 0;
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1300_ = 128;
                v___x_1301_ = lean_uint8_dec_lt(v_c_1299_, v___x_1300_);
                if v___x_1301_ == 0 {
                    leanh::lean_dec_ref(v_rule_1298_);
                    return v___x_1301_;
                } else {
                    v___x_1318_ = leanh::lean_box((v_c_1299_) as usize);
                    v___x_1319_ = leanh::lean_apply_1(v_rule_1298_, v___x_1318_);
                    v___x_1320_ = (leanh::lean_unbox(v___x_1319_) as u8);
                    if v___x_1320_ == 0 {
                        v___x_1321_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__5,
                        );
                        v___x_1322_ = lean_uint8_dec_le(v___x_1321_, v_c_1299_);
                        if v___x_1322_ == 0 {
                            v___y_1313_ = v___x_1322_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1323_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_isEncodedChar___closed__6_once
                                ),
                                _init_l_Std_Http_URI_isEncodedChar___closed__6,
                            );
                            v___x_1324_ = lean_uint8_dec_le(v_c_1299_, v___x_1323_);
                            v___y_1313_ = v___x_1324_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_1301_;
                    }
                }
            }
            1 => {
                if v___y_1303_ == 0 {
                    v___x_1304_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__0,
                    );
                    v___x_1305_ = lean_uint8_dec_eq(v_c_1299_, v___x_1304_);
                    if v___x_1305_ == 0 {
                        return v___y_1303_;
                    } else {
                        return v___x_1301_;
                    }
                } else {
                    return v___x_1301_;
                }
            }
            2 => {
                if v___y_1307_ == 0 {
                    v___x_1308_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_1309_ = lean_uint8_dec_le(v___x_1308_, v_c_1299_);
                    if v___x_1309_ == 0 {
                        v___y_1303_ = v___x_1309_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1310_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__2,
                        );
                        v___x_1311_ = lean_uint8_dec_le(v_c_1299_, v___x_1310_);
                        v___y_1303_ = v___x_1311_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1301_;
                }
            }
            3 => {
                if v___y_1313_ == 0 {
                    v___x_1314_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_1315_ = lean_uint8_dec_le(v___x_1314_, v_c_1299_);
                    if v___x_1315_ == 0 {
                        v___y_1307_ = v___x_1315_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1316_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__4,
                        );
                        v___x_1317_ = lean_uint8_dec_le(v_c_1299_, v___x_1316_);
                        v___y_1307_ = v___x_1317_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_1301_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_isEncodedChar___boxed(
    mut v_rule_1325_: *mut leanh::LeanObject,
    mut v_c_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1327_: u8 = 0;
    let mut v_res_1328_: u8 = 0;
    let mut v_r_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1327_ = (leanh::lean_unbox(v_c_1326_) as u8);
    v_res_1328_ = l_Std_Http_URI_isEncodedChar(v_rule_1325_, v_c_boxed_1327_);
    v_r_1329_ = leanh::lean_box((v_res_1328_) as usize);
    return v_r_1329_;
}
pub unsafe fn _init_l_Std_Http_URI_isEncodedQueryChar___closed__0() -> u8 {
    let mut v___x_1330_: u32 = 0;
    let mut v___x_1331_: u8 = 0;
    v___x_1330_ = 43;
    v___x_1331_ = lean_uint32_to_uint8(v___x_1330_);
    return v___x_1331_;
}
pub unsafe fn l_Std_Http_URI_isEncodedQueryChar(
    mut v_rule_1332_: *mut leanh::LeanObject,
    mut v_c_1333_: u8,
) -> u8 {
    let mut v___x_1334_: u8 = 0;
    v___x_1334_ = l_Std_Http_URI_isEncodedChar(v_rule_1332_, v_c_1333_);
    if v___x_1334_ == 0 {
        let mut v___x_1335_: u8 = 0;
        let mut v___x_1336_: u8 = 0;
        v___x_1335_ = leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedQueryChar___closed__0),
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedQueryChar___closed__0_once),
            _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
        );
        v___x_1336_ = lean_uint8_dec_eq(v_c_1333_, v___x_1335_);
        if v___x_1336_ == 0 {
            return v___x_1334_;
        } else {
            return v___x_1336_;
        }
    } else {
        return v___x_1334_;
    }
}
pub unsafe fn l_Std_Http_URI_isEncodedQueryChar___boxed(
    mut v_rule_1337_: *mut leanh::LeanObject,
    mut v_c_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1339_: u8 = 0;
    let mut v_res_1340_: u8 = 0;
    let mut v_r_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1339_ = (leanh::lean_unbox(v_c_1338_) as u8);
    v_res_1340_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_1337_, v_c_boxed_1339_);
    v_r_1341_ = leanh::lean_box((v_res_1340_) as usize);
    return v_r_1341_;
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(
    mut v_r_1342_: *mut leanh::LeanObject,
    mut v___x_1343_: u8,
    mut v_v_1344_: u8,
) -> u8 {
    let mut v___x_1345_: u8 = 0;
    v___x_1345_ = l_Std_Http_URI_isEncodedChar(v_r_1342_, v_v_1344_);
    if v___x_1345_ == 0 {
        return v___x_1343_;
    } else {
        let mut v___x_1346_: u8 = 0;
        v___x_1346_ = 0;
        return v___x_1346_;
    }
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(
    mut v_r_1347_: *mut leanh::LeanObject,
    mut v___x_1348_: *mut leanh::LeanObject,
    mut v_v_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_71__boxed_1350_: u8 = 0;
    let mut v_v_boxed_1351_: u8 = 0;
    let mut v_res_1352_: u8 = 0;
    let mut v_r_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_71__boxed_1350_ = (leanh::lean_unbox(v___x_1348_) as u8);
    v_v_boxed_1351_ = (leanh::lean_unbox(v_v_1349_) as u8);
    v_res_1352_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(
        v_r_1347_,
        v___x_71__boxed_1350_,
        v_v_boxed_1351_,
    );
    v_r_1353_ = leanh::lean_box((v_res_1352_) as usize);
    return v_r_1353_;
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedChars(
    mut v_r_1373_: *mut leanh::LeanObject,
    mut v_s_1374_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    v___x_1375_ = lean_byte_array_data(v_s_1374_);
    v___x_1376_ = leanh::lean_unsigned_to_nat(0);
    v___x_1377_ = lean_array_get_size(v___x_1375_);
    v___x_1378_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9;
    v___x_1379_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
    if v___x_1379_ == 0 {
        let mut v___x_1380_: u8 = 0;
        leanh::lean_dec_ref(v___x_1375_);
        leanh::lean_dec_ref(v_r_1373_);
        v___x_1380_ = 1;
        return v___x_1380_;
    } else {
        if v___x_1379_ == 0 {
            leanh::lean_dec_ref(v___x_1375_);
            leanh::lean_dec_ref(v_r_1373_);
            return v___x_1379_;
        } else {
            let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1383_: usize = 0;
            let mut v___x_1384_: usize = 0;
            let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: u8 = 0;
            v___x_1381_ = leanh::lean_box((v___x_1379_) as usize);
            v___f_1382_ = leanh::lean_alloc_closure(
                l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_1382_, 0, v_r_1373_);
            leanh::lean_closure_set(v___f_1382_, 1, v___x_1381_);
            v___x_1383_ = 0usize;
            v___x_1384_ = lean_usize_of_nat(v___x_1377_);
            v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1378_,
                v___f_1382_,
                v___x_1375_,
                v___x_1383_,
                v___x_1384_,
            );
            v___x_1386_ = (leanh::lean_unbox(v___x_1385_) as u8);
            leanh::lean_dec(v___x_1385_);
            if v___x_1386_ == 0 {
                return v___x_1379_;
            } else {
                let mut v___x_1387_: u8 = 0;
                v___x_1387_ = 0;
                return v___x_1387_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(
    mut v_r_1388_: *mut leanh::LeanObject,
    mut v_s_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1390_: u8 = 0;
    let mut v_r_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_1388_, v_s_1389_);
    v_r_1391_ = leanh::lean_box((v_res_1390_) as usize);
    return v_r_1391_;
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(
    mut v_r_1392_: *mut leanh::LeanObject,
    mut v___x_1393_: u8,
    mut v_v_1394_: u8,
) -> u8 {
    let mut v___x_1395_: u8 = 0;
    v___x_1395_ = l_Std_Http_URI_isEncodedQueryChar(v_r_1392_, v_v_1394_);
    if v___x_1395_ == 0 {
        return v___x_1393_;
    } else {
        let mut v___x_1396_: u8 = 0;
        v___x_1396_ = 0;
        return v___x_1396_;
    }
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(
    mut v_r_1397_: *mut leanh::LeanObject,
    mut v___x_1398_: *mut leanh::LeanObject,
    mut v_v_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_71__boxed_1400_: u8 = 0;
    let mut v_v_boxed_1401_: u8 = 0;
    let mut v_res_1402_: u8 = 0;
    let mut v_r_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_71__boxed_1400_ = (leanh::lean_unbox(v___x_1398_) as u8);
    v_v_boxed_1401_ = (leanh::lean_unbox(v_v_1399_) as u8);
    v_res_1402_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(
        v_r_1397_,
        v___x_71__boxed_1400_,
        v_v_boxed_1401_,
    );
    v_r_1403_ = leanh::lean_box((v_res_1402_) as usize);
    return v_r_1403_;
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(
    mut v_r_1404_: *mut leanh::LeanObject,
    mut v_s_1405_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    v___x_1406_ = lean_byte_array_data(v_s_1405_);
    v___x_1407_ = leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = lean_array_get_size(v___x_1406_);
    v___x_1409_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9;
    v___x_1410_ = lean_nat_dec_lt(v___x_1407_, v___x_1408_);
    if v___x_1410_ == 0 {
        let mut v___x_1411_: u8 = 0;
        leanh::lean_dec_ref(v___x_1406_);
        leanh::lean_dec_ref(v_r_1404_);
        v___x_1411_ = 1;
        return v___x_1411_;
    } else {
        if v___x_1410_ == 0 {
            leanh::lean_dec_ref(v___x_1406_);
            leanh::lean_dec_ref(v_r_1404_);
            return v___x_1410_;
        } else {
            let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1414_: usize = 0;
            let mut v___x_1415_: usize = 0;
            let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1417_: u8 = 0;
            v___x_1412_ = leanh::lean_box((v___x_1410_) as usize);
            v___f_1413_ = leanh::lean_alloc_closure(
                l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_1413_, 0, v_r_1404_);
            leanh::lean_closure_set(v___f_1413_, 1, v___x_1412_);
            v___x_1414_ = 0usize;
            v___x_1415_ = lean_usize_of_nat(v___x_1408_);
            v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1409_,
                v___f_1413_,
                v___x_1406_,
                v___x_1414_,
                v___x_1415_,
            );
            v___x_1417_ = (leanh::lean_unbox(v___x_1416_) as u8);
            leanh::lean_dec(v___x_1416_);
            if v___x_1417_ == 0 {
                return v___x_1410_;
            } else {
                let mut v___x_1418_: u8 = 0;
                v___x_1418_ = 0;
                return v___x_1418_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(
    mut v_r_1419_: *mut leanh::LeanObject,
    mut v_s_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: u8 = 0;
    let mut v_r_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_1419_, v_s_1420_);
    v_r_1422_ = leanh::lean_box((v_res_1421_) as usize);
    return v_r_1422_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(
    mut v_ba_1423_: *mut leanh::LeanObject,
    mut v_i_1424_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1430_: u8 = 0;
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: u8 = 0;
    let mut v_c_1434_: u8 = 0;
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d1_1445_: u8 = 0;
    let mut v_d2_1446_: u8 = 0;
    let mut v___y_1448_: u8 = 0;
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: u8 = 0;
    let mut v___y_1454_: u8 = 0;
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: u8 = 0;
    let mut v___y_1465_: u8 = 0;
    let mut v___y_1467_: u8 = 0;
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: u8 = 0;
    let mut v___y_1473_: u8 = 0;
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1431_ = lean_byte_array_size(v_ba_1423_);
                v___x_1432_ = lean_nat_dec_lt(v_i_1424_, v___x_1431_);
                if v___x_1432_ == 0 {
                    leanh::lean_dec(v_i_1424_);
                    v___x_1433_ = 1;
                    return v___x_1433_;
                } else {
                    v_c_1434_ = lean_byte_array_fget(v_ba_1423_, v_i_1424_);
                    v___x_1435_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__0,
                    );
                    v___x_1436_ = lean_uint8_dec_eq(v_c_1434_, v___x_1435_);
                    if v___x_1436_ == 0 {
                        v___x_1437_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1438_ = lean_nat_add(v_i_1424_, v___x_1437_);
                        leanh::lean_dec(v_i_1424_);
                        v_i_1424_ = v___x_1438_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1440_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1441_ = lean_nat_add(v_i_1424_, v___x_1440_);
                        v___x_1442_ = lean_nat_dec_lt(v___x_1441_, v___x_1431_);
                        if v___x_1442_ == 0 {
                            leanh::lean_dec(v___x_1441_);
                            leanh::lean_dec(v_i_1424_);
                            return v___x_1442_;
                        } else {
                            v___x_1443_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1444_ = lean_nat_add(v_i_1424_, v___x_1443_);
                            v_d1_1445_ = lean_byte_array_fget(v_ba_1423_, v___x_1444_);
                            leanh::lean_dec(v___x_1444_);
                            v_d2_1446_ = lean_byte_array_fget(v_ba_1423_, v___x_1441_);
                            leanh::lean_dec(v___x_1441_);
                            v___x_1478_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_isEncodedChar___closed__5_once
                                ),
                                _init_l_Std_Http_URI_isEncodedChar___closed__5,
                            );
                            v___x_1479_ = lean_uint8_dec_le(v___x_1478_, v_d1_1445_);
                            if v___x_1479_ == 0 {
                                v___y_1473_ = v___x_1479_;
                                state = 8;
                                continue;
                            } else {
                                v___x_1480_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_URI_isEncodedChar___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_URI_isEncodedChar___closed__6_once
                                    ),
                                    _init_l_Std_Http_URI_isEncodedChar___closed__6,
                                );
                                v___x_1481_ = lean_uint8_dec_le(v_d1_1445_, v___x_1480_);
                                v___y_1473_ = v___x_1481_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1426_ = leanh::lean_unsigned_to_nat(3);
                v___x_1427_ = lean_nat_add(v_i_1424_, v___x_1426_);
                leanh::lean_dec(v_i_1424_);
                v_i_1424_ = v___x_1427_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1430_ == 0 {
                    leanh::lean_dec(v_i_1424_);
                    return v___y_1430_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1448_ == 0 {
                    v___x_1449_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_1450_ = lean_uint8_dec_le(v___x_1449_, v_d2_1446_);
                    if v___x_1450_ == 0 {
                        v___y_1430_ = v___x_1450_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1451_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__2,
                        );
                        v___x_1452_ = lean_uint8_dec_le(v_d2_1446_, v___x_1451_);
                        v___y_1430_ = v___x_1452_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_1454_ == 0 {
                    v___x_1455_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_1456_ = lean_uint8_dec_le(v___x_1455_, v_d2_1446_);
                    if v___x_1456_ == 0 {
                        v___y_1448_ = v___x_1456_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1457_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__4,
                        );
                        v___x_1458_ = lean_uint8_dec_le(v_d2_1446_, v___x_1457_);
                        v___y_1448_ = v___x_1458_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1460_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_1461_ = lean_uint8_dec_le(v___x_1460_, v_d2_1446_);
                if v___x_1461_ == 0 {
                    v___y_1454_ = v___x_1461_;
                    state = 4;
                    continue;
                } else {
                    v___x_1462_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_1463_ = lean_uint8_dec_le(v_d2_1446_, v___x_1462_);
                    v___y_1454_ = v___x_1463_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_1465_ == 0 {
                    leanh::lean_dec(v_i_1424_);
                    return v___y_1465_;
                } else {
                    state = 5;
                    continue;
                }
            }
            7 => {
                if v___y_1467_ == 0 {
                    v___x_1468_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_1469_ = lean_uint8_dec_le(v___x_1468_, v_d1_1445_);
                    if v___x_1469_ == 0 {
                        v___y_1465_ = v___x_1469_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1470_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__2,
                        );
                        v___x_1471_ = lean_uint8_dec_le(v_d1_1445_, v___x_1470_);
                        v___y_1465_ = v___x_1471_;
                        state = 6;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            8 => {
                if v___y_1473_ == 0 {
                    v___x_1474_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_1475_ = lean_uint8_dec_le(v___x_1474_, v_d1_1445_);
                    if v___x_1475_ == 0 {
                        v___y_1467_ = v___x_1475_;
                        state = 7;
                        continue;
                    } else {
                        v___x_1476_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__4,
                        );
                        v___x_1477_ = lean_uint8_dec_le(v_d1_1445_, v___x_1476_);
                        v___y_1467_ = v___x_1477_;
                        state = 7;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(
    mut v_ba_1482_: *mut leanh::LeanObject,
    mut v_i_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1484_: u8 = 0;
    let mut v_r_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(
            v_ba_1482_, v_i_1483_,
        );
    leanh::lean_dec_ref(v_ba_1482_);
    v_r_1485_ = leanh::lean_box((v_res_1484_) as usize);
    return v_r_1485_;
}
pub unsafe fn l_Std_Http_URI_isValidPercentEncoding(
    mut v_ba_1486_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    v___x_1487_ = leanh::lean_unsigned_to_nat(0);
    v___x_1488_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(
            v_ba_1486_,
            v___x_1487_,
        );
    return v___x_1488_;
}
pub unsafe fn l_Std_Http_URI_isValidPercentEncoding___boxed(
    mut v_ba_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1490_: u8 = 0;
    let mut v_r_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1490_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_1489_);
    leanh::lean_dec_ref(v_ba_1489_);
    v_r_1491_ = leanh::lean_box((v_res_1490_) as usize);
    return v_r_1491_;
}
pub unsafe fn l_Std_Http_URI_hexDigit(mut v_n_1492_: u8) -> u8 {
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: u8 = 0;
    v___x_1493_ = 10;
    v___x_1494_ = lean_uint8_dec_lt(v_n_1492_, v___x_1493_);
    if v___x_1494_ == 0 {
        let mut v___x_1495_: u8 = 0;
        let mut v___x_1496_: u8 = 0;
        let mut v___x_1497_: u8 = 0;
        v___x_1495_ = lean_uint8_sub(v_n_1492_, v___x_1493_);
        v___x_1496_ = leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
            _init_l_Std_Http_URI_isEncodedChar___closed__1,
        );
        v___x_1497_ = lean_uint8_add(v___x_1495_, v___x_1496_);
        return v___x_1497_;
    } else {
        let mut v___x_1498_: u8 = 0;
        let mut v___x_1499_: u8 = 0;
        v___x_1498_ = leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
            _init_l_Std_Http_URI_isEncodedChar___closed__5,
        );
        v___x_1499_ = lean_uint8_add(v_n_1492_, v___x_1498_);
        return v___x_1499_;
    }
}
pub unsafe fn l_Std_Http_URI_hexDigit___boxed(
    mut v_n_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1501_: u8 = 0;
    let mut v_res_1502_: u8 = 0;
    let mut v_r_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1501_ = (leanh::lean_unbox(v_n_1500_) as u8);
    v_res_1502_ = l_Std_Http_URI_hexDigit(v_n_boxed_1501_);
    v_r_1503_ = leanh::lean_box((v_res_1502_) as usize);
    return v_r_1503_;
}
pub unsafe fn l_Std_Http_URI_hexDigitToUInt8_x3f(
    mut v_c_1504_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_1506_: u8 = 0;
    let mut v___y_1507_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: u8 = 0;
    let mut v___y_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___y_1528_: u8 = 0;
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1526_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_1536_ = lean_uint8_dec_le(v___x_1526_, v_c_1504_);
                if v___x_1536_ == 0 {
                    v___y_1528_ = v___x_1536_;
                    state = 3;
                    continue;
                } else {
                    v___x_1537_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_1538_ = lean_uint8_dec_le(v_c_1504_, v___x_1537_);
                    v___y_1528_ = v___x_1538_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_1507_ == 0 {
                    v___x_1508_ = leanh::lean_box(0);
                    return v___x_1508_;
                } else {
                    v___x_1509_ = lean_uint8_sub(v_c_1504_, v___y_1506_);
                    v___x_1510_ = 10;
                    v___x_1511_ = lean_uint8_add(v___x_1509_, v___x_1510_);
                    v___x_1512_ = leanh::lean_box((v___x_1511_) as usize);
                    v___x_1513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
                    return v___x_1513_;
                }
            }
            2 => {
                if v___y_1516_ == 0 {
                    v___x_1517_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_1518_ = lean_uint8_dec_le(v___x_1517_, v_c_1504_);
                    if v___x_1518_ == 0 {
                        v___y_1506_ = v___x_1517_;
                        v___y_1507_ = v___x_1518_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1519_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__2_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__2,
                        );
                        v___x_1520_ = lean_uint8_dec_le(v_c_1504_, v___x_1519_);
                        v___y_1506_ = v___x_1517_;
                        v___y_1507_ = v___x_1520_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1521_ = lean_uint8_sub(v_c_1504_, v___y_1515_);
                    v___x_1522_ = 10;
                    v___x_1523_ = lean_uint8_add(v___x_1521_, v___x_1522_);
                    v___x_1524_ = leanh::lean_box((v___x_1523_) as usize);
                    v___x_1525_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1525_, 0, v___x_1524_);
                    return v___x_1525_;
                }
            }
            3 => {
                if v___y_1528_ == 0 {
                    v___x_1529_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_1530_ = lean_uint8_dec_le(v___x_1529_, v_c_1504_);
                    if v___x_1530_ == 0 {
                        v___y_1515_ = v___x_1529_;
                        v___y_1516_ = v___x_1530_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1531_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4),
                            core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__4_once),
                            _init_l_Std_Http_URI_isEncodedChar___closed__4,
                        );
                        v___x_1532_ = lean_uint8_dec_le(v_c_1504_, v___x_1531_);
                        v___y_1515_ = v___x_1529_;
                        v___y_1516_ = v___x_1532_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1533_ = lean_uint8_sub(v_c_1504_, v___x_1526_);
                    v___x_1534_ = leanh::lean_box((v___x_1533_) as usize);
                    v___x_1535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
                    return v___x_1535_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(
    mut v_c_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1540_: u8 = 0;
    let mut v_res_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1540_ = (leanh::lean_unbox(v_c_1539_) as u8);
    v_res_1541_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_1540_);
    return v_res_1541_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(
    mut v_x_1542_: *mut leanh::LeanObject,
    mut v_x_1543_: u8,
    mut v_h__1_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_data_1545_ = lean_byte_array_data(v_x_1542_);
    v___x_1546_ = leanh::lean_box((v_x_1543_) as usize);
    v___x_1547_ = leanh::lean_apply_2(v_h__1_1544_, v_data_1545_, v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(
    mut v_x_1548_: *mut leanh::LeanObject,
    mut v_x_1549_: *mut leanh::LeanObject,
    mut v_h__1_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_1551_: u8 = 0;
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1551_ = (leanh::lean_unbox(v_x_1549_) as u8);
    v_res_1552_ =
        l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(
            v_x_1548_,
            v_x_17__boxed_1551_,
            v_h__1_1550_,
        );
    return v_res_1552_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(
    mut v_motive_1553_: *mut leanh::LeanObject,
    mut v_x_1554_: *mut leanh::LeanObject,
    mut v_x_1555_: u8,
    mut v_h__1_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_data_1557_ = lean_byte_array_data(v_x_1554_);
    v___x_1558_ = leanh::lean_box((v_x_1555_) as usize);
    v___x_1559_ = leanh::lean_apply_2(v_h__1_1556_, v_data_1557_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(
    mut v_motive_1560_: *mut leanh::LeanObject,
    mut v_x_1561_: *mut leanh::LeanObject,
    mut v_x_1562_: *mut leanh::LeanObject,
    mut v_h__1_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_29__boxed_1564_: u8 = 0;
    let mut v_res_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_29__boxed_1564_ = (leanh::lean_unbox(v_x_1562_) as u8);
    v_res_1565_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(
        v_motive_1560_,
        v_x_1561_,
        v_x_29__boxed_1564_,
        v_h__1_1563_,
    );
    return v_res_1565_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(
    mut v_x_1566_: *mut leanh::LeanObject,
    mut v_x_1567_: *mut leanh::LeanObject,
    mut v_h__1_1568_: *mut leanh::LeanObject,
    mut v_h__2_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1566_) == 0 {
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1569_);
        v___x_1570_ = leanh::lean_apply_1(v_h__1_1568_, v_x_1567_);
        return v___x_1570_;
    } else {
        let mut v_head_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1568_);
        v_head_1571_ = leanh::lean_ctor_get(v_x_1566_, 0);
        leanh::lean_inc(v_head_1571_);
        v_tail_1572_ = leanh::lean_ctor_get(v_x_1566_, 1);
        leanh::lean_inc(v_tail_1572_);
        leanh::lean_dec_ref_known(v_x_1566_, 2);
        v___x_1573_ =
            leanh::lean_apply_3(v_h__2_1569_, v_head_1571_, v_tail_1572_, v_x_1567_);
        return v___x_1573_;
    }
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(
    mut v_motive_1574_: *mut leanh::LeanObject,
    mut v_x_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
    mut v_h__1_1577_: *mut leanh::LeanObject,
    mut v_h__2_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1575_) == 0 {
        let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1578_);
        v___x_1579_ = leanh::lean_apply_1(v_h__1_1577_, v_x_1576_);
        return v___x_1579_;
    } else {
        let mut v_head_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1577_);
        v_head_1580_ = leanh::lean_ctor_get(v_x_1575_, 0);
        leanh::lean_inc(v_head_1580_);
        v_tail_1581_ = leanh::lean_ctor_get(v_x_1575_, 1);
        leanh::lean_inc(v_tail_1581_);
        leanh::lean_dec_ref_known(v_x_1575_, 2);
        v___x_1582_ =
            leanh::lean_apply_3(v_h__2_1578_, v_head_1580_, v_tail_1581_, v_x_1576_);
        return v___x_1582_;
    }
}
pub unsafe fn l_Std_Http_URI_EncodedString_empty(
    mut v_r_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_ByteArray_empty;
    return v___x_1584_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_empty___boxed(
    mut v_r_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_Std_Http_URI_EncodedString_empty(v_r_1585_);
    leanh::lean_dec_ref(v_r_1585_);
    return v_res_1586_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instInhabited(
    mut v_r_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = l_ByteArray_empty;
    return v___x_1588_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instInhabited___boxed(
    mut v_r_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_1589_);
    leanh::lean_dec_ref(v_r_1589_);
    return v_res_1590_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(
    mut v_s_1591_: *mut leanh::LeanObject,
    mut v_c_1592_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_byte_array_push(v_s_1591_, v_c_1592_);
    return v___x_1593_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(
    mut v_s_1594_: *mut leanh::LeanObject,
    mut v_c_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1596_: u8 = 0;
    let mut v_res_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1596_ = (leanh::lean_unbox(v_c_1595_) as u8);
    v_res_1597_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(
            v_s_1594_,
            v_c_boxed_1596_,
        );
    return v_res_1597_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(
    mut v_r_1598_: *mut leanh::LeanObject,
    mut v_s_1599_: *mut leanh::LeanObject,
    mut v_c_1600_: u8,
    mut v_h_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = lean_byte_array_push(v_s_1599_, v_c_1600_);
    return v___x_1602_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(
    mut v_r_1603_: *mut leanh::LeanObject,
    mut v_s_1604_: *mut leanh::LeanObject,
    mut v_c_1605_: *mut leanh::LeanObject,
    mut v_h_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1607_: u8 = 0;
    let mut v_res_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1607_ = (leanh::lean_unbox(v_c_1605_) as u8);
    v_res_1608_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(
        v_r_1603_,
        v_s_1604_,
        v_c_boxed_1607_,
        v_h_1606_,
    );
    leanh::lean_dec_ref(v_r_1603_);
    return v_res_1608_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(
    mut v_b_1609_: u8,
    mut v_s_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: u8 = 0;
    let mut v_ba_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0_once),
        _init_l_Std_Http_URI_isEncodedChar___closed__0,
    );
    v___x_1612_ = lean_byte_array_push(v_s_1610_, v___x_1611_);
    v___x_1613_ = 4;
    v___x_1614_ = lean_uint8_shift_right(v_b_1609_, v___x_1613_);
    v___x_1615_ = l_Std_Http_URI_hexDigit(v___x_1614_);
    v___x_1616_ = lean_byte_array_push(v___x_1612_, v___x_1615_);
    v___x_1617_ = 15;
    v___x_1618_ = lean_uint8_land(v_b_1609_, v___x_1617_);
    v___x_1619_ = l_Std_Http_URI_hexDigit(v___x_1618_);
    v_ba_1620_ = lean_byte_array_push(v___x_1616_, v___x_1619_);
    return v_ba_1620_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(
    mut v_b_1621_: *mut leanh::LeanObject,
    mut v_s_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1623_: u8 = 0;
    let mut v_res_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1623_ = (leanh::lean_unbox(v_b_1621_) as u8);
    v_res_1624_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(
            v_b_boxed_1623_,
            v_s_1622_,
        );
    return v_res_1624_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(
    mut v_r_1625_: *mut leanh::LeanObject,
    mut v_b_1626_: u8,
    mut v_s_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(
            v_b_1626_, v_s_1627_,
        );
    return v___x_1628_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(
    mut v_r_1629_: *mut leanh::LeanObject,
    mut v_b_1630_: *mut leanh::LeanObject,
    mut v_s_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1632_ = (leanh::lean_unbox(v_b_1630_) as u8);
    v_res_1633_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(
        v_r_1629_,
        v_b_boxed_1632_,
        v_s_1631_,
    );
    leanh::lean_dec_ref(v_r_1629_);
    return v_res_1633_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(
    mut v_r_1634_: *mut leanh::LeanObject,
    mut v_as_1635_: *mut leanh::LeanObject,
    mut v_i_1636_: usize,
    mut v_stop_1637_: usize,
    mut v_b_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: usize = 0;
    let mut v___x_1642_: usize = 0;
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1644_ = lean_usize_dec_eq(v_i_1636_, v_stop_1637_);
                if v___x_1644_ == 0 {
                    v___x_1645_ = lean_byte_array_uget(v_as_1635_, v_i_1636_);
                    v___x_1646_ = 128;
                    v___x_1647_ = lean_uint8_dec_lt(v___x_1645_, v___x_1646_);
                    if v___x_1647_ == 0 {
                        v___x_1648_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_1645_, v_b_1638_);
                        v___y_1640_ = v___x_1648_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1649_ = leanh::lean_box((v___x_1645_) as usize);
                        leanh::lean_inc_ref(v_r_1634_);
                        v___x_1650_ = leanh::lean_apply_1(v_r_1634_, v___x_1649_);
                        v___x_1651_ = (leanh::lean_unbox(v___x_1650_) as u8);
                        if v___x_1651_ == 0 {
                            v___x_1652_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_1645_, v_b_1638_);
                            v___y_1640_ = v___x_1652_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1653_ = lean_byte_array_push(v_b_1638_, v___x_1645_);
                            v___y_1640_ = v___x_1653_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_r_1634_);
                    return v_b_1638_;
                }
            }
            1 => {
                v___x_1641_ = 1usize;
                v___x_1642_ = lean_usize_add(v_i_1636_, v___x_1641_);
                v_i_1636_ = v___x_1642_;
                v_b_1638_ = v___y_1640_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(
    mut v_r_1654_: *mut leanh::LeanObject,
    mut v_as_1655_: *mut leanh::LeanObject,
    mut v_i_1656_: *mut leanh::LeanObject,
    mut v_stop_1657_: *mut leanh::LeanObject,
    mut v_b_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1659_: usize = 0;
    let mut v_stop_boxed_1660_: usize = 0;
    let mut v_res_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1659_ = leanh::lean_unbox_usize(v_i_1656_);
    leanh::lean_dec(v_i_1656_);
    v_stop_boxed_1660_ = leanh::lean_unbox_usize(v_stop_1657_);
    leanh::lean_dec(v_stop_1657_);
    v_res_1661_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(
        v_r_1654_,
        v_as_1655_,
        v_i_boxed_1659_,
        v_stop_boxed_1660_,
        v_b_1658_,
    );
    leanh::lean_dec_ref(v_as_1655_);
    return v_res_1661_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_encode(
    mut v_r_1662_: *mut leanh::LeanObject,
    mut v_s_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    v___x_1664_ = l_ByteArray_empty;
    v___x_1665_ = lean_string_to_utf8(v_s_1663_);
    v___x_1666_ = leanh::lean_unsigned_to_nat(0);
    v___x_1667_ = lean_byte_array_size(v___x_1665_);
    v___x_1668_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
    if v___x_1668_ == 0 {
        leanh::lean_dec_ref(v___x_1665_);
        leanh::lean_dec_ref(v_r_1662_);
        return v___x_1664_;
    } else {
        let mut v___x_1669_: u8 = 0;
        v___x_1669_ = lean_nat_dec_le(v___x_1667_, v___x_1667_);
        if v___x_1669_ == 0 {
            if v___x_1668_ == 0 {
                leanh::lean_dec_ref(v___x_1665_);
                leanh::lean_dec_ref(v_r_1662_);
                return v___x_1664_;
            } else {
                let mut v___x_1670_: usize = 0;
                let mut v___x_1671_: usize = 0;
                let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1670_ = 0usize;
                v___x_1671_ = lean_usize_of_nat(v___x_1667_);
                v___x_1672_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_1662_, v___x_1665_, v___x_1670_, v___x_1671_, v___x_1664_);
                leanh::lean_dec_ref(v___x_1665_);
                return v___x_1672_;
            }
        } else {
            let mut v___x_1673_: usize = 0;
            let mut v___x_1674_: usize = 0;
            let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1673_ = 0usize;
            v___x_1674_ = lean_usize_of_nat(v___x_1667_);
            v___x_1675_ =
                l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(
                    v_r_1662_,
                    v___x_1665_,
                    v___x_1673_,
                    v___x_1674_,
                    v___x_1664_,
                );
            leanh::lean_dec_ref(v___x_1665_);
            return v___x_1675_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedString_encode___boxed(
    mut v_r_1676_: *mut leanh::LeanObject,
    mut v_s_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Std_Http_URI_EncodedString_encode(v_r_1676_, v_s_1677_);
    leanh::lean_dec_ref(v_s_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofByteArray_x3f(
    mut v_r_1679_: *mut leanh::LeanObject,
    mut v_ba_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: u8 = 0;
    leanh::lean_inc_ref(v_ba_1680_);
    v___x_1681_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_1679_, v_ba_1680_);
    if v___x_1681_ == 0 {
        let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ba_1680_);
        v___x_1682_ = leanh::lean_box(0);
        return v___x_1682_;
    } else {
        let mut v___x_1683_: u8 = 0;
        v___x_1683_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_1680_);
        if v___x_1683_ == 0 {
            let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_ba_1680_);
            v___x_1684_ = leanh::lean_box(0);
            return v___x_1684_;
        } else {
            let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1685_, 0, v_ba_1680_);
            return v___x_1685_;
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(
    mut v_msg_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_ByteArray_empty;
    v___x_1688_ = lean_panic_fn_borrowed(v___x_1687_, v_msg_1686_);
    return v___x_1688_;
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(
    mut v_r_1689_: *mut leanh::LeanObject,
    mut v_msg_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ =
        l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_1690_);
    return v___x_1691_;
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(
    mut v_r_1692_: *mut leanh::LeanObject,
    mut v_msg_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ =
        l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_1692_, v_msg_1693_);
    leanh::lean_dec_ref(v_r_1692_);
    return v_res_1694_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2;
    v___x_1699_ = leanh::lean_unsigned_to_nat(12);
    v___x_1700_ = leanh::lean_unsigned_to_nat(320);
    v___x_1701_ = l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1;
    v___x_1702_ = l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0;
    v___x_1703_ = l_mkPanicMessageWithDecl(
        v___x_1702_,
        v___x_1701_,
        v___x_1700_,
        v___x_1699_,
        v___x_1698_,
    );
    return v___x_1703_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofByteArray_x21(
    mut v_r_1704_: *mut leanh::LeanObject,
    mut v_ba_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_1704_, v_ba_1705_);
    if leanh::lean_obj_tag(v___x_1706_) == 0 {
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1707_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3),
            core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once),
            _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3,
        );
        v___x_1708_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(
            v___x_1707_,
        );
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1709_ = leanh::lean_ctor_get(v___x_1706_, 0);
        leanh::lean_inc(v_val_1709_);
        leanh::lean_dec_ref_known(v___x_1706_, 1);
        return v_val_1709_;
    }
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofString_x3f(
    mut v_r_1710_: *mut leanh::LeanObject,
    mut v_s_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = lean_string_to_utf8(v_s_1711_);
    v___x_1713_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_1710_, v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofString_x3f___boxed(
    mut v_r_1714_: *mut leanh::LeanObject,
    mut v_s_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_1714_, v_s_1715_);
    leanh::lean_dec_ref(v_s_1715_);
    return v_res_1716_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofString_x21(
    mut v_r_1717_: *mut leanh::LeanObject,
    mut v_s_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = lean_string_to_utf8(v_s_1718_);
    v___x_1720_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_1717_, v___x_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_ofString_x21___boxed(
    mut v_r_1721_: *mut leanh::LeanObject,
    mut v_s_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1723_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_1721_, v_s_1722_);
    leanh::lean_dec_ref(v_s_1722_);
    return v_res_1723_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_new___redArg(
    mut v_ba_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_ba_1724_);
    return v_ba_1724_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_new___redArg___boxed(
    mut v_ba_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_1725_);
    leanh::lean_dec_ref(v_ba_1725_);
    return v_res_1726_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_new(
    mut v_r_1727_: *mut leanh::LeanObject,
    mut v_ba_1728_: *mut leanh::LeanObject,
    mut v_valid_1729_: *mut leanh::LeanObject,
    mut v___validEncoding_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_ba_1728_);
    return v_ba_1728_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_new___boxed(
    mut v_r_1731_: *mut leanh::LeanObject,
    mut v_ba_1732_: *mut leanh::LeanObject,
    mut v_valid_1733_: *mut leanh::LeanObject,
    mut v___validEncoding_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1735_ = l_Std_Http_URI_EncodedString_new(
        v_r_1731_,
        v_ba_1732_,
        v_valid_1733_,
        v___validEncoding_1734_,
    );
    leanh::lean_dec_ref(v_ba_1732_);
    leanh::lean_dec_ref(v_r_1731_);
    return v_res_1735_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instToString___lam__0(
    mut v_es_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = lean_string_from_utf8_unchecked(v_es_1736_);
    return v___x_1737_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instToString(
    mut v_r_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1740_ = l_Std_Http_URI_EncodedString_instToString___closed__0;
    return v___f_1740_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instToString___boxed(
    mut v_r_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1742_ = l_Std_Http_URI_EncodedString_instToString(v_r_1741_);
    leanh::lean_dec_ref(v_r_1741_);
    return v_res_1742_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(
    mut v_len_1743_: *mut leanh::LeanObject,
    mut v_rawBytes_1744_: *mut leanh::LeanObject,
    mut v_a_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_percent_1755_: u8 = 0;
    let mut v___x_1756_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1746_ = leanh::lean_ctor_get(v_a_1745_, 0);
                v_snd_1747_ = leanh::lean_ctor_get(v_a_1745_, 1);
                v_isSharedCheck_1805_ = (!leanh::lean_is_exclusive(v_a_1745_)) as u8;
                if v_isSharedCheck_1805_ == 0 {
                    v___x_1749_ = v_a_1745_;
                    v_isShared_1750_ = v_isSharedCheck_1805_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1747_);
                    leanh::lean_inc(v_fst_1746_);
                    leanh::lean_dec(v_a_1745_);
                    v___x_1749_ = leanh::lean_box(0);
                    v_isShared_1750_ = v_isSharedCheck_1805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1751_ = lean_nat_dec_lt(v_snd_1747_, v_len_1743_);
                if v___x_1751_ == 0 {
                    if v_isShared_1750_ == 0 {
                        v___x_1753_ = v___x_1749_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1754_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_fst_1746_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_snd_1747_);
                        v___x_1753_ = v_reuseFailAlloc_1754_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_percent_1755_ = 37;
                    v___x_1756_ = lean_byte_array_fget(v_rawBytes_1744_, v_snd_1747_);
                    v___x_1765_ = lean_uint8_dec_eq(v___x_1756_, v_percent_1755_);
                    if v___x_1765_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_1766_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1767_ = lean_nat_add(v_snd_1747_, v___x_1766_);
                        v___x_1768_ = lean_nat_dec_lt(v___x_1767_, v_len_1743_);
                        if v___x_1768_ == 0 {
                            leanh::lean_dec(v___x_1767_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_1749_);
                            v___x_1769_ = lean_byte_array_fget(v_rawBytes_1744_, v___x_1767_);
                            leanh::lean_dec(v___x_1767_);
                            v___x_1770_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_1769_);
                            if leanh::lean_obj_tag(v___x_1770_) == 1 {
                                v_val_1771_ = leanh::lean_ctor_get(v___x_1770_, 0);
                                leanh::lean_inc(v_val_1771_);
                                leanh::lean_dec_ref_known(v___x_1770_, 1);
                                v___x_1772_ = leanh::lean_unsigned_to_nat(2);
                                v___x_1773_ = lean_nat_add(v_snd_1747_, v___x_1772_);
                                v___x_1774_ = lean_nat_dec_lt(v___x_1773_, v_len_1743_);
                                if v___x_1774_ == 0 {
                                    leanh::lean_dec(v_val_1771_);
                                    leanh::lean_dec(v_snd_1747_);
                                    v___x_1775_ = lean_byte_array_push(v_fst_1746_, v___x_1756_);
                                    v___x_1776_ = lean_byte_array_push(v___x_1775_, v___x_1769_);
                                    v___x_1777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1777_, 0, v___x_1776_);
                                    leanh::lean_ctor_set(v___x_1777_, 1, v___x_1773_);
                                    v_a_1745_ = v___x_1777_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_1779_ =
                                        lean_byte_array_fget(v_rawBytes_1744_, v___x_1773_);
                                    leanh::lean_dec(v___x_1773_);
                                    v___x_1780_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_1779_);
                                    if leanh::lean_obj_tag(v___x_1780_) == 1 {
                                        v_val_1781_ = leanh::lean_ctor_get(v___x_1780_, 0);
                                        leanh::lean_inc(v_val_1781_);
                                        leanh::lean_dec_ref_known(v___x_1780_, 1);
                                        v___x_1782_ = 4;
                                        v___x_1783_ = (leanh::lean_unbox(v_val_1771_) as u8);
                                        leanh::lean_dec(v_val_1771_);
                                        v___x_1784_ =
                                            lean_uint8_shift_left(v___x_1783_, v___x_1782_);
                                        v___x_1785_ = (leanh::lean_unbox(v_val_1781_) as u8);
                                        leanh::lean_dec(v_val_1781_);
                                        v___x_1786_ = lean_uint8_add(v___x_1784_, v___x_1785_);
                                        v___x_1787_ =
                                            lean_byte_array_push(v_fst_1746_, v___x_1786_);
                                        v___x_1788_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_1789_ = lean_nat_add(v_snd_1747_, v___x_1788_);
                                        leanh::lean_dec(v_snd_1747_);
                                        v___x_1790_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1790_, 0, v___x_1787_);
                                        leanh::lean_ctor_set(v___x_1790_, 1, v___x_1789_);
                                        v_a_1745_ = v___x_1790_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1780_);
                                        leanh::lean_dec(v_val_1771_);
                                        v___x_1792_ =
                                            lean_byte_array_push(v_fst_1746_, v___x_1756_);
                                        v___x_1793_ =
                                            lean_byte_array_push(v___x_1792_, v___x_1769_);
                                        v___x_1794_ =
                                            lean_byte_array_push(v___x_1793_, v___x_1779_);
                                        v___x_1795_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_1796_ = lean_nat_add(v_snd_1747_, v___x_1795_);
                                        leanh::lean_dec(v_snd_1747_);
                                        v___x_1797_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1797_, 0, v___x_1794_);
                                        leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                                        v_a_1745_ = v___x_1797_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_1770_);
                                v___x_1799_ = lean_byte_array_push(v_fst_1746_, v___x_1756_);
                                v___x_1800_ = lean_byte_array_push(v___x_1799_, v___x_1769_);
                                v___x_1801_ = leanh::lean_unsigned_to_nat(2);
                                v___x_1802_ = lean_nat_add(v_snd_1747_, v___x_1801_);
                                leanh::lean_dec(v_snd_1747_);
                                v___x_1803_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1803_, 0, v___x_1800_);
                                leanh::lean_ctor_set(v___x_1803_, 1, v___x_1802_);
                                v_a_1745_ = v___x_1803_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1753_;
            }
            3 => {
                v___x_1758_ = lean_byte_array_push(v_fst_1746_, v___x_1756_);
                v___x_1759_ = leanh::lean_unsigned_to_nat(1);
                v___x_1760_ = lean_nat_add(v_snd_1747_, v___x_1759_);
                leanh::lean_dec(v_snd_1747_);
                if v_isShared_1750_ == 0 {
                    leanh::lean_ctor_set(v___x_1749_, 1, v___x_1760_);
                    leanh::lean_ctor_set(v___x_1749_, 0, v___x_1758_);
                    v___x_1762_ = v___x_1749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1760_);
                    v___x_1762_ = v_reuseFailAlloc_1764_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1745_ = v___x_1762_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(
    mut v_len_1806_: *mut leanh::LeanObject,
    mut v_rawBytes_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_1806_, v_rawBytes_1807_, v_a_1808_);
    leanh::lean_dec_ref(v_rawBytes_1807_);
    leanh::lean_dec(v_len_1806_);
    return v_res_1809_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_i_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decoded_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_1810_ = leanh::lean_unsigned_to_nat(0);
    v_decoded_1811_ = l_ByteArray_empty;
    v___x_1812_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v_decoded_1811_);
    leanh::lean_ctor_set(v___x_1812_, 1, v_i_1810_);
    return v___x_1812_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_decode___redArg(
    mut v_es_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_len_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    v_len_1814_ = lean_byte_array_size(v_es_1813_);
    v___x_1815_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_decode___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once),
        _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0,
    );
    v___x_1816_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_1814_, v_es_1813_, v___x_1815_);
    v_fst_1817_ = leanh::lean_ctor_get(v___x_1816_, 0);
    leanh::lean_inc(v_fst_1817_);
    leanh::lean_dec_ref(v___x_1816_);
    v___x_1818_ = lean_string_validate_utf8(v_fst_1817_);
    if v___x_1818_ == 0 {
        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_1817_);
        v___x_1819_ = leanh::lean_box(0);
        return v___x_1819_;
    } else {
        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1820_ = lean_string_from_utf8_unchecked(v_fst_1817_);
        v___x_1821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
        return v___x_1821_;
    }
}
pub unsafe fn l_Std_Http_URI_EncodedString_decode___redArg___boxed(
    mut v_es_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_1822_);
    leanh::lean_dec_ref(v_es_1822_);
    return v_res_1823_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_decode(
    mut v_r_1824_: *mut leanh::LeanObject,
    mut v_es_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_1825_);
    return v___x_1826_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_decode___boxed(
    mut v_r_1827_: *mut leanh::LeanObject,
    mut v_es_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Std_Http_URI_EncodedString_decode(v_r_1827_, v_es_1828_);
    leanh::lean_dec_ref(v_es_1828_);
    leanh::lean_dec_ref(v_r_1827_);
    return v_res_1829_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(
    mut v_len_1830_: *mut leanh::LeanObject,
    mut v_rawBytes_1831_: *mut leanh::LeanObject,
    mut v_inst_1832_: *mut leanh::LeanObject,
    mut v_a_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_1830_, v_rawBytes_1831_, v_a_1833_);
    return v___x_1834_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(
    mut v_len_1835_: *mut leanh::LeanObject,
    mut v_rawBytes_1836_: *mut leanh::LeanObject,
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(
            v_len_1835_,
            v_rawBytes_1836_,
            v_inst_1837_,
            v_a_1838_,
        );
    leanh::lean_dec_ref(v_rawBytes_1836_);
    leanh::lean_dec(v_len_1835_);
    return v_res_1839_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instRepr___lam__0(
    mut v_es_1840_: *mut leanh::LeanObject,
    mut v_n_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = lean_string_from_utf8_unchecked(v_es_1840_);
    v___x_1843_ = l_String_quote(v___x_1842_);
    v___x_1844_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1844_, 0, v___x_1843_);
    return v___x_1844_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(
    mut v_es_1845_: *mut leanh::LeanObject,
    mut v_n_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_1845_, v_n_1846_);
    leanh::lean_dec(v_n_1846_);
    return v_res_1847_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instRepr(
    mut v_r_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1850_ = l_Std_Http_URI_EncodedString_instRepr___closed__0;
    return v___f_1850_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instRepr___boxed(
    mut v_r_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Std_Http_URI_EncodedString_instRepr(v_r_1851_);
    leanh::lean_dec_ref(v_r_1851_);
    return v_res_1852_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instBEq(
    mut v_r_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1855_ = l_Std_Http_URI_EncodedString_instBEq___closed__0;
    return v___f_1855_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instBEq___boxed(
    mut v_r_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_Http_URI_EncodedString_instBEq(v_r_1856_);
    leanh::lean_dec_ref(v_r_1856_);
    return v_res_1857_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instHashable(
    mut v_r_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1860_ = l_Std_Http_URI_EncodedString_instHashable___closed__0;
    return v___f_1860_;
}
pub unsafe fn l_Std_Http_URI_EncodedString_instHashable___boxed(
    mut v_r_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l_Std_Http_URI_EncodedString_instHashable(v_r_1861_);
    leanh::lean_dec_ref(v_r_1861_);
    return v_res_1862_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_empty(
    mut v_r_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = l_ByteArray_empty;
    return v___x_1864_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_empty___boxed(
    mut v_r_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_1865_);
    leanh::lean_dec_ref(v_r_1865_);
    return v_res_1866_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_instInhabited(
    mut v_r_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_ByteArray_empty;
    return v___x_1868_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(
    mut v_r_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_1869_);
    leanh::lean_dec_ref(v_r_1869_);
    return v_res_1870_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(
    mut v_s_1871_: *mut leanh::LeanObject,
    mut v_c_1872_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = lean_byte_array_push(v_s_1871_, v_c_1872_);
    return v___x_1873_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(
    mut v_s_1874_: *mut leanh::LeanObject,
    mut v_c_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1876_: u8 = 0;
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1876_ = (leanh::lean_unbox(v_c_1875_) as u8);
    v_res_1877_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(
            v_s_1874_,
            v_c_boxed_1876_,
        );
    return v_res_1877_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(
    mut v_r_1878_: *mut leanh::LeanObject,
    mut v_s_1879_: *mut leanh::LeanObject,
    mut v_c_1880_: u8,
    mut v_h_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = lean_byte_array_push(v_s_1879_, v_c_1880_);
    return v___x_1882_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(
    mut v_r_1883_: *mut leanh::LeanObject,
    mut v_s_1884_: *mut leanh::LeanObject,
    mut v_c_1885_: *mut leanh::LeanObject,
    mut v_h_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1887_: u8 = 0;
    let mut v_res_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1887_ = (leanh::lean_unbox(v_c_1885_) as u8);
    v_res_1888_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(
        v_r_1883_,
        v_s_1884_,
        v_c_boxed_1887_,
        v_h_1886_,
    );
    leanh::lean_dec_ref(v_r_1883_);
    return v_res_1888_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(
    mut v_ba_1889_: *mut leanh::LeanObject,
    mut v_r_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: u8 = 0;
    leanh::lean_inc_ref(v_ba_1889_);
    v___x_1891_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_1890_, v_ba_1889_);
    if v___x_1891_ == 0 {
        let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ba_1889_);
        v___x_1892_ = leanh::lean_box(0);
        return v___x_1892_;
    } else {
        let mut v___x_1893_: u8 = 0;
        v___x_1893_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_1889_);
        if v___x_1893_ == 0 {
            let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_ba_1889_);
            v___x_1894_ = leanh::lean_box(0);
            return v___x_1894_;
        } else {
            let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1895_, 0, v_ba_1889_);
            return v___x_1895_;
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(
    mut v_msg_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_ByteArray_empty;
    v___x_1898_ = lean_panic_fn_borrowed(v___x_1897_, v_msg_1896_);
    return v___x_1898_;
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(
    mut v_r_1899_: *mut leanh::LeanObject,
    mut v_msg_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(
        v_msg_1900_,
    );
    return v___x_1901_;
}
pub unsafe fn l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(
    mut v_r_1902_: *mut leanh::LeanObject,
    mut v_msg_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(
        v_r_1902_,
        v_msg_1903_,
    );
    leanh::lean_dec_ref(v_r_1902_);
    return v_res_1904_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1;
    v___x_1908_ = leanh::lean_unsigned_to_nat(12);
    v___x_1909_ = leanh::lean_unsigned_to_nat(438);
    v___x_1910_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0;
    v___x_1911_ = l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0;
    v___x_1912_ = l_mkPanicMessageWithDecl(
        v___x_1911_,
        v___x_1910_,
        v___x_1909_,
        v___x_1908_,
        v___x_1907_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(
    mut v_ba_1913_: *mut leanh::LeanObject,
    mut v_r_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1913_, v_r_1914_);
    if leanh::lean_obj_tag(v___x_1915_) == 0 {
        let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1916_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2),
            core::ptr::addr_of_mut!(
                l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once
            ),
            _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2,
        );
        v___x_1917_ =
            l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(
                v___x_1916_,
            );
        return v___x_1917_;
    } else {
        let mut v_val_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1918_ = leanh::lean_ctor_get(v___x_1915_, 0);
        leanh::lean_inc(v_val_1918_);
        leanh::lean_dec_ref_known(v___x_1915_, 1);
        return v_val_1918_;
    }
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofString_x3f(
    mut v_s_1919_: *mut leanh::LeanObject,
    mut v_r_1920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ = lean_string_to_utf8(v_s_1919_);
    v___x_1922_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_1921_, v_r_1920_);
    return v___x_1922_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(
    mut v_s_1923_: *mut leanh::LeanObject,
    mut v_r_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1923_, v_r_1924_);
    leanh::lean_dec_ref(v_s_1923_);
    return v_res_1925_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofString_x21(
    mut v_s_1926_: *mut leanh::LeanObject,
    mut v_r_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = lean_string_to_utf8(v_s_1926_);
    v___x_1929_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_1928_, v_r_1927_);
    return v___x_1929_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(
    mut v_s_1930_: *mut leanh::LeanObject,
    mut v_r_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1932_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_1930_, v_r_1931_);
    leanh::lean_dec_ref(v_s_1930_);
    return v_res_1932_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_new___redArg(
    mut v_ba_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_ba_1933_);
    return v_ba_1933_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(
    mut v_ba_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_1934_);
    leanh::lean_dec_ref(v_ba_1934_);
    return v_res_1935_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_new(
    mut v_r_1936_: *mut leanh::LeanObject,
    mut v_ba_1937_: *mut leanh::LeanObject,
    mut v_valid_1938_: *mut leanh::LeanObject,
    mut v___validEncoding_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_ba_1937_);
    return v_ba_1937_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_new___boxed(
    mut v_r_1940_: *mut leanh::LeanObject,
    mut v_ba_1941_: *mut leanh::LeanObject,
    mut v_valid_1942_: *mut leanh::LeanObject,
    mut v___validEncoding_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l_Std_Http_URI_EncodedQueryString_new(
        v_r_1940_,
        v_ba_1941_,
        v_valid_1942_,
        v___validEncoding_1943_,
    );
    leanh::lean_dec_ref(v_ba_1941_);
    leanh::lean_dec_ref(v_r_1940_);
    return v_res_1944_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(
    mut v_b_1945_: u8,
    mut v_s_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v_ba_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__0_once),
        _init_l_Std_Http_URI_isEncodedChar___closed__0,
    );
    v___x_1948_ = lean_byte_array_push(v_s_1946_, v___x_1947_);
    v___x_1949_ = 4;
    v___x_1950_ = lean_uint8_shift_right(v_b_1945_, v___x_1949_);
    v___x_1951_ = l_Std_Http_URI_hexDigit(v___x_1950_);
    v___x_1952_ = lean_byte_array_push(v___x_1948_, v___x_1951_);
    v___x_1953_ = 15;
    v___x_1954_ = lean_uint8_land(v_b_1945_, v___x_1953_);
    v___x_1955_ = l_Std_Http_URI_hexDigit(v___x_1954_);
    v_ba_1956_ = lean_byte_array_push(v___x_1952_, v___x_1955_);
    return v_ba_1956_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(
    mut v_b_1957_: *mut leanh::LeanObject,
    mut v_s_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1959_: u8 = 0;
    let mut v_res_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1959_ = (leanh::lean_unbox(v_b_1957_) as u8);
    v_res_1960_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_1959_, v_s_1958_);
    return v_res_1960_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(
    mut v_r_1961_: *mut leanh::LeanObject,
    mut v_b_1962_: u8,
    mut v_s_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_1962_, v_s_1963_);
    return v___x_1964_;
}
pub unsafe fn l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(
    mut v_r_1965_: *mut leanh::LeanObject,
    mut v_b_1966_: *mut leanh::LeanObject,
    mut v_s_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1968_: u8 = 0;
    let mut v_res_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1968_ = (leanh::lean_unbox(v_b_1966_) as u8);
    v_res_1969_ =
        l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(
            v_r_1965_,
            v_b_boxed_1968_,
            v_s_1967_,
        );
    leanh::lean_dec_ref(v_r_1965_);
    return v_res_1969_;
}
pub unsafe fn _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0()
-> u8 {
    let mut v___x_1970_: u32 = 0;
    let mut v___x_1971_: u8 = 0;
    v___x_1970_ = 32;
    v___x_1971_ = lean_uint32_to_uint8(v___x_1970_);
    return v___x_1971_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(
    mut v_r_1972_: *mut leanh::LeanObject,
    mut v_as_1973_: *mut leanh::LeanObject,
    mut v_i_1974_: usize,
    mut v_stop_1975_: usize,
    mut v_b_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: usize = 0;
    let mut v___x_1980_: usize = 0;
    let mut v___x_1982_: u8 = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: u8 = 0;
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1982_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
                if v___x_1982_ == 0 {
                    v___x_1983_ = lean_byte_array_uget(v_as_1973_, v_i_1974_);
                    v___x_1990_ = 128;
                    v___x_1991_ = lean_uint8_dec_lt(v___x_1983_, v___x_1990_);
                    if v___x_1991_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1992_ = leanh::lean_box((v___x_1983_) as usize);
                        leanh::lean_inc_ref(v_r_1972_);
                        v___x_1993_ = leanh::lean_apply_1(v_r_1972_, v___x_1992_);
                        v___x_1994_ = (leanh::lean_unbox(v___x_1993_) as u8);
                        if v___x_1994_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_1995_ = lean_byte_array_push(v_b_1976_, v___x_1983_);
                            v___y_1978_ = v___x_1995_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_r_1972_);
                    return v_b_1976_;
                }
            }
            1 => {
                v___x_1979_ = 1usize;
                v___x_1980_ = lean_usize_add(v_i_1974_, v___x_1979_);
                v_i_1974_ = v___x_1980_;
                v_b_1976_ = v___y_1978_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1985_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0), core::ptr::addr_of_mut!(l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once), _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
                v___x_1986_ = lean_uint8_dec_eq(v___x_1983_, v___x_1985_);
                if v___x_1986_ == 0 {
                    v___x_1987_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_1983_, v_b_1976_);
                    v___y_1978_ = v___x_1987_;
                    state = 1;
                    continue;
                } else {
                    v___x_1988_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedQueryChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedQueryChar___closed__0_once),
                        _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
                    );
                    v___x_1989_ = lean_byte_array_push(v_b_1976_, v___x_1988_);
                    v___y_1978_ = v___x_1989_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(
    mut v_r_1996_: *mut leanh::LeanObject,
    mut v_as_1997_: *mut leanh::LeanObject,
    mut v_i_1998_: *mut leanh::LeanObject,
    mut v_stop_1999_: *mut leanh::LeanObject,
    mut v_b_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2001_: usize = 0;
    let mut v_stop_boxed_2002_: usize = 0;
    let mut v_res_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2001_ = leanh::lean_unbox_usize(v_i_1998_);
    leanh::lean_dec(v_i_1998_);
    v_stop_boxed_2002_ = leanh::lean_unbox_usize(v_stop_1999_);
    leanh::lean_dec(v_stop_1999_);
    v_res_2003_ =
        l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(
            v_r_1996_,
            v_as_1997_,
            v_i_boxed_2001_,
            v_stop_boxed_2002_,
            v_b_2000_,
        );
    leanh::lean_dec_ref(v_as_1997_);
    return v_res_2003_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_encode(
    mut v_s_2004_: *mut leanh::LeanObject,
    mut v_r_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    v___x_2006_ = l_ByteArray_empty;
    v___x_2007_ = lean_string_to_utf8(v_s_2004_);
    v___x_2008_ = leanh::lean_unsigned_to_nat(0);
    v___x_2009_ = lean_byte_array_size(v___x_2007_);
    v___x_2010_ = lean_nat_dec_lt(v___x_2008_, v___x_2009_);
    if v___x_2010_ == 0 {
        leanh::lean_dec_ref(v___x_2007_);
        leanh::lean_dec_ref(v_r_2005_);
        return v___x_2006_;
    } else {
        let mut v___x_2011_: u8 = 0;
        v___x_2011_ = lean_nat_dec_le(v___x_2009_, v___x_2009_);
        if v___x_2011_ == 0 {
            if v___x_2010_ == 0 {
                leanh::lean_dec_ref(v___x_2007_);
                leanh::lean_dec_ref(v_r_2005_);
                return v___x_2006_;
            } else {
                let mut v___x_2012_: usize = 0;
                let mut v___x_2013_: usize = 0;
                let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2012_ = 0usize;
                v___x_2013_ = lean_usize_of_nat(v___x_2009_);
                v___x_2014_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_2005_, v___x_2007_, v___x_2012_, v___x_2013_, v___x_2006_);
                leanh::lean_dec_ref(v___x_2007_);
                return v___x_2014_;
            }
        } else {
            let mut v___x_2015_: usize = 0;
            let mut v___x_2016_: usize = 0;
            let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2015_ = 0usize;
            v___x_2016_ = lean_usize_of_nat(v___x_2009_);
            v___x_2017_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_2005_, v___x_2007_, v___x_2015_, v___x_2016_, v___x_2006_);
            leanh::lean_dec_ref(v___x_2007_);
            return v___x_2017_;
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_encode___boxed(
    mut v_s_2018_: *mut leanh::LeanObject,
    mut v_r_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_2018_, v_r_2019_);
    leanh::lean_dec_ref(v_s_2018_);
    return v_res_2020_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_toString___redArg(
    mut v_es_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = lean_string_from_utf8_unchecked(v_es_2021_);
    return v___x_2022_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_toString(
    mut v_r_2023_: *mut leanh::LeanObject,
    mut v_es_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = lean_string_from_utf8_unchecked(v_es_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_toString___boxed(
    mut v_r_2026_: *mut leanh::LeanObject,
    mut v_es_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_2026_, v_es_2027_);
    leanh::lean_dec_ref(v_r_2026_);
    return v_res_2028_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(
    mut v_len_2029_: *mut leanh::LeanObject,
    mut v_rawBytes_2030_: *mut leanh::LeanObject,
    mut v_a_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plus_2041_: u8 = 0;
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v_percent_2052_: u8 = 0;
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2032_ = leanh::lean_ctor_get(v_a_2031_, 0);
                v_snd_2033_ = leanh::lean_ctor_get(v_a_2031_, 1);
                v_isSharedCheck_2099_ = (!leanh::lean_is_exclusive(v_a_2031_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2035_ = v_a_2031_;
                    v_isShared_2036_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2033_);
                    leanh::lean_inc(v_fst_2032_);
                    leanh::lean_dec(v_a_2031_);
                    v___x_2035_ = leanh::lean_box(0);
                    v_isShared_2036_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2037_ = lean_nat_dec_lt(v_snd_2033_, v_len_2029_);
                if v___x_2037_ == 0 {
                    if v_isShared_2036_ == 0 {
                        v___x_2039_ = v___x_2035_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2040_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_fst_2032_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_snd_2033_);
                        v___x_2039_ = v_reuseFailAlloc_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_plus_2041_ = 43;
                    v___x_2042_ = lean_byte_array_fget(v_rawBytes_2030_, v_snd_2033_);
                    v___x_2051_ = lean_uint8_dec_eq(v___x_2042_, v_plus_2041_);
                    if v___x_2051_ == 0 {
                        v_percent_2052_ = 37;
                        v___x_2053_ = lean_uint8_dec_eq(v___x_2042_, v_percent_2052_);
                        if v___x_2053_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___x_2054_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2055_ = lean_nat_add(v_snd_2033_, v___x_2054_);
                            v___x_2056_ = lean_nat_dec_lt(v___x_2055_, v_len_2029_);
                            if v___x_2056_ == 0 {
                                leanh::lean_dec(v___x_2055_);
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2035_);
                                v___x_2057_ = lean_byte_array_fget(v_rawBytes_2030_, v___x_2055_);
                                leanh::lean_dec(v___x_2055_);
                                v___x_2058_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_2057_);
                                if leanh::lean_obj_tag(v___x_2058_) == 1 {
                                    v_val_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                                    leanh::lean_inc(v_val_2059_);
                                    leanh::lean_dec_ref_known(v___x_2058_, 1);
                                    v___x_2060_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_2061_ = lean_nat_add(v_snd_2033_, v___x_2060_);
                                    v___x_2062_ = lean_nat_dec_lt(v___x_2061_, v_len_2029_);
                                    if v___x_2062_ == 0 {
                                        leanh::lean_dec(v_val_2059_);
                                        leanh::lean_dec(v_snd_2033_);
                                        v___x_2063_ =
                                            lean_byte_array_push(v_fst_2032_, v___x_2042_);
                                        v___x_2064_ =
                                            lean_byte_array_push(v___x_2063_, v___x_2057_);
                                        v___x_2065_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2065_, 0, v___x_2064_);
                                        leanh::lean_ctor_set(v___x_2065_, 1, v___x_2061_);
                                        v_a_2031_ = v___x_2065_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v___x_2067_ =
                                            lean_byte_array_fget(v_rawBytes_2030_, v___x_2061_);
                                        leanh::lean_dec(v___x_2061_);
                                        v___x_2068_ =
                                            l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_2067_);
                                        if leanh::lean_obj_tag(v___x_2068_) == 1 {
                                            v_val_2069_ =
                                                leanh::lean_ctor_get(v___x_2068_, 0);
                                            leanh::lean_inc(v_val_2069_);
                                            leanh::lean_dec_ref_known(v___x_2068_, 1);
                                            v___x_2070_ = 4;
                                            v___x_2071_ =
                                                (leanh::lean_unbox(v_val_2059_) as u8);
                                            leanh::lean_dec(v_val_2059_);
                                            v___x_2072_ =
                                                lean_uint8_shift_left(v___x_2071_, v___x_2070_);
                                            v___x_2073_ =
                                                (leanh::lean_unbox(v_val_2069_) as u8);
                                            leanh::lean_dec(v_val_2069_);
                                            v___x_2074_ = lean_uint8_add(v___x_2072_, v___x_2073_);
                                            v___x_2075_ =
                                                lean_byte_array_push(v_fst_2032_, v___x_2074_);
                                            v___x_2076_ = leanh::lean_unsigned_to_nat(3);
                                            v___x_2077_ = lean_nat_add(v_snd_2033_, v___x_2076_);
                                            leanh::lean_dec(v_snd_2033_);
                                            v___x_2078_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_2078_,
                                                0,
                                                v___x_2075_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_2078_,
                                                1,
                                                v___x_2077_,
                                            );
                                            v_a_2031_ = v___x_2078_;
                                            state = 0;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_2068_);
                                            leanh::lean_dec(v_val_2059_);
                                            v___x_2080_ =
                                                lean_byte_array_push(v_fst_2032_, v___x_2042_);
                                            v___x_2081_ =
                                                lean_byte_array_push(v___x_2080_, v___x_2057_);
                                            v___x_2082_ =
                                                lean_byte_array_push(v___x_2081_, v___x_2067_);
                                            v___x_2083_ = leanh::lean_unsigned_to_nat(3);
                                            v___x_2084_ = lean_nat_add(v_snd_2033_, v___x_2083_);
                                            leanh::lean_dec(v_snd_2033_);
                                            v___x_2085_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_2085_,
                                                0,
                                                v___x_2082_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_2085_,
                                                1,
                                                v___x_2084_,
                                            );
                                            v_a_2031_ = v___x_2085_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2058_);
                                    v___x_2087_ = lean_byte_array_push(v_fst_2032_, v___x_2042_);
                                    v___x_2088_ = lean_byte_array_push(v___x_2087_, v___x_2057_);
                                    v___x_2089_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_2090_ = lean_nat_add(v_snd_2033_, v___x_2089_);
                                    leanh::lean_dec(v_snd_2033_);
                                    v___x_2091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2091_, 0, v___x_2088_);
                                    leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
                                    v_a_2031_ = v___x_2091_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_2035_);
                        v___x_2093_ = 32;
                        v___x_2094_ = lean_byte_array_push(v_fst_2032_, v___x_2093_);
                        v___x_2095_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2096_ = lean_nat_add(v_snd_2033_, v___x_2095_);
                        leanh::lean_dec(v_snd_2033_);
                        v___x_2097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2097_, 0, v___x_2094_);
                        leanh::lean_ctor_set(v___x_2097_, 1, v___x_2096_);
                        v_a_2031_ = v___x_2097_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2039_;
            }
            3 => {
                v___x_2044_ = lean_byte_array_push(v_fst_2032_, v___x_2042_);
                v___x_2045_ = leanh::lean_unsigned_to_nat(1);
                v___x_2046_ = lean_nat_add(v_snd_2033_, v___x_2045_);
                leanh::lean_dec(v_snd_2033_);
                if v_isShared_2036_ == 0 {
                    leanh::lean_ctor_set(v___x_2035_, 1, v___x_2046_);
                    leanh::lean_ctor_set(v___x_2035_, 0, v___x_2044_);
                    v___x_2048_ = v___x_2035_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2046_);
                    v___x_2048_ = v_reuseFailAlloc_2050_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_2031_ = v___x_2048_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(
    mut v_len_2100_: *mut leanh::LeanObject,
    mut v_rawBytes_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2103_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_2100_, v_rawBytes_2101_, v_a_2102_);
    leanh::lean_dec_ref(v_rawBytes_2101_);
    leanh::lean_dec(v_len_2100_);
    return v_res_2103_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_decode___redArg(
    mut v_es_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_len_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    v_len_2105_ = lean_byte_array_size(v_es_2104_);
    v___x_2106_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_decode___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once),
        _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0,
    );
    v___x_2107_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_2105_, v_es_2104_, v___x_2106_);
    v_fst_2108_ = leanh::lean_ctor_get(v___x_2107_, 0);
    leanh::lean_inc(v_fst_2108_);
    leanh::lean_dec_ref(v___x_2107_);
    v___x_2109_ = lean_string_validate_utf8(v_fst_2108_);
    if v___x_2109_ == 0 {
        let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_2108_);
        v___x_2110_ = leanh::lean_box(0);
        return v___x_2110_;
    } else {
        let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2111_ = lean_string_from_utf8_unchecked(v_fst_2108_);
        v___x_2112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2112_, 0, v___x_2111_);
        return v___x_2112_;
    }
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(
    mut v_es_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_2113_);
    leanh::lean_dec_ref(v_es_2113_);
    return v_res_2114_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_decode(
    mut v_r_2115_: *mut leanh::LeanObject,
    mut v_es_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_2116_);
    return v___x_2117_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryString_decode___boxed(
    mut v_r_2118_: *mut leanh::LeanObject,
    mut v_es_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2120_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_2118_, v_es_2119_);
    leanh::lean_dec_ref(v_es_2119_);
    leanh::lean_dec_ref(v_r_2118_);
    return v_res_2120_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(
    mut v_len_2121_: *mut leanh::LeanObject,
    mut v_rawBytes_2122_: *mut leanh::LeanObject,
    mut v_inst_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_2121_, v_rawBytes_2122_, v_a_2124_);
    return v___x_2125_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(
    mut v_len_2126_: *mut leanh::LeanObject,
    mut v_rawBytes_2127_: *mut leanh::LeanObject,
    mut v_inst_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2130_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_2126_, v_rawBytes_2127_, v_inst_2128_, v_a_2129_);
    leanh::lean_dec_ref(v_rawBytes_2127_);
    leanh::lean_dec(v_len_2126_);
    return v_res_2130_;
}
pub unsafe fn l_Std_Http_URI_instToStringEncodedQueryString(
    mut v_r_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = leanh::lean_alloc_closure(
        l_Std_Http_URI_EncodedQueryString_toString___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_2132_, 0, v_r_2131_);
    return v___x_2132_;
}
pub unsafe fn l_Std_Http_URI_instReprEncodedQueryString(
    mut v_r_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2134_ = l_Std_Http_URI_EncodedString_instRepr___closed__0;
    return v___f_2134_;
}
pub unsafe fn l_Std_Http_URI_instReprEncodedQueryString___boxed(
    mut v_r_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2136_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_2135_);
    leanh::lean_dec_ref(v_r_2135_);
    return v_res_2136_;
}
pub unsafe fn l_Std_Http_URI_instBEqEncodedQueryString(
    mut v_r_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2138_ = l_Std_Http_URI_EncodedString_instBEq___closed__0;
    return v___f_2138_;
}
pub unsafe fn l_Std_Http_URI_instBEqEncodedQueryString___boxed(
    mut v_r_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_2139_);
    leanh::lean_dec_ref(v_r_2139_);
    return v_res_2140_;
}
pub unsafe fn l_Std_Http_URI_instHashableEncodedQueryString(
    mut v_r_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2142_ = l_Std_Http_URI_EncodedString_instHashable___closed__0;
    return v___f_2142_;
}
pub unsafe fn l_Std_Http_URI_instHashableEncodedQueryString___boxed(
    mut v_r_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_2143_);
    leanh::lean_dec_ref(v_r_2143_);
    return v_res_2144_;
}
pub unsafe fn _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1() -> u64
{
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u64 = 0;
    v___x_2151_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0;
    v___x_2152_ = lean_byte_array_hash(v___x_2151_);
    return v___x_2152_;
}
pub unsafe fn _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2;
    v___x_2160_ = lean_byte_array_size(v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(
    mut v_x_2161_: *mut leanh::LeanObject,
) -> u64 {
    if leanh::lean_obj_tag(v_x_2161_) == 0 {
        let mut v___x_2162_: u64 = 0;
        v___x_2162_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(
                l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once
            ),
            _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1,
        );
        return v___x_2162_;
    } else {
        let mut v_val_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: u8 = 0;
        let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2170_: u64 = 0;
        v_val_2163_ = leanh::lean_ctor_get(v_x_2161_, 0);
        v___x_2164_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2;
        v___x_2165_ = leanh::lean_unsigned_to_nat(0);
        v___x_2166_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once
            ),
            _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3,
        );
        v___x_2167_ = lean_byte_array_size(v_val_2163_);
        v___x_2168_ = 0;
        v___x_2169_ = lean_byte_array_copy_slice(
            v_val_2163_,
            v___x_2165_,
            v___x_2164_,
            v___x_2166_,
            v___x_2167_,
            v___x_2168_,
        );
        v___x_2170_ = lean_byte_array_hash(v___x_2169_);
        leanh::lean_dec_ref(v___x_2169_);
        return v___x_2170_;
    }
}
pub unsafe fn l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(
    mut v_x_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2172_: u64 = 0;
    let mut v_r_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_2171_);
    leanh::lean_dec(v_x_2171_);
    v_r_2173_ = leanh::lean_box_uint64(v_res_2172_);
    return v_r_2173_;
}
pub unsafe fn l_Std_Http_URI_instHashableOptionEncodedQueryString(
    mut v_r_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2176_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0;
    return v___f_2176_;
}
pub unsafe fn l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(
    mut v_r_2177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2178_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_2177_);
    leanh::lean_dec_ref(v_r_2177_);
    return v_res_2178_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0() -> u8 {
    let mut v___x_2179_: u32 = 0;
    let mut v___x_2180_: u8 = 0;
    v___x_2179_ = 58;
    v___x_2180_ = lean_uint32_to_uint8(v___x_2179_);
    return v___x_2180_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1() -> u8 {
    let mut v___x_2181_: u32 = 0;
    let mut v___x_2182_: u8 = 0;
    v___x_2181_ = 64;
    v___x_2182_ = lean_uint32_to_uint8(v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2() -> u8 {
    let mut v___x_2183_: u32 = 0;
    let mut v___x_2184_: u8 = 0;
    v___x_2183_ = 38;
    v___x_2184_ = lean_uint32_to_uint8(v___x_2183_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3() -> u8 {
    let mut v___x_2185_: u32 = 0;
    let mut v___x_2186_: u8 = 0;
    v___x_2185_ = 39;
    v___x_2186_ = lean_uint32_to_uint8(v___x_2185_);
    return v___x_2186_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4() -> u8 {
    let mut v___x_2187_: u32 = 0;
    let mut v___x_2188_: u8 = 0;
    v___x_2187_ = 40;
    v___x_2188_ = lean_uint32_to_uint8(v___x_2187_);
    return v___x_2188_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5() -> u8 {
    let mut v___x_2189_: u32 = 0;
    let mut v___x_2190_: u8 = 0;
    v___x_2189_ = 41;
    v___x_2190_ = lean_uint32_to_uint8(v___x_2189_);
    return v___x_2190_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6() -> u8 {
    let mut v___x_2191_: u32 = 0;
    let mut v___x_2192_: u8 = 0;
    v___x_2191_ = 42;
    v___x_2192_ = lean_uint32_to_uint8(v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7() -> u8 {
    let mut v___x_2193_: u32 = 0;
    let mut v___x_2194_: u8 = 0;
    v___x_2193_ = 44;
    v___x_2194_ = lean_uint32_to_uint8(v___x_2193_);
    return v___x_2194_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8() -> u8 {
    let mut v___x_2195_: u32 = 0;
    let mut v___x_2196_: u8 = 0;
    v___x_2195_ = 59;
    v___x_2196_ = lean_uint32_to_uint8(v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9() -> u8 {
    let mut v___x_2197_: u32 = 0;
    let mut v___x_2198_: u8 = 0;
    v___x_2197_ = 61;
    v___x_2198_ = lean_uint32_to_uint8(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10() -> u8 {
    let mut v___x_2199_: u32 = 0;
    let mut v___x_2200_: u8 = 0;
    v___x_2199_ = 33;
    v___x_2200_ = lean_uint32_to_uint8(v___x_2199_);
    return v___x_2200_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11() -> u8 {
    let mut v___x_2201_: u32 = 0;
    let mut v___x_2202_: u8 = 0;
    v___x_2201_ = 36;
    v___x_2202_ = lean_uint32_to_uint8(v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12() -> u8 {
    let mut v___x_2203_: u32 = 0;
    let mut v___x_2204_: u8 = 0;
    v___x_2203_ = 95;
    v___x_2204_ = lean_uint32_to_uint8(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13() -> u8 {
    let mut v___x_2205_: u32 = 0;
    let mut v___x_2206_: u8 = 0;
    v___x_2205_ = 126;
    v___x_2206_ = lean_uint32_to_uint8(v___x_2205_);
    return v___x_2206_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14() -> u8 {
    let mut v___x_2207_: u32 = 0;
    let mut v___x_2208_: u8 = 0;
    v___x_2207_ = 45;
    v___x_2208_ = lean_uint32_to_uint8(v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15() -> u8 {
    let mut v___x_2209_: u32 = 0;
    let mut v___x_2210_: u8 = 0;
    v___x_2209_ = 46;
    v___x_2210_ = lean_uint32_to_uint8(v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16() -> u8 {
    let mut v___x_2211_: u32 = 0;
    let mut v___x_2212_: u8 = 0;
    v___x_2211_ = 90;
    v___x_2212_ = lean_uint32_to_uint8(v___x_2211_);
    return v___x_2212_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17() -> u8 {
    let mut v___x_2213_: u32 = 0;
    let mut v___x_2214_: u8 = 0;
    v___x_2213_ = 122;
    v___x_2214_ = lean_uint32_to_uint8(v___x_2213_);
    return v___x_2214_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_encode___lam__0(mut v___y_2215_: u8) -> u8 {
    let mut v___y_2217_: u8 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: u8 = 0;
    let mut v___y_2223_: u8 = 0;
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut v___y_2243_: u8 = 0;
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: u8 = 0;
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___y_2249_: u8 = 0;
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: u8 = 0;
    let mut v___y_2255_: u8 = 0;
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: u8 = 0;
    let mut v___y_2261_: u8 = 0;
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: u8 = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v___y_2267_: u8 = 0;
    let mut v___x_2268_: u8 = 0;
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: u8 = 0;
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2272_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_2273_ = lean_uint8_dec_le(v___x_2272_, v___y_2215_);
                if v___x_2273_ == 0 {
                    v___y_2267_ = v___x_2273_;
                    state = 7;
                    continue;
                } else {
                    v___x_2274_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_2275_ = lean_uint8_dec_le(v___y_2215_, v___x_2274_);
                    v___y_2267_ = v___x_2275_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_2217_ == 0 {
                    v___x_2218_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0,
                    );
                    v___x_2219_ = lean_uint8_dec_eq(v___y_2215_, v___x_2218_);
                    if v___x_2219_ == 0 {
                        v___x_2220_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1,
                        );
                        v___x_2221_ = lean_uint8_dec_eq(v___y_2215_, v___x_2220_);
                        return v___x_2221_;
                    } else {
                        return v___x_2219_;
                    }
                } else {
                    return v___y_2217_;
                }
            }
            2 => {
                if v___y_2223_ == 0 {
                    v___x_2224_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2,
                    );
                    v___x_2225_ = lean_uint8_dec_eq(v___y_2215_, v___x_2224_);
                    if v___x_2225_ == 0 {
                        v___x_2226_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3,
                        );
                        v___x_2227_ = lean_uint8_dec_eq(v___y_2215_, v___x_2226_);
                        if v___x_2227_ == 0 {
                            v___x_2228_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once
                                ),
                                _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4,
                            );
                            v___x_2229_ = lean_uint8_dec_eq(v___y_2215_, v___x_2228_);
                            if v___x_2229_ == 0 {
                                v___x_2230_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
                                v___x_2231_ = lean_uint8_dec_eq(v___y_2215_, v___x_2230_);
                                if v___x_2231_ == 0 {
                                    v___x_2232_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
                                    v___x_2233_ = lean_uint8_dec_eq(v___y_2215_, v___x_2232_);
                                    if v___x_2233_ == 0 {
                                        v___x_2234_ = leanh::lean_uint8_once(
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0_once
                                            ),
                                            _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
                                        );
                                        v___x_2235_ = lean_uint8_dec_eq(v___y_2215_, v___x_2234_);
                                        if v___x_2235_ == 0 {
                                            v___x_2236_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
                                            v___x_2237_ =
                                                lean_uint8_dec_eq(v___y_2215_, v___x_2236_);
                                            if v___x_2237_ == 0 {
                                                v___x_2238_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
                                                v___x_2239_ =
                                                    lean_uint8_dec_eq(v___y_2215_, v___x_2238_);
                                                if v___x_2239_ == 0 {
                                                    v___x_2240_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
                                                    v___x_2241_ =
                                                        lean_uint8_dec_eq(v___y_2215_, v___x_2240_);
                                                    v___y_2217_ = v___x_2241_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_2217_ = v___x_2239_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_2217_ = v___x_2237_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_2217_ = v___x_2235_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_2217_ = v___x_2233_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_2217_ = v___x_2231_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_2217_ = v___x_2229_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_2217_ = v___x_2227_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2217_ = v___x_2225_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_2223_;
                }
            }
            3 => {
                if v___y_2243_ == 0 {
                    v___x_2244_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10,
                    );
                    v___x_2245_ = lean_uint8_dec_eq(v___y_2215_, v___x_2244_);
                    if v___x_2245_ == 0 {
                        v___x_2246_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11,
                        );
                        v___x_2247_ = lean_uint8_dec_eq(v___y_2215_, v___x_2246_);
                        v___y_2223_ = v___x_2247_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2223_ = v___x_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_2243_;
                }
            }
            4 => {
                if v___y_2249_ == 0 {
                    v___x_2250_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12,
                    );
                    v___x_2251_ = lean_uint8_dec_eq(v___y_2215_, v___x_2250_);
                    if v___x_2251_ == 0 {
                        v___x_2252_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13,
                        );
                        v___x_2253_ = lean_uint8_dec_eq(v___y_2215_, v___x_2252_);
                        v___y_2243_ = v___x_2253_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2243_ = v___x_2251_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_2249_;
                }
            }
            5 => {
                if v___y_2255_ == 0 {
                    v___x_2256_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14,
                    );
                    v___x_2257_ = lean_uint8_dec_eq(v___y_2215_, v___x_2256_);
                    if v___x_2257_ == 0 {
                        v___x_2258_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15,
                        );
                        v___x_2259_ = lean_uint8_dec_eq(v___y_2215_, v___x_2258_);
                        v___y_2249_ = v___x_2259_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2249_ = v___x_2257_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_2255_;
                }
            }
            6 => {
                if v___y_2261_ == 0 {
                    v___x_2262_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_2263_ = lean_uint8_dec_le(v___x_2262_, v___y_2215_);
                    if v___x_2263_ == 0 {
                        v___y_2255_ = v___x_2263_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2264_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16,
                        );
                        v___x_2265_ = lean_uint8_dec_le(v___y_2215_, v___x_2264_);
                        v___y_2255_ = v___x_2265_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_2261_;
                }
            }
            7 => {
                if v___y_2267_ == 0 {
                    v___x_2268_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_2269_ = lean_uint8_dec_le(v___x_2268_, v___y_2215_);
                    if v___x_2269_ == 0 {
                        v___y_2261_ = v___x_2269_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2270_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17,
                        );
                        v___x_2271_ = lean_uint8_dec_le(v___y_2215_, v___x_2270_);
                        v___y_2261_ = v___x_2271_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_2267_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(
    mut v___y_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_318__boxed_2277_: u8 = 0;
    let mut v_res_2278_: u8 = 0;
    let mut v_r_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_318__boxed_2277_ = (leanh::lean_unbox(v___y_2276_) as u8);
    v_res_2278_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_318__boxed_2277_);
    v_r_2279_ = leanh::lean_box((v_res_2278_) as usize);
    return v_r_2279_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_encode(
    mut v_s_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2282_ = l_Std_Http_URI_EncodedSegment_encode___closed__0;
    v___x_2283_ = l_Std_Http_URI_EncodedString_encode(v___f_2282_, v_s_2281_);
    return v___x_2283_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_encode___boxed(
    mut v_s_2284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Std_Http_URI_EncodedSegment_encode(v_s_2284_);
    leanh::lean_dec_ref(v_s_2284_);
    return v_res_2285_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(
    mut v_ba_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2287_ = l_Std_Http_URI_EncodedSegment_encode___closed__0;
    v___x_2288_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_2287_, v_ba_2286_);
    return v___x_2288_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_ofByteArray_x21(
    mut v_ba_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2290_ = l_Std_Http_URI_EncodedSegment_encode___closed__0;
    v___x_2291_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_2290_, v_ba_2289_);
    return v___x_2291_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_decode(
    mut v_segment_2292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_2292_);
    return v___x_2293_;
}
pub unsafe fn l_Std_Http_URI_EncodedSegment_decode___boxed(
    mut v_segment_2294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_2294_);
    leanh::lean_dec_ref(v_segment_2294_);
    return v_res_2295_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0() -> u8 {
    let mut v___x_2296_: u32 = 0;
    let mut v___x_2297_: u8 = 0;
    v___x_2296_ = 47;
    v___x_2297_ = lean_uint32_to_uint8(v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1() -> u8 {
    let mut v___x_2298_: u32 = 0;
    let mut v___x_2299_: u8 = 0;
    v___x_2298_ = 63;
    v___x_2299_ = lean_uint32_to_uint8(v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_encode___lam__0(mut v___y_2300_: u8) -> u8 {
    let mut v___y_2302_: u8 = 0;
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: u8 = 0;
    let mut v___y_2308_: u8 = 0;
    let mut v___x_2309_: u8 = 0;
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2312_: u8 = 0;
    let mut v___y_2314_: u8 = 0;
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: u8 = 0;
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
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: u8 = 0;
    let mut v___y_2334_: u8 = 0;
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: u8 = 0;
    let mut v___x_2338_: u8 = 0;
    let mut v___y_2340_: u8 = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: u8 = 0;
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: u8 = 0;
    let mut v___y_2346_: u8 = 0;
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: u8 = 0;
    let mut v___y_2352_: u8 = 0;
    let mut v___x_2353_: u8 = 0;
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v___y_2358_: u8 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2363_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_2364_ = lean_uint8_dec_le(v___x_2363_, v___y_2300_);
                if v___x_2364_ == 0 {
                    v___y_2358_ = v___x_2364_;
                    state = 8;
                    continue;
                } else {
                    v___x_2365_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_2366_ = lean_uint8_dec_le(v___y_2300_, v___x_2365_);
                    v___y_2358_ = v___x_2366_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                if v___y_2302_ == 0 {
                    v___x_2303_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0,
                    );
                    v___x_2304_ = lean_uint8_dec_eq(v___y_2300_, v___x_2303_);
                    if v___x_2304_ == 0 {
                        v___x_2305_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once
                            ),
                            _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1,
                        );
                        v___x_2306_ = lean_uint8_dec_eq(v___y_2300_, v___x_2305_);
                        return v___x_2306_;
                    } else {
                        return v___x_2304_;
                    }
                } else {
                    return v___y_2302_;
                }
            }
            2 => {
                if v___y_2308_ == 0 {
                    v___x_2309_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0,
                    );
                    v___x_2310_ = lean_uint8_dec_eq(v___y_2300_, v___x_2309_);
                    if v___x_2310_ == 0 {
                        v___x_2311_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1,
                        );
                        v___x_2312_ = lean_uint8_dec_eq(v___y_2300_, v___x_2311_);
                        v___y_2302_ = v___x_2312_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2302_ = v___x_2310_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_2308_;
                }
            }
            3 => {
                if v___y_2314_ == 0 {
                    v___x_2315_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2,
                    );
                    v___x_2316_ = lean_uint8_dec_eq(v___y_2300_, v___x_2315_);
                    if v___x_2316_ == 0 {
                        v___x_2317_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3,
                        );
                        v___x_2318_ = lean_uint8_dec_eq(v___y_2300_, v___x_2317_);
                        if v___x_2318_ == 0 {
                            v___x_2319_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once
                                ),
                                _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4,
                            );
                            v___x_2320_ = lean_uint8_dec_eq(v___y_2300_, v___x_2319_);
                            if v___x_2320_ == 0 {
                                v___x_2321_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
                                v___x_2322_ = lean_uint8_dec_eq(v___y_2300_, v___x_2321_);
                                if v___x_2322_ == 0 {
                                    v___x_2323_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
                                    v___x_2324_ = lean_uint8_dec_eq(v___y_2300_, v___x_2323_);
                                    if v___x_2324_ == 0 {
                                        v___x_2325_ = leanh::lean_uint8_once(
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0_once
                                            ),
                                            _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
                                        );
                                        v___x_2326_ = lean_uint8_dec_eq(v___y_2300_, v___x_2325_);
                                        if v___x_2326_ == 0 {
                                            v___x_2327_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
                                            v___x_2328_ =
                                                lean_uint8_dec_eq(v___y_2300_, v___x_2327_);
                                            if v___x_2328_ == 0 {
                                                v___x_2329_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
                                                v___x_2330_ =
                                                    lean_uint8_dec_eq(v___y_2300_, v___x_2329_);
                                                if v___x_2330_ == 0 {
                                                    v___x_2331_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
                                                    v___x_2332_ =
                                                        lean_uint8_dec_eq(v___y_2300_, v___x_2331_);
                                                    v___y_2308_ = v___x_2332_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___y_2308_ = v___x_2330_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                v___y_2308_ = v___x_2328_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            v___y_2308_ = v___x_2326_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v___y_2308_ = v___x_2324_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_2308_ = v___x_2322_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_2308_ = v___x_2320_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_2308_ = v___x_2318_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2308_ = v___x_2316_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_2314_;
                }
            }
            4 => {
                if v___y_2334_ == 0 {
                    v___x_2335_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10,
                    );
                    v___x_2336_ = lean_uint8_dec_eq(v___y_2300_, v___x_2335_);
                    if v___x_2336_ == 0 {
                        v___x_2337_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11,
                        );
                        v___x_2338_ = lean_uint8_dec_eq(v___y_2300_, v___x_2337_);
                        v___y_2314_ = v___x_2338_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2314_ = v___x_2336_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_2334_;
                }
            }
            5 => {
                if v___y_2340_ == 0 {
                    v___x_2341_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12,
                    );
                    v___x_2342_ = lean_uint8_dec_eq(v___y_2300_, v___x_2341_);
                    if v___x_2342_ == 0 {
                        v___x_2343_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13,
                        );
                        v___x_2344_ = lean_uint8_dec_eq(v___y_2300_, v___x_2343_);
                        v___y_2334_ = v___x_2344_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2334_ = v___x_2342_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_2340_;
                }
            }
            6 => {
                if v___y_2346_ == 0 {
                    v___x_2347_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14,
                    );
                    v___x_2348_ = lean_uint8_dec_eq(v___y_2300_, v___x_2347_);
                    if v___x_2348_ == 0 {
                        v___x_2349_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15,
                        );
                        v___x_2350_ = lean_uint8_dec_eq(v___y_2300_, v___x_2349_);
                        v___y_2340_ = v___x_2350_;
                        state = 5;
                        continue;
                    } else {
                        v___y_2340_ = v___x_2348_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_2346_;
                }
            }
            7 => {
                if v___y_2352_ == 0 {
                    v___x_2353_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_2354_ = lean_uint8_dec_le(v___x_2353_, v___y_2300_);
                    if v___x_2354_ == 0 {
                        v___y_2346_ = v___x_2354_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2355_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16,
                        );
                        v___x_2356_ = lean_uint8_dec_le(v___y_2300_, v___x_2355_);
                        v___y_2346_ = v___x_2356_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_2352_;
                }
            }
            8 => {
                if v___y_2358_ == 0 {
                    v___x_2359_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_2360_ = lean_uint8_dec_le(v___x_2359_, v___y_2300_);
                    if v___x_2360_ == 0 {
                        v___y_2352_ = v___x_2360_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2361_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17,
                        );
                        v___x_2362_ = lean_uint8_dec_le(v___y_2300_, v___x_2361_);
                        v___y_2352_ = v___x_2362_;
                        state = 7;
                        continue;
                    }
                } else {
                    return v___y_2358_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(
    mut v___y_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_312__boxed_2368_: u8 = 0;
    let mut v_res_2369_: u8 = 0;
    let mut v_r_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_312__boxed_2368_ = (leanh::lean_unbox(v___y_2367_) as u8);
    v_res_2369_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_312__boxed_2368_);
    v_r_2370_ = leanh::lean_box((v_res_2369_) as usize);
    return v_r_2370_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_encode(
    mut v_s_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2373_ = l_Std_Http_URI_EncodedFragment_encode___closed__0;
    v___x_2374_ = l_Std_Http_URI_EncodedString_encode(v___f_2373_, v_s_2372_);
    return v___x_2374_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_encode___boxed(
    mut v_s_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Std_Http_URI_EncodedFragment_encode(v_s_2375_);
    leanh::lean_dec_ref(v_s_2375_);
    return v_res_2376_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(
    mut v_ba_2377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2378_ = l_Std_Http_URI_EncodedFragment_encode___closed__0;
    v___x_2379_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_2378_, v_ba_2377_);
    return v___x_2379_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_ofByteArray_x21(
    mut v_ba_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2381_ = l_Std_Http_URI_EncodedFragment_encode___closed__0;
    v___x_2382_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_2381_, v_ba_2380_);
    return v___x_2382_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_decode(
    mut v_fragment_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_2383_);
    return v___x_2384_;
}
pub unsafe fn l_Std_Http_URI_EncodedFragment_decode___boxed(
    mut v_fragment_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_2385_);
    leanh::lean_dec_ref(v_fragment_2385_);
    return v_res_2386_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_encode___lam__0(mut v___y_2387_: u8) -> u8 {
    let mut v___y_2389_: u8 = 0;
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: u8 = 0;
    let mut v___y_2393_: u8 = 0;
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: u8 = 0;
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: u8 = 0;
    let mut v___x_2405_: u8 = 0;
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: u8 = 0;
    let mut v___y_2413_: u8 = 0;
    let mut v___x_2414_: u8 = 0;
    let mut v___x_2415_: u8 = 0;
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___y_2419_: u8 = 0;
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: u8 = 0;
    let mut v___y_2425_: u8 = 0;
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: u8 = 0;
    let mut v___y_2431_: u8 = 0;
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2434_: u8 = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___y_2437_: u8 = 0;
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2442_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_2443_ = lean_uint8_dec_le(v___x_2442_, v___y_2387_);
                if v___x_2443_ == 0 {
                    v___y_2437_ = v___x_2443_;
                    state = 7;
                    continue;
                } else {
                    v___x_2444_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_2445_ = lean_uint8_dec_le(v___y_2387_, v___x_2444_);
                    v___y_2437_ = v___x_2445_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_2389_ == 0 {
                    v___x_2390_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0,
                    );
                    v___x_2391_ = lean_uint8_dec_eq(v___y_2387_, v___x_2390_);
                    return v___x_2391_;
                } else {
                    return v___y_2389_;
                }
            }
            2 => {
                if v___y_2393_ == 0 {
                    v___x_2394_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2,
                    );
                    v___x_2395_ = lean_uint8_dec_eq(v___y_2387_, v___x_2394_);
                    if v___x_2395_ == 0 {
                        v___x_2396_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3,
                        );
                        v___x_2397_ = lean_uint8_dec_eq(v___y_2387_, v___x_2396_);
                        if v___x_2397_ == 0 {
                            v___x_2398_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once
                                ),
                                _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4,
                            );
                            v___x_2399_ = lean_uint8_dec_eq(v___y_2387_, v___x_2398_);
                            if v___x_2399_ == 0 {
                                v___x_2400_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
                                v___x_2401_ = lean_uint8_dec_eq(v___y_2387_, v___x_2400_);
                                if v___x_2401_ == 0 {
                                    v___x_2402_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
                                    v___x_2403_ = lean_uint8_dec_eq(v___y_2387_, v___x_2402_);
                                    if v___x_2403_ == 0 {
                                        v___x_2404_ = leanh::lean_uint8_once(
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0_once
                                            ),
                                            _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
                                        );
                                        v___x_2405_ = lean_uint8_dec_eq(v___y_2387_, v___x_2404_);
                                        if v___x_2405_ == 0 {
                                            v___x_2406_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
                                            v___x_2407_ =
                                                lean_uint8_dec_eq(v___y_2387_, v___x_2406_);
                                            if v___x_2407_ == 0 {
                                                v___x_2408_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
                                                v___x_2409_ =
                                                    lean_uint8_dec_eq(v___y_2387_, v___x_2408_);
                                                if v___x_2409_ == 0 {
                                                    v___x_2410_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
                                                    v___x_2411_ =
                                                        lean_uint8_dec_eq(v___y_2387_, v___x_2410_);
                                                    v___y_2389_ = v___x_2411_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_2389_ = v___x_2409_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_2389_ = v___x_2407_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_2389_ = v___x_2405_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_2389_ = v___x_2403_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_2389_ = v___x_2401_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_2389_ = v___x_2399_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_2389_ = v___x_2397_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2389_ = v___x_2395_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_2393_;
                }
            }
            3 => {
                if v___y_2413_ == 0 {
                    v___x_2414_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10,
                    );
                    v___x_2415_ = lean_uint8_dec_eq(v___y_2387_, v___x_2414_);
                    if v___x_2415_ == 0 {
                        v___x_2416_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11,
                        );
                        v___x_2417_ = lean_uint8_dec_eq(v___y_2387_, v___x_2416_);
                        v___y_2393_ = v___x_2417_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2393_ = v___x_2415_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_2413_;
                }
            }
            4 => {
                if v___y_2419_ == 0 {
                    v___x_2420_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12,
                    );
                    v___x_2421_ = lean_uint8_dec_eq(v___y_2387_, v___x_2420_);
                    if v___x_2421_ == 0 {
                        v___x_2422_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13,
                        );
                        v___x_2423_ = lean_uint8_dec_eq(v___y_2387_, v___x_2422_);
                        v___y_2413_ = v___x_2423_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2413_ = v___x_2421_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_2419_;
                }
            }
            5 => {
                if v___y_2425_ == 0 {
                    v___x_2426_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14,
                    );
                    v___x_2427_ = lean_uint8_dec_eq(v___y_2387_, v___x_2426_);
                    if v___x_2427_ == 0 {
                        v___x_2428_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15,
                        );
                        v___x_2429_ = lean_uint8_dec_eq(v___y_2387_, v___x_2428_);
                        v___y_2419_ = v___x_2429_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2419_ = v___x_2427_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_2425_;
                }
            }
            6 => {
                if v___y_2431_ == 0 {
                    v___x_2432_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_2433_ = lean_uint8_dec_le(v___x_2432_, v___y_2387_);
                    if v___x_2433_ == 0 {
                        v___y_2425_ = v___x_2433_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2434_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16,
                        );
                        v___x_2435_ = lean_uint8_dec_le(v___y_2387_, v___x_2434_);
                        v___y_2425_ = v___x_2435_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_2431_;
                }
            }
            7 => {
                if v___y_2437_ == 0 {
                    v___x_2438_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_2439_ = lean_uint8_dec_le(v___x_2438_, v___y_2387_);
                    if v___x_2439_ == 0 {
                        v___y_2431_ = v___x_2439_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2440_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17,
                        );
                        v___x_2441_ = lean_uint8_dec_le(v___y_2387_, v___x_2440_);
                        v___y_2431_ = v___x_2441_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_2437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(
    mut v___y_2446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_271__boxed_2447_: u8 = 0;
    let mut v_res_2448_: u8 = 0;
    let mut v_r_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_271__boxed_2447_ = (leanh::lean_unbox(v___y_2446_) as u8);
    v_res_2448_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_271__boxed_2447_);
    v_r_2449_ = leanh::lean_box((v_res_2448_) as usize);
    return v_r_2449_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_encode(
    mut v_s_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2452_ = l_Std_Http_URI_EncodedUserInfo_encode___closed__0;
    v___x_2453_ = l_Std_Http_URI_EncodedString_encode(v___f_2452_, v_s_2451_);
    return v___x_2453_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_encode___boxed(
    mut v_s_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_2454_);
    leanh::lean_dec_ref(v_s_2454_);
    return v_res_2455_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(
    mut v_ba_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2457_ = l_Std_Http_URI_EncodedUserInfo_encode___closed__0;
    v___x_2458_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_2457_, v_ba_2456_);
    return v___x_2458_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(
    mut v_ba_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2460_ = l_Std_Http_URI_EncodedUserInfo_encode___closed__0;
    v___x_2461_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_2460_, v_ba_2459_);
    return v___x_2461_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_decode(
    mut v_userInfo_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_2462_);
    return v___x_2463_;
}
pub unsafe fn l_Std_Http_URI_EncodedUserInfo_decode___boxed(
    mut v_userInfo_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_2464_);
    leanh::lean_dec_ref(v_userInfo_2464_);
    return v_res_2465_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_encode___lam__0(mut v___y_2466_: u8) -> u8 {
    let mut v___x_2468_: u8 = 0;
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: u8 = 0;
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2473_: u8 = 0;
    let mut v___y_2475_: u8 = 0;
    let mut v___y_2477_: u8 = 0;
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: u8 = 0;
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2481_: u8 = 0;
    let mut v___y_2483_: u8 = 0;
    let mut v___x_2484_: u8 = 0;
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: u8 = 0;
    let mut v___x_2487_: u8 = 0;
    let mut v___y_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: u8 = 0;
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: u8 = 0;
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: u8 = 0;
    let mut v___y_2509_: u8 = 0;
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: u8 = 0;
    let mut v___x_2512_: u8 = 0;
    let mut v___x_2513_: u8 = 0;
    let mut v___y_2515_: u8 = 0;
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: u8 = 0;
    let mut v___y_2521_: u8 = 0;
    let mut v___x_2522_: u8 = 0;
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: u8 = 0;
    let mut v___y_2527_: u8 = 0;
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: u8 = 0;
    let mut v___y_2533_: u8 = 0;
    let mut v___x_2534_: u8 = 0;
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2538_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__5_once),
                    _init_l_Std_Http_URI_isEncodedChar___closed__5,
                );
                v___x_2539_ = lean_uint8_dec_le(v___x_2538_, v___y_2466_);
                if v___x_2539_ == 0 {
                    v___y_2533_ = v___x_2539_;
                    state = 10;
                    continue;
                } else {
                    v___x_2540_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__6_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__6,
                    );
                    v___x_2541_ = lean_uint8_dec_le(v___y_2466_, v___x_2540_);
                    v___y_2533_ = v___x_2541_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2468_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once
                    ),
                    _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2,
                );
                v___x_2469_ = lean_uint8_dec_eq(v___y_2466_, v___x_2468_);
                if v___x_2469_ == 0 {
                    v___x_2470_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9,
                    );
                    v___x_2471_ = lean_uint8_dec_eq(v___y_2466_, v___x_2470_);
                    if v___x_2471_ == 0 {
                        v___x_2472_ = 1;
                        return v___x_2472_;
                    } else {
                        return v___x_2469_;
                    }
                } else {
                    v___x_2473_ = 0;
                    return v___x_2473_;
                }
            }
            2 => {
                if v___y_2475_ == 0 {
                    return v___y_2475_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2477_ == 0 {
                    v___x_2478_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0,
                    );
                    v___x_2479_ = lean_uint8_dec_eq(v___y_2466_, v___x_2478_);
                    if v___x_2479_ == 0 {
                        v___x_2480_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once
                            ),
                            _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1,
                        );
                        v___x_2481_ = lean_uint8_dec_eq(v___y_2466_, v___x_2480_);
                        v___y_2475_ = v___x_2481_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2475_ = v___x_2479_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_2483_ == 0 {
                    v___x_2484_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0,
                    );
                    v___x_2485_ = lean_uint8_dec_eq(v___y_2466_, v___x_2484_);
                    if v___x_2485_ == 0 {
                        v___x_2486_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1,
                        );
                        v___x_2487_ = lean_uint8_dec_eq(v___y_2466_, v___x_2486_);
                        v___y_2477_ = v___x_2487_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2477_ = v___x_2485_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_2489_ == 0 {
                    v___x_2490_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2,
                    );
                    v___x_2491_ = lean_uint8_dec_eq(v___y_2466_, v___x_2490_);
                    if v___x_2491_ == 0 {
                        v___x_2492_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3,
                        );
                        v___x_2493_ = lean_uint8_dec_eq(v___y_2466_, v___x_2492_);
                        if v___x_2493_ == 0 {
                            v___x_2494_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once
                                ),
                                _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4,
                            );
                            v___x_2495_ = lean_uint8_dec_eq(v___y_2466_, v___x_2494_);
                            if v___x_2495_ == 0 {
                                v___x_2496_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
                                v___x_2497_ = lean_uint8_dec_eq(v___y_2466_, v___x_2496_);
                                if v___x_2497_ == 0 {
                                    v___x_2498_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
                                    v___x_2499_ = lean_uint8_dec_eq(v___y_2466_, v___x_2498_);
                                    if v___x_2499_ == 0 {
                                        v___x_2500_ = leanh::lean_uint8_once(
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Std_Http_URI_isEncodedQueryChar___closed__0_once
                                            ),
                                            _init_l_Std_Http_URI_isEncodedQueryChar___closed__0,
                                        );
                                        v___x_2501_ = lean_uint8_dec_eq(v___y_2466_, v___x_2500_);
                                        if v___x_2501_ == 0 {
                                            v___x_2502_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
                                            v___x_2503_ =
                                                lean_uint8_dec_eq(v___y_2466_, v___x_2502_);
                                            if v___x_2503_ == 0 {
                                                v___x_2504_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
                                                v___x_2505_ =
                                                    lean_uint8_dec_eq(v___y_2466_, v___x_2504_);
                                                if v___x_2505_ == 0 {
                                                    v___x_2506_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once), _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
                                                    v___x_2507_ =
                                                        lean_uint8_dec_eq(v___y_2466_, v___x_2506_);
                                                    v___y_2483_ = v___x_2507_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    v___y_2483_ = v___x_2505_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                v___y_2483_ = v___x_2503_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            v___y_2483_ = v___x_2501_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v___y_2483_ = v___x_2499_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___y_2483_ = v___x_2497_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___y_2483_ = v___x_2495_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_2483_ = v___x_2493_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_2483_ = v___x_2491_;
                        state = 4;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            6 => {
                if v___y_2509_ == 0 {
                    v___x_2510_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10,
                    );
                    v___x_2511_ = lean_uint8_dec_eq(v___y_2466_, v___x_2510_);
                    if v___x_2511_ == 0 {
                        v___x_2512_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11,
                        );
                        v___x_2513_ = lean_uint8_dec_eq(v___y_2466_, v___x_2512_);
                        v___y_2489_ = v___x_2513_;
                        state = 5;
                        continue;
                    } else {
                        v___y_2489_ = v___x_2511_;
                        state = 5;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v___y_2515_ == 0 {
                    v___x_2516_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12,
                    );
                    v___x_2517_ = lean_uint8_dec_eq(v___y_2466_, v___x_2516_);
                    if v___x_2517_ == 0 {
                        v___x_2518_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13,
                        );
                        v___x_2519_ = lean_uint8_dec_eq(v___y_2466_, v___x_2518_);
                        v___y_2509_ = v___x_2519_;
                        state = 6;
                        continue;
                    } else {
                        v___y_2509_ = v___x_2517_;
                        state = 6;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v___y_2521_ == 0 {
                    v___x_2522_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once
                        ),
                        _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14,
                    );
                    v___x_2523_ = lean_uint8_dec_eq(v___y_2466_, v___x_2522_);
                    if v___x_2523_ == 0 {
                        v___x_2524_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15,
                        );
                        v___x_2525_ = lean_uint8_dec_eq(v___y_2466_, v___x_2524_);
                        v___y_2515_ = v___x_2525_;
                        state = 7;
                        continue;
                    } else {
                        v___y_2515_ = v___x_2523_;
                        state = 7;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            9 => {
                if v___y_2527_ == 0 {
                    v___x_2528_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__1_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__1,
                    );
                    v___x_2529_ = lean_uint8_dec_le(v___x_2528_, v___y_2466_);
                    if v___x_2529_ == 0 {
                        v___y_2521_ = v___x_2529_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2530_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16,
                        );
                        v___x_2531_ = lean_uint8_dec_le(v___y_2466_, v___x_2530_);
                        v___y_2521_ = v___x_2531_;
                        state = 8;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            10 => {
                if v___y_2533_ == 0 {
                    v___x_2534_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Http_URI_isEncodedChar___closed__3_once),
                        _init_l_Std_Http_URI_isEncodedChar___closed__3,
                    );
                    v___x_2535_ = lean_uint8_dec_le(v___x_2534_, v___y_2466_);
                    if v___x_2535_ == 0 {
                        v___y_2527_ = v___x_2535_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2536_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once
                            ),
                            _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17,
                        );
                        v___x_2537_ = lean_uint8_dec_le(v___y_2466_, v___x_2536_);
                        v___y_2527_ = v___x_2537_;
                        state = 9;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(
    mut v___y_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_362__boxed_2543_: u8 = 0;
    let mut v_res_2544_: u8 = 0;
    let mut v_r_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_362__boxed_2543_ = (leanh::lean_unbox(v___y_2542_) as u8);
    v_res_2544_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_362__boxed_2543_);
    v_r_2545_ = leanh::lean_box((v_res_2544_) as usize);
    return v_r_2545_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_encode(
    mut v_s_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2548_ = l_Std_Http_URI_EncodedQueryParam_encode___closed__0;
    v___x_2549_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_2547_, v___f_2548_);
    return v___x_2549_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_encode___boxed(
    mut v_s_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_2550_);
    leanh::lean_dec_ref(v_s_2550_);
    return v_res_2551_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(
    mut v_ba_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2553_ = l_Std_Http_URI_EncodedQueryParam_encode___closed__0;
    v___x_2554_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_2552_, v___f_2553_);
    return v___x_2554_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(
    mut v_ba_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2556_ = l_Std_Http_URI_EncodedQueryParam_encode___closed__0;
    v___x_2557_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_2555_, v___f_2556_);
    return v___x_2557_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_fromString_x3f(
    mut v_s_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2559_ = l_Std_Http_URI_EncodedQueryParam_encode___closed__0;
    v___x_2560_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_2558_, v___f_2559_);
    return v___x_2560_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(
    mut v_s_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_2561_);
    leanh::lean_dec_ref(v_s_2561_);
    return v_res_2562_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_decode(
    mut v_param_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Std_Http_URI_EncodedQueryParam_decode___boxed(
    mut v_param_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2566_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_2565_);
    leanh::lean_dec_ref(v_param_2565_);
    return v_res_2566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_URI_Encoding(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_URI_Encoding(
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
pub unsafe fn initialize_Std_Http_Data_URI_Encoding(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Encoding(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_URI_Encoding(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_URI_Encoding(builtin);
}