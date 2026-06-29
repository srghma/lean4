// Lean compiler output
// Module: Std.Internal.Parsec.ByteArray
// Imports: Std.Internal.Parsec.Basic Init.Data.String.Basic Std.Data.ByteSlice Init.Omega
use crate::r#gen::Init::Data::ByteArray::Basic::{
    l_ByteArray_Iterator_remainingBytes, l_ByteArray_mkIterator,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::ByteSlice::{
    initialize_Std_Data_ByteSlice, l_ByteArray_toByteSlice, runtime_initialize_Std_Data_ByteSlice,
};
use crate::r#gen::Std::Internal::Parsec::Basic::{
    initialize_Std_Internal_Parsec_Basic, runtime_initialize_Std_Internal_Parsec_Basic,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_fget;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::UInt::Basic::lean_uint8_sub;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint32_to_uint8,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint8_of_nat,
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0: u8 = 0;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value:
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
    m_fun: l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value:
    crate::leanh::LeanCtorObject<6> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0_value:
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
    m_data: [111, 102, 102, 115, 101, 116, 32, 0],
};
static mut l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105,
        110, 112, 117, 116, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_pbyte___closed__0_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0],
};
static mut l_Std_Internal_Parsec_ByteArray_pbyte___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_pbyte___closed__1_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_Std_Internal_Parsec_ByteArray_pbyte___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 98, 121, 116, 101, 32, 0]};
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_digit___closed__0_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
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
        100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_digit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_digit___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_digit___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_digit___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__2: u8 = 0;
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_digit___closed__3: u8 = 0;
pub static l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        104, 101, 120, 32, 100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2: u8 = 0;
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3: u8 = 0;
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4: u8 = 0;
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5: u8 = 0;
pub static l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
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
        111, 99, 116, 97, 108, 32, 100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101,
        100, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_octDigit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_octDigit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_ByteArray_octDigit___closed__2: u8 = 0;
pub static l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        65, 83, 67, 73, 73, 32, 108, 101, 116, 116, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101,
        100, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2: u8 = 0;
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3: u8 = 0;
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0: u8 = 0;
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1: u8 = 0;
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2: u8 = 0;
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3: u8 = 0;
pub static l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111,
        110, 101, 32, 99, 104, 97, 114, 0,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(
    mut v_it_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_idx_1135_ = crate::leanh::lean_ctor_get(v_it_1134_, 1);
    crate::leanh::lean_inc(v_idx_1135_);
    return v_idx_1135_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(
    mut v_it_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(v_it_1136_);
    crate::leanh::lean_dec_ref(v_it_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(
    mut v_it_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1139_ = crate::leanh::lean_ctor_get(v_it_1138_, 0);
                v_idx_1140_ = crate::leanh::lean_ctor_get(v_it_1138_, 1);
                v_isSharedCheck_1149_ = (!crate::leanh::lean_is_exclusive(v_it_1138_)) as u8;
                if v_isSharedCheck_1149_ == 0 {
                    v___x_1142_ = v_it_1138_;
                    v_isShared_1143_ = v_isSharedCheck_1149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1140_);
                    crate::leanh::lean_inc(v_array_1139_);
                    crate::leanh::lean_dec(v_it_1138_);
                    v___x_1142_ = crate::leanh::lean_box(0);
                    v_isShared_1143_ = v_isSharedCheck_1149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1144_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1145_ = lean_nat_add(v_idx_1140_, v___x_1144_);
                crate::leanh::lean_dec(v_idx_1140_);
                if v_isShared_1143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1142_, 1, v___x_1145_);
                    v___x_1147_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_array_1139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
                    v___x_1147_ = v_reuseFailAlloc_1148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0()
-> u8 {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    v___x_1150_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1151_ = lean_uint8_of_nat(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(
    mut v_it_1152_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_array_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    v_array_1153_ = crate::leanh::lean_ctor_get(v_it_1152_, 0);
    v_idx_1154_ = crate::leanh::lean_ctor_get(v_it_1152_, 1);
    v___x_1155_ = lean_byte_array_size(v_array_1153_);
    v___x_1156_ = lean_nat_dec_lt(v_idx_1154_, v___x_1155_);
    if v___x_1156_ == 0 {
        let mut v___x_1157_: u8 = 0;
        v___x_1157_ = crate::leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(
                l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0
            ),
            core::ptr::addr_of_mut!(
                l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once
            ),
            _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0,
        );
        return v___x_1157_;
    } else {
        let mut v___x_1158_: u8 = 0;
        v___x_1158_ = lean_byte_array_fget(v_array_1153_, v_idx_1154_);
        return v___x_1158_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(
    mut v_it_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1160_: u8 = 0;
    let mut v_r_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(v_it_1159_);
    crate::leanh::lean_dec_ref(v_it_1159_);
    v_r_1161_ = crate::leanh::lean_box((v_res_1160_) as usize);
    return v_r_1161_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(
    mut v_it_1162_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_array_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    v_array_1163_ = crate::leanh::lean_ctor_get(v_it_1162_, 0);
    v_idx_1164_ = crate::leanh::lean_ctor_get(v_it_1162_, 1);
    v___x_1165_ = lean_byte_array_size(v_array_1163_);
    v___x_1166_ = lean_nat_dec_lt(v_idx_1164_, v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(
    mut v_it_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1168_: u8 = 0;
    let mut v_r_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1168_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(v_it_1167_);
    crate::leanh::lean_dec_ref(v_it_1167_);
    v_r_1169_ = crate::leanh::lean_box((v_res_1168_) as usize);
    return v_r_1169_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(
    mut v_it_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1172_ = crate::leanh::lean_ctor_get(v_it_1170_, 0);
                v_idx_1173_ = crate::leanh::lean_ctor_get(v_it_1170_, 1);
                v_isSharedCheck_1182_ = (!crate::leanh::lean_is_exclusive(v_it_1170_)) as u8;
                if v_isSharedCheck_1182_ == 0 {
                    v___x_1175_ = v_it_1170_;
                    v_isShared_1176_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1173_);
                    crate::leanh::lean_inc(v_array_1172_);
                    crate::leanh::lean_dec(v_it_1170_);
                    v___x_1175_ = crate::leanh::lean_box(0);
                    v_isShared_1176_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1177_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1178_ = lean_nat_add(v_idx_1173_, v___x_1177_);
                crate::leanh::lean_dec(v_idx_1173_);
                if v_isShared_1176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1175_, 1, v___x_1178_);
                    v___x_1180_ = v___x_1175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_array_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
                    v___x_1180_ = v_reuseFailAlloc_1181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(
    mut v_it_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_array_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    v_array_1185_ = crate::leanh::lean_ctor_get(v_it_1183_, 0);
    v_idx_1186_ = crate::leanh::lean_ctor_get(v_it_1183_, 1);
    v___x_1187_ = lean_byte_array_fget(v_array_1185_, v_idx_1186_);
    return v___x_1187_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(
    mut v_it_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1190_: u8 = 0;
    let mut v_r_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(v_it_1188_, v___y_1189_);
    crate::leanh::lean_dec_ref(v_it_1188_);
    v_r_1191_ = crate::leanh::lean_box((v_res_1190_) as usize);
    return v_r_1191_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(
    mut v_p_1209_: *mut crate::leanh::LeanObject,
    mut v_arr_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1211_ = l_ByteArray_mkIterator(v_arr_1210_);
                v___x_1212_ = crate::leanh::lean_apply_1(v_p_1209_, v___x_1211_);
                if crate::leanh::lean_obj_tag(v___x_1212_) == 0 {
                    v_res_1213_ = crate::leanh::lean_ctor_get(v___x_1212_, 1);
                    crate::leanh::lean_inc(v_res_1213_);
                    crate::leanh::lean_dec_ref_known(v___x_1212_, 2);
                    v___x_1214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v_res_1213_);
                    return v___x_1214_;
                } else {
                    v_pos_1215_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                    crate::leanh::lean_inc(v_pos_1215_);
                    v_err_1216_ = crate::leanh::lean_ctor_get(v___x_1212_, 1);
                    crate::leanh::lean_inc(v_err_1216_);
                    crate::leanh::lean_dec_ref_known(v___x_1212_, 2);
                    v_idx_1217_ = crate::leanh::lean_ctor_get(v_pos_1215_, 1);
                    crate::leanh::lean_inc(v_idx_1217_);
                    crate::leanh::lean_dec(v_pos_1215_);
                    v___x_1218_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0;
                    v___x_1219_ = l_Nat_reprFast(v_idx_1217_);
                    v___x_1220_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                    v___x_1221_ = l_Std_Format_defWidth;
                    v___x_1222_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1223_ =
                        l_Std_Format_pretty(v___x_1220_, v___x_1221_, v___x_1222_, v___x_1222_);
                    v___x_1224_ = lean_string_append(v___x_1218_, v___x_1223_);
                    crate::leanh::lean_dec_ref(v___x_1223_);
                    v___x_1225_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1;
                    v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
                    if crate::leanh::lean_obj_tag(v_err_1216_) == 0 {
                        v___x_1231_ =
                            l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2;
                        v___y_1228_ = v___x_1231_;
                        state = 1;
                        continue;
                    } else {
                        v_s_1232_ = crate::leanh::lean_ctor_get(v_err_1216_, 0);
                        crate::leanh::lean_inc_ref(v_s_1232_);
                        crate::leanh::lean_dec_ref_known(v_err_1216_, 1);
                        v___y_1228_ = v_s_1232_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1229_ = lean_string_append(v___x_1226_, v___y_1228_);
                crate::leanh::lean_dec_ref(v___y_1228_);
                v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1229_);
                return v___x_1230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_Parser_run(
    mut v_00_u03b1_1233_: *mut crate::leanh::LeanObject,
    mut v_p_1234_: *mut crate::leanh::LeanObject,
    mut v_arr_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v_p_1234_, v_arr_1235_);
    return v___x_1236_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_pbyte(
    mut v_b_1239_: u8,
    mut v_it_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_got_1247_: u8 = 0;
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v_unused_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1241_ = crate::leanh::lean_ctor_get(v_it_1240_, 0);
                v_idx_1242_ = crate::leanh::lean_ctor_get(v_it_1240_, 1);
                v___x_1243_ = lean_byte_array_size(v_array_1241_);
                v___x_1244_ = lean_nat_dec_lt(v_idx_1242_, v___x_1243_);
                if v___x_1244_ == 0 {
                    v___x_1245_ = crate::leanh::lean_box(0);
                    v___x_1246_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1246_, 0, v_it_1240_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 1, v___x_1245_);
                    return v___x_1246_;
                } else {
                    v_got_1247_ = lean_byte_array_fget(v_array_1241_, v_idx_1242_);
                    v___x_1248_ = lean_uint8_dec_eq(v_got_1247_, v_b_1239_);
                    if v___x_1248_ == 0 {
                        v___x_1249_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
                        v___x_1250_ = lean_uint8_to_nat(v_b_1239_);
                        v___x_1251_ = l_Nat_reprFast(v___x_1250_);
                        v___x_1252_ = lean_string_append(v___x_1249_, v___x_1251_);
                        crate::leanh::lean_dec_ref(v___x_1251_);
                        v___x_1253_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
                        v___x_1254_ = lean_string_append(v___x_1252_, v___x_1253_);
                        v___x_1255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1255_, 0, v___x_1254_);
                        v___x_1256_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1256_, 0, v_it_1240_);
                        crate::leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
                        return v___x_1256_;
                    } else {
                        crate::leanh::lean_inc(v_idx_1242_);
                        crate::leanh::lean_inc_ref(v_array_1241_);
                        v_isSharedCheck_1267_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1240_)) as u8;
                        if v_isSharedCheck_1267_ == 0 {
                            v_unused_1268_ = crate::leanh::lean_ctor_get(v_it_1240_, 1);
                            crate::leanh::lean_dec(v_unused_1268_);
                            v_unused_1269_ = crate::leanh::lean_ctor_get(v_it_1240_, 0);
                            crate::leanh::lean_dec(v_unused_1269_);
                            v___x_1258_ = v_it_1240_;
                            v_isShared_1259_ = v_isSharedCheck_1267_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_it_1240_);
                            v___x_1258_ = crate::leanh::lean_box(0);
                            v_isShared_1259_ = v_isSharedCheck_1267_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1260_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1261_ = lean_nat_add(v_idx_1242_, v___x_1260_);
                crate::leanh::lean_dec(v_idx_1242_);
                if v_isShared_1259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1261_);
                    v___x_1263_ = v___x_1258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_array_1241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1261_);
                    v___x_1263_ = v_reuseFailAlloc_1266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1264_ = crate::leanh::lean_box((v_got_1247_) as usize);
                v___x_1265_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1265_, 0, v___x_1263_);
                crate::leanh::lean_ctor_set(v___x_1265_, 1, v___x_1264_);
                return v___x_1265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_pbyte___boxed(
    mut v_b_1270_: *mut crate::leanh::LeanObject,
    mut v_it_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1272_: u8 = 0;
    let mut v_res_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1272_ = (crate::leanh::lean_unbox(v_b_1270_) as u8);
    v_res_1273_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_boxed_1272_, v_it_1271_);
    return v_res_1273_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipByte(
    mut v_b_1274_: u8,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_got_1282_: u8 = 0;
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1302_: u8 = 0;
    let mut v_unused_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1276_ = crate::leanh::lean_ctor_get(v_a_1275_, 0);
                v_idx_1277_ = crate::leanh::lean_ctor_get(v_a_1275_, 1);
                v___x_1278_ = lean_byte_array_size(v_array_1276_);
                v___x_1279_ = lean_nat_dec_lt(v_idx_1277_, v___x_1278_);
                if v___x_1279_ == 0 {
                    v___x_1280_ = crate::leanh::lean_box(0);
                    v___x_1281_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1281_, 0, v_a_1275_);
                    crate::leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
                    return v___x_1281_;
                } else {
                    v_got_1282_ = lean_byte_array_fget(v_array_1276_, v_idx_1277_);
                    v___x_1283_ = lean_uint8_dec_eq(v_got_1282_, v_b_1274_);
                    if v___x_1283_ == 0 {
                        v___x_1284_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
                        v___x_1285_ = lean_uint8_to_nat(v_b_1274_);
                        v___x_1286_ = l_Nat_reprFast(v___x_1285_);
                        v___x_1287_ = lean_string_append(v___x_1284_, v___x_1286_);
                        crate::leanh::lean_dec_ref(v___x_1286_);
                        v___x_1288_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
                        v___x_1289_ = lean_string_append(v___x_1287_, v___x_1288_);
                        v___x_1290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
                        v___x_1291_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1291_, 0, v_a_1275_);
                        crate::leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
                        return v___x_1291_;
                    } else {
                        crate::leanh::lean_inc(v_idx_1277_);
                        crate::leanh::lean_inc_ref(v_array_1276_);
                        v_isSharedCheck_1302_ = (!crate::leanh::lean_is_exclusive(v_a_1275_)) as u8;
                        if v_isSharedCheck_1302_ == 0 {
                            v_unused_1303_ = crate::leanh::lean_ctor_get(v_a_1275_, 1);
                            crate::leanh::lean_dec(v_unused_1303_);
                            v_unused_1304_ = crate::leanh::lean_ctor_get(v_a_1275_, 0);
                            crate::leanh::lean_dec(v_unused_1304_);
                            v___x_1293_ = v_a_1275_;
                            v_isShared_1294_ = v_isSharedCheck_1302_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1275_);
                            v___x_1293_ = crate::leanh::lean_box(0);
                            v_isShared_1294_ = v_isSharedCheck_1302_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1295_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1296_ = lean_nat_add(v_idx_1277_, v___x_1295_);
                crate::leanh::lean_dec(v_idx_1277_);
                if v_isShared_1294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1293_, 1, v___x_1296_);
                    v___x_1298_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_array_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1296_);
                    v___x_1298_ = v_reuseFailAlloc_1301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1299_ = crate::leanh::lean_box(0);
                v___x_1300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1298_);
                crate::leanh::lean_ctor_set(v___x_1300_, 1, v___x_1299_);
                return v___x_1300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipByte___boxed(
    mut v_b_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1307_: u8 = 0;
    let mut v_res_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1307_ = (crate::leanh::lean_unbox(v_b_1305_) as u8);
    v_res_1308_ = l_Std_Internal_Parsec_ByteArray_skipByte(v_b_boxed_1307_, v_a_1306_);
    return v_res_1308_;
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(
    mut v_arr_1311_: *mut crate::leanh::LeanObject,
    mut v_idx_1312_: *mut crate::leanh::LeanObject,
    mut v_it_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_got_1324_: u8 = 0;
    let mut v_want_1325_: u8 = 0;
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_unused_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1314_ = lean_byte_array_size(v_arr_1311_);
                v___x_1315_ = lean_nat_dec_lt(v_idx_1312_, v___x_1314_);
                if v___x_1315_ == 0 {
                    crate::leanh::lean_dec(v_idx_1312_);
                    v___x_1316_ = crate::leanh::lean_box(0);
                    v___x_1317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1317_, 0, v_it_1313_);
                    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1316_);
                    return v___x_1317_;
                } else {
                    v_array_1318_ = crate::leanh::lean_ctor_get(v_it_1313_, 0);
                    v_idx_1319_ = crate::leanh::lean_ctor_get(v_it_1313_, 1);
                    v___x_1320_ = lean_byte_array_size(v_array_1318_);
                    v___x_1321_ = lean_nat_dec_lt(v_idx_1319_, v___x_1320_);
                    if v___x_1321_ == 0 {
                        crate::leanh::lean_dec(v_idx_1312_);
                        v___x_1322_ = crate::leanh::lean_box(0);
                        v___x_1323_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1323_, 0, v_it_1313_);
                        crate::leanh::lean_ctor_set(v___x_1323_, 1, v___x_1322_);
                        return v___x_1323_;
                    } else {
                        v_got_1324_ = lean_byte_array_fget(v_array_1318_, v_idx_1319_);
                        v_want_1325_ = lean_byte_array_fget(v_arr_1311_, v_idx_1312_);
                        v___x_1326_ = lean_uint8_dec_eq(v_got_1324_, v_want_1325_);
                        if v___x_1326_ == 0 {
                            crate::leanh::lean_dec(v_idx_1312_);
                            v___x_1327_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0;
                            v___x_1328_ = lean_uint8_to_nat(v_want_1325_);
                            v___x_1329_ = l_Nat_reprFast(v___x_1328_);
                            v___x_1330_ = lean_string_append(v___x_1327_, v___x_1329_);
                            crate::leanh::lean_dec_ref(v___x_1329_);
                            v___x_1331_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1;
                            v___x_1332_ = lean_string_append(v___x_1330_, v___x_1331_);
                            v___x_1333_ = lean_uint8_to_nat(v_got_1324_);
                            v___x_1334_ = l_Nat_reprFast(v___x_1333_);
                            v___x_1335_ = lean_string_append(v___x_1332_, v___x_1334_);
                            crate::leanh::lean_dec_ref(v___x_1334_);
                            v___x_1336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1335_);
                            v___x_1337_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1337_, 0, v_it_1313_);
                            crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1336_);
                            return v___x_1337_;
                        } else {
                            crate::leanh::lean_inc(v_idx_1319_);
                            crate::leanh::lean_inc_ref(v_array_1318_);
                            v_isSharedCheck_1348_ =
                                (!crate::leanh::lean_is_exclusive(v_it_1313_)) as u8;
                            if v_isSharedCheck_1348_ == 0 {
                                v_unused_1349_ = crate::leanh::lean_ctor_get(v_it_1313_, 1);
                                crate::leanh::lean_dec(v_unused_1349_);
                                v_unused_1350_ = crate::leanh::lean_ctor_get(v_it_1313_, 0);
                                crate::leanh::lean_dec(v_unused_1350_);
                                v___x_1339_ = v_it_1313_;
                                v_isShared_1340_ = v_isSharedCheck_1348_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_it_1313_);
                                v___x_1339_ = crate::leanh::lean_box(0);
                                v_isShared_1340_ = v_isSharedCheck_1348_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1341_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1342_ = lean_nat_add(v_idx_1312_, v___x_1341_);
                crate::leanh::lean_dec(v_idx_1312_);
                v___x_1343_ = lean_nat_add(v_idx_1319_, v___x_1341_);
                crate::leanh::lean_dec(v_idx_1319_);
                if v_isShared_1340_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1339_, 1, v___x_1343_);
                    v___x_1345_ = v___x_1339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_array_1318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1343_);
                    v___x_1345_ = v_reuseFailAlloc_1347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_idx_1312_ = v___x_1342_;
                v_it_1313_ = v___x_1345_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___boxed(
    mut v_arr_1351_: *mut crate::leanh::LeanObject,
    mut v_idx_1352_: *mut crate::leanh::LeanObject,
    mut v_it_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(
            v_arr_1351_,
            v_idx_1352_,
            v_it_1353_,
        );
    crate::leanh::lean_dec_ref(v_arr_1351_);
    return v_res_1354_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipBytes(
    mut v_arr_1355_: *mut crate::leanh::LeanObject,
    mut v_it_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1358_ =
        l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(
            v_arr_1355_,
            v___x_1357_,
            v_it_1356_,
        );
    return v___x_1358_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(
    mut v_arr_1359_: *mut crate::leanh::LeanObject,
    mut v_it_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_arr_1359_, v_it_1360_);
    crate::leanh::lean_dec_ref(v_arr_1359_);
    return v_res_1361_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_pstring(
    mut v_s_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_utf8_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_unused_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1364_ = lean_string_to_utf8(v_s_1362_);
                v___x_1365_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1364_, v_a_1363_);
                crate::leanh::lean_dec_ref(v_utf8_1364_);
                if crate::leanh::lean_obj_tag(v___x_1365_) == 0 {
                    v_pos_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v_unused_1374_ = crate::leanh::lean_ctor_get(v___x_1365_, 1);
                        crate::leanh::lean_dec(v_unused_1374_);
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1366_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1368_ = crate::leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_1362_);
                    v_pos_1375_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_err_1376_ = crate::leanh::lean_ctor_get(v___x_1365_, 1);
                    v_isSharedCheck_1383_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1383_ == 0 {
                        v___x_1378_ = v___x_1365_;
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1376_);
                        crate::leanh::lean_inc(v_pos_1375_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1378_ = crate::leanh::lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1368_, 1, v_s_1362_);
                    v___x_1371_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_pos_1366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_s_1362_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1371_;
            }
            3 => {
                if v_isShared_1379_ == 0 {
                    v___x_1381_ = v___x_1378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_pos_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_err_1376_);
                    v___x_1381_ = v_reuseFailAlloc_1382_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipString(
    mut v_s_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_utf8_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_unused_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1386_ = lean_string_to_utf8(v_s_1384_);
                v___x_1387_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1386_, v_a_1385_);
                crate::leanh::lean_dec_ref(v_utf8_1386_);
                if crate::leanh::lean_obj_tag(v___x_1387_) == 0 {
                    v_pos_1388_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                    v_isSharedCheck_1396_ = (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v_unused_1397_ = crate::leanh::lean_ctor_get(v___x_1387_, 1);
                        crate::leanh::lean_dec(v_unused_1397_);
                        v___x_1390_ = v___x_1387_;
                        v_isShared_1391_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1388_);
                        crate::leanh::lean_dec(v___x_1387_);
                        v___x_1390_ = crate::leanh::lean_box(0);
                        v_isShared_1391_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1387_;
                }
            }
            1 => {
                v___x_1392_ = crate::leanh::lean_box(0);
                if v_isShared_1391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1390_, 1, v___x_1392_);
                    v___x_1394_ = v___x_1390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_pos_1388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1392_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipString___boxed(
    mut v_s_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_Internal_Parsec_ByteArray_skipString(v_s_1398_, v_a_1399_);
    crate::leanh::lean_dec_ref(v_s_1398_);
    return v_res_1400_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_pByteChar(
    mut v_c_1402_: u32,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1410_: u8 = 0;
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut v_unused_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1404_ = crate::leanh::lean_ctor_get(v_a_1403_, 0);
                v_idx_1405_ = crate::leanh::lean_ctor_get(v_a_1403_, 1);
                v___x_1406_ = lean_byte_array_size(v_array_1404_);
                v___x_1407_ = lean_nat_dec_lt(v_idx_1405_, v___x_1406_);
                if v___x_1407_ == 0 {
                    v___x_1408_ = crate::leanh::lean_box(0);
                    v___x_1409_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1409_, 0, v_a_1403_);
                    crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
                    return v___x_1409_;
                } else {
                    v_c_1410_ = lean_byte_array_fget(v_array_1404_, v_idx_1405_);
                    v___x_1411_ = lean_uint32_to_uint8(v_c_1402_);
                    v___x_1412_ = lean_uint8_dec_eq(v_c_1410_, v___x_1411_);
                    if v___x_1412_ == 0 {
                        v___x_1413_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
                        v___x_1414_ = l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0;
                        v___x_1415_ = lean_string_push(v___x_1414_, v_c_1402_);
                        v___x_1416_ = lean_string_append(v___x_1413_, v___x_1415_);
                        crate::leanh::lean_dec_ref(v___x_1415_);
                        v___x_1417_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
                        v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
                        v___x_1419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1419_, 0, v___x_1418_);
                        v___x_1420_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1420_, 0, v_a_1403_);
                        crate::leanh::lean_ctor_set(v___x_1420_, 1, v___x_1419_);
                        return v___x_1420_;
                    } else {
                        crate::leanh::lean_inc(v_idx_1405_);
                        crate::leanh::lean_inc_ref(v_array_1404_);
                        v_isSharedCheck_1431_ = (!crate::leanh::lean_is_exclusive(v_a_1403_)) as u8;
                        if v_isSharedCheck_1431_ == 0 {
                            v_unused_1432_ = crate::leanh::lean_ctor_get(v_a_1403_, 1);
                            crate::leanh::lean_dec(v_unused_1432_);
                            v_unused_1433_ = crate::leanh::lean_ctor_get(v_a_1403_, 0);
                            crate::leanh::lean_dec(v_unused_1433_);
                            v___x_1422_ = v_a_1403_;
                            v_isShared_1423_ = v_isSharedCheck_1431_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1403_);
                            v___x_1422_ = crate::leanh::lean_box(0);
                            v_isShared_1423_ = v_isSharedCheck_1431_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1424_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1425_ = lean_nat_add(v_idx_1405_, v___x_1424_);
                crate::leanh::lean_dec(v_idx_1405_);
                if v_isShared_1423_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1422_, 1, v___x_1425_);
                    v_it_x27_1427_ = v___x_1422_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_array_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1425_);
                    v_it_x27_1427_ = v_reuseFailAlloc_1430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1428_ = crate::leanh::lean_box_uint32(v_c_1402_);
                v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1429_, 0, v_it_x27_1427_);
                crate::leanh::lean_ctor_set(v___x_1429_, 1, v___x_1428_);
                return v___x_1429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(
    mut v_c_1434_: *mut crate::leanh::LeanObject,
    mut v_a_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1436_: u32 = 0;
    let mut v_res_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1436_ = crate::leanh::lean_unbox_uint32(v_c_1434_);
    crate::leanh::lean_dec(v_c_1434_);
    v_res_1437_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_boxed_1436_, v_a_1435_);
    return v_res_1437_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipByteChar(
    mut v_c_1438_: u32,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v_got_1447_: u8 = 0;
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1467_: u8 = 0;
    let mut v_unused_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1440_ = crate::leanh::lean_ctor_get(v_a_1439_, 0);
                v_idx_1441_ = crate::leanh::lean_ctor_get(v_a_1439_, 1);
                v___x_1442_ = lean_byte_array_size(v_array_1440_);
                v___x_1443_ = lean_nat_dec_lt(v_idx_1441_, v___x_1442_);
                if v___x_1443_ == 0 {
                    v___x_1444_ = crate::leanh::lean_box(0);
                    v___x_1445_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1445_, 0, v_a_1439_);
                    crate::leanh::lean_ctor_set(v___x_1445_, 1, v___x_1444_);
                    return v___x_1445_;
                } else {
                    v___x_1446_ = lean_uint32_to_uint8(v_c_1438_);
                    v_got_1447_ = lean_byte_array_fget(v_array_1440_, v_idx_1441_);
                    v___x_1448_ = lean_uint8_dec_eq(v_got_1447_, v___x_1446_);
                    if v___x_1448_ == 0 {
                        v___x_1449_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
                        v___x_1450_ = lean_uint8_to_nat(v___x_1446_);
                        v___x_1451_ = l_Nat_reprFast(v___x_1450_);
                        v___x_1452_ = lean_string_append(v___x_1449_, v___x_1451_);
                        crate::leanh::lean_dec_ref(v___x_1451_);
                        v___x_1453_ = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
                        v___x_1454_ = lean_string_append(v___x_1452_, v___x_1453_);
                        v___x_1455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
                        v___x_1456_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1456_, 0, v_a_1439_);
                        crate::leanh::lean_ctor_set(v___x_1456_, 1, v___x_1455_);
                        return v___x_1456_;
                    } else {
                        crate::leanh::lean_inc(v_idx_1441_);
                        crate::leanh::lean_inc_ref(v_array_1440_);
                        v_isSharedCheck_1467_ = (!crate::leanh::lean_is_exclusive(v_a_1439_)) as u8;
                        if v_isSharedCheck_1467_ == 0 {
                            v_unused_1468_ = crate::leanh::lean_ctor_get(v_a_1439_, 1);
                            crate::leanh::lean_dec(v_unused_1468_);
                            v_unused_1469_ = crate::leanh::lean_ctor_get(v_a_1439_, 0);
                            crate::leanh::lean_dec(v_unused_1469_);
                            v___x_1458_ = v_a_1439_;
                            v_isShared_1459_ = v_isSharedCheck_1467_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1439_);
                            v___x_1458_ = crate::leanh::lean_box(0);
                            v_isShared_1459_ = v_isSharedCheck_1467_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1460_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1461_ = lean_nat_add(v_idx_1441_, v___x_1460_);
                crate::leanh::lean_dec(v_idx_1441_);
                if v_isShared_1459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1461_);
                    v___x_1463_ = v___x_1458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_array_1440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1461_);
                    v___x_1463_ = v_reuseFailAlloc_1466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1464_ = crate::leanh::lean_box(0);
                v___x_1465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1463_);
                crate::leanh::lean_ctor_set(v___x_1465_, 1, v___x_1464_);
                return v___x_1465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(
    mut v_c_1470_: *mut crate::leanh::LeanObject,
    mut v_a_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1472_: u32 = 0;
    let mut v_res_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1472_ = crate::leanh::lean_unbox_uint32(v_c_1470_);
    crate::leanh::lean_dec(v_c_1470_);
    v_res_1473_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_boxed_1472_, v_a_1471_);
    return v_res_1473_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2() -> u8 {
    let mut v___x_1477_: u32 = 0;
    let mut v___x_1478_: u8 = 0;
    v___x_1477_ = 48;
    v___x_1478_ = lean_uint32_to_uint8(v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3() -> u8 {
    let mut v___x_1479_: u32 = 0;
    let mut v___x_1480_: u8 = 0;
    v___x_1479_ = 57;
    v___x_1480_ = lean_uint32_to_uint8(v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_digit(
    mut v_a_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1491_: u8 = 0;
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u32 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_unused_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1485_ = crate::leanh::lean_ctor_get(v_a_1481_, 0);
                v_idx_1486_ = crate::leanh::lean_ctor_get(v_a_1481_, 1);
                v___x_1487_ = lean_byte_array_size(v_array_1485_);
                v___x_1488_ = lean_nat_dec_lt(v_idx_1486_, v___x_1487_);
                if v___x_1488_ == 0 {
                    v___x_1489_ = crate::leanh::lean_box(0);
                    v___x_1490_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1490_, 0, v_a_1481_);
                    crate::leanh::lean_ctor_set(v___x_1490_, 1, v___x_1489_);
                    return v___x_1490_;
                } else {
                    v_c_1491_ = lean_byte_array_fget(v_array_1485_, v_idx_1486_);
                    v___x_1492_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_digit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
                    );
                    v___x_1493_ = lean_uint8_dec_le(v___x_1492_, v_c_1491_);
                    if v___x_1493_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1494_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3,
                        );
                        v___x_1495_ = lean_uint8_dec_le(v_c_1491_, v___x_1494_);
                        if v___x_1495_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_idx_1486_);
                            crate::leanh::lean_inc_ref(v_array_1485_);
                            v_isSharedCheck_1507_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1481_)) as u8;
                            if v_isSharedCheck_1507_ == 0 {
                                v_unused_1508_ = crate::leanh::lean_ctor_get(v_a_1481_, 1);
                                crate::leanh::lean_dec(v_unused_1508_);
                                v_unused_1509_ = crate::leanh::lean_ctor_get(v_a_1481_, 0);
                                crate::leanh::lean_dec(v_unused_1509_);
                                v___x_1497_ = v_a_1481_;
                                v_isShared_1498_ = v_isSharedCheck_1507_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1481_);
                                v___x_1497_ = crate::leanh::lean_box(0);
                                v_isShared_1498_ = v_isSharedCheck_1507_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1483_ = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
                v___x_1484_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1484_, 0, v_a_1481_);
                crate::leanh::lean_ctor_set(v___x_1484_, 1, v___x_1483_);
                return v___x_1484_;
            }
            2 => {
                v___x_1499_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1500_ = lean_nat_add(v_idx_1486_, v___x_1499_);
                crate::leanh::lean_dec(v_idx_1486_);
                if v_isShared_1498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1497_, 1, v___x_1500_);
                    v_it_x27_1502_ = v___x_1497_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_array_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1500_);
                    v_it_x27_1502_ = v_reuseFailAlloc_1506_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1503_ = lean_uint8_to_uint32(v_c_1491_);
                v___x_1504_ = crate::leanh::lean_box_uint32(v___x_1503_);
                v___x_1505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v_it_x27_1502_);
                crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                return v___x_1505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(
    mut v_b_1510_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2_once),
        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
    );
    v___x_1512_ = lean_uint8_sub(v_b_1510_, v___x_1511_);
    v___x_1513_ = lean_uint8_to_nat(v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(
    mut v_b_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1515_: u8 = 0;
    let mut v_res_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1515_ = (crate::leanh::lean_unbox(v_b_1514_) as u8);
    v_res_1516_ =
        l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(
            v_b_boxed_1515_,
        );
    return v_res_1516_;
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(
    mut v_it_1517_: *mut crate::leanh::LeanObject,
    mut v_acc_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidate_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: u8 = 0;
    let mut v_digit_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_unused_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1519_ = crate::leanh::lean_ctor_get(v_it_1517_, 0);
                v_idx_1520_ = crate::leanh::lean_ctor_get(v_it_1517_, 1);
                v___x_1521_ = lean_byte_array_size(v_array_1519_);
                v___x_1522_ = lean_nat_dec_lt(v_idx_1520_, v___x_1521_);
                if v___x_1522_ == 0 {
                    v___x_1523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1523_, 0, v_acc_1518_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 1, v_it_1517_);
                    return v___x_1523_;
                } else {
                    v_candidate_1524_ = lean_byte_array_fget(v_array_1519_, v_idx_1520_);
                    v___x_1525_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_digit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
                    );
                    v___x_1526_ = lean_uint8_dec_le(v___x_1525_, v_candidate_1524_);
                    if v___x_1526_ == 0 {
                        v___x_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1527_, 0, v_acc_1518_);
                        crate::leanh::lean_ctor_set(v___x_1527_, 1, v_it_1517_);
                        return v___x_1527_;
                    } else {
                        v___x_1528_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3,
                        );
                        v___x_1529_ = lean_uint8_dec_le(v_candidate_1524_, v___x_1528_);
                        if v___x_1529_ == 0 {
                            v___x_1530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1530_, 0, v_acc_1518_);
                            crate::leanh::lean_ctor_set(v___x_1530_, 1, v_it_1517_);
                            return v___x_1530_;
                        } else {
                            crate::leanh::lean_inc(v_idx_1520_);
                            crate::leanh::lean_inc_ref(v_array_1519_);
                            v_isSharedCheck_1545_ =
                                (!crate::leanh::lean_is_exclusive(v_it_1517_)) as u8;
                            if v_isSharedCheck_1545_ == 0 {
                                v_unused_1546_ = crate::leanh::lean_ctor_get(v_it_1517_, 1);
                                crate::leanh::lean_dec(v_unused_1546_);
                                v_unused_1547_ = crate::leanh::lean_ctor_get(v_it_1517_, 0);
                                crate::leanh::lean_dec(v_unused_1547_);
                                v___x_1532_ = v_it_1517_;
                                v_isShared_1533_ = v_isSharedCheck_1545_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_it_1517_);
                                v___x_1532_ = crate::leanh::lean_box(0);
                                v_isShared_1533_ = v_isSharedCheck_1545_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1534_ = lean_uint8_sub(v_candidate_1524_, v___x_1525_);
                v_digit_1535_ = lean_uint8_to_nat(v___x_1534_);
                v___x_1536_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1537_ = lean_nat_mul(v_acc_1518_, v___x_1536_);
                crate::leanh::lean_dec(v_acc_1518_);
                v_acc_1538_ = lean_nat_add(v___x_1537_, v_digit_1535_);
                crate::leanh::lean_dec(v___x_1537_);
                v___x_1539_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1540_ = lean_nat_add(v_idx_1520_, v___x_1539_);
                crate::leanh::lean_dec(v_idx_1520_);
                if v_isShared_1533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1532_, 1, v___x_1540_);
                    v___x_1542_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_array_1519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1540_);
                    v___x_1542_ = v_reuseFailAlloc_1544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_it_1517_ = v___x_1542_;
                v_acc_1518_ = v_acc_1538_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(
    mut v_acc_1548_: *mut crate::leanh::LeanObject,
    mut v_it_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_1549_, v_acc_1548_);
                v_fst_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                v_snd_1552_ = crate::leanh::lean_ctor_get(v___x_1550_, 1);
                v_isSharedCheck_1559_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                if v_isSharedCheck_1559_ == 0 {
                    v___x_1554_ = v___x_1550_;
                    v_isShared_1555_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1552_);
                    crate::leanh::lean_inc(v_fst_1551_);
                    crate::leanh::lean_dec(v___x_1550_);
                    v___x_1554_ = crate::leanh::lean_box(0);
                    v_isShared_1555_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1554_, 1, v_fst_1551_);
                    crate::leanh::lean_ctor_set(v___x_1554_, 0, v_snd_1552_);
                    v___x_1557_ = v___x_1554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_snd_1552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_fst_1551_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_digits(
    mut v_a_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1570_: u8 = 0;
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u32 = 0;
    let mut v___x_1583_: u8 = 0;
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_unused_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1564_ = crate::leanh::lean_ctor_get(v_a_1560_, 0);
                v_idx_1565_ = crate::leanh::lean_ctor_get(v_a_1560_, 1);
                v___x_1566_ = lean_byte_array_size(v_array_1564_);
                v___x_1567_ = lean_nat_dec_lt(v_idx_1565_, v___x_1566_);
                if v___x_1567_ == 0 {
                    v___x_1568_ = crate::leanh::lean_box(0);
                    v___x_1569_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1569_, 0, v_a_1560_);
                    crate::leanh::lean_ctor_set(v___x_1569_, 1, v___x_1568_);
                    return v___x_1569_;
                } else {
                    v_c_1570_ = lean_byte_array_fget(v_array_1564_, v_idx_1565_);
                    v___x_1571_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_digit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
                    );
                    v___x_1572_ = lean_uint8_dec_le(v___x_1571_, v_c_1570_);
                    if v___x_1572_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1573_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3,
                        );
                        v___x_1574_ = lean_uint8_dec_le(v_c_1570_, v___x_1573_);
                        if v___x_1574_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_idx_1565_);
                            crate::leanh::lean_inc_ref(v_array_1564_);
                            v_isSharedCheck_1597_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1560_)) as u8;
                            if v_isSharedCheck_1597_ == 0 {
                                v_unused_1598_ = crate::leanh::lean_ctor_get(v_a_1560_, 1);
                                crate::leanh::lean_dec(v_unused_1598_);
                                v_unused_1599_ = crate::leanh::lean_ctor_get(v_a_1560_, 0);
                                crate::leanh::lean_dec(v_unused_1599_);
                                v___x_1576_ = v_a_1560_;
                                v_isShared_1577_ = v_isSharedCheck_1597_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1560_);
                                v___x_1576_ = crate::leanh::lean_box(0);
                                v_isShared_1577_ = v_isSharedCheck_1597_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1562_ = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
                v___x_1563_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1563_, 0, v_a_1560_);
                crate::leanh::lean_ctor_set(v___x_1563_, 1, v___x_1562_);
                return v___x_1563_;
            }
            2 => {
                v___x_1578_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1579_ = lean_nat_add(v_idx_1565_, v___x_1578_);
                crate::leanh::lean_dec(v_idx_1565_);
                if v_isShared_1577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1576_, 1, v___x_1579_);
                    v_it_x27_1581_ = v___x_1576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_array_1564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1579_);
                    v_it_x27_1581_ = v_reuseFailAlloc_1596_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1582_ = lean_uint8_to_uint32(v_c_1570_);
                v___x_1583_ = lean_uint32_to_uint8(v___x_1582_);
                v___x_1584_ = lean_uint8_sub(v___x_1583_, v___x_1571_);
                v___x_1585_ = lean_uint8_to_nat(v___x_1584_);
                v___x_1586_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1581_, v___x_1585_);
                v_fst_1587_ = crate::leanh::lean_ctor_get(v___x_1586_, 0);
                v_snd_1588_ = crate::leanh::lean_ctor_get(v___x_1586_, 1);
                v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v___x_1586_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1590_ = v___x_1586_;
                    v_isShared_1591_ = v_isSharedCheck_1595_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1588_);
                    crate::leanh::lean_inc(v_fst_1587_);
                    crate::leanh::lean_dec(v___x_1586_);
                    v___x_1590_ = crate::leanh::lean_box(0);
                    v_isShared_1591_ = v_isSharedCheck_1595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1590_, 1, v_fst_1587_);
                    crate::leanh::lean_ctor_set(v___x_1590_, 0, v_snd_1588_);
                    v___x_1593_ = v___x_1590_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_snd_1588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_fst_1587_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2() -> u8 {
    let mut v___x_1603_: u32 = 0;
    let mut v___x_1604_: u8 = 0;
    v___x_1603_ = 65;
    v___x_1604_ = lean_uint32_to_uint8(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3() -> u8 {
    let mut v___x_1605_: u32 = 0;
    let mut v___x_1606_: u8 = 0;
    v___x_1605_ = 70;
    v___x_1606_ = lean_uint32_to_uint8(v___x_1605_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4() -> u8 {
    let mut v___x_1607_: u32 = 0;
    let mut v___x_1608_: u8 = 0;
    v___x_1607_ = 97;
    v___x_1608_ = lean_uint32_to_uint8(v___x_1607_);
    return v___x_1608_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5() -> u8 {
    let mut v___x_1609_: u32 = 0;
    let mut v___x_1610_: u8 = 0;
    v___x_1609_ = 102;
    v___x_1610_ = lean_uint32_to_uint8(v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_hexDigit(
    mut v_a_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u32 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1615_ = crate::leanh::lean_ctor_get(v_a_1611_, 0);
                v_idx_1616_ = crate::leanh::lean_ctor_get(v_a_1611_, 1);
                v___x_1617_ = lean_byte_array_size(v_array_1615_);
                v___x_1618_ = lean_nat_dec_lt(v_idx_1616_, v___x_1617_);
                if v___x_1618_ == 0 {
                    v___x_1619_ = crate::leanh::lean_box(0);
                    v___x_1620_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1620_, 0, v_a_1611_);
                    crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                    return v___x_1620_;
                } else {
                    v_c_1621_ = lean_byte_array_fget(v_array_1615_, v_idx_1616_);
                    v___x_1622_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1623_ = lean_nat_add(v_idx_1616_, v___x_1622_);
                    crate::leanh::lean_inc_ref(v_array_1615_);
                    v_it_x27_1624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_it_x27_1624_, 0, v_array_1615_);
                    crate::leanh::lean_ctor_set(v_it_x27_1624_, 1, v___x_1623_);
                    v___x_1639_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_digit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
                    );
                    v___x_1640_ = lean_uint8_dec_le(v___x_1639_, v_c_1621_);
                    if v___x_1640_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_1641_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_digit___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3,
                        );
                        v___x_1642_ = lean_uint8_dec_le(v_c_1621_, v___x_1641_);
                        if v___x_1642_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_1611_);
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1613_ = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1;
                v___x_1614_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1614_, 0, v_a_1611_);
                crate::leanh::lean_ctor_set(v___x_1614_, 1, v___x_1613_);
                return v___x_1614_;
            }
            2 => {
                v___x_1626_ = lean_uint8_to_uint32(v_c_1621_);
                v___x_1627_ = crate::leanh::lean_box_uint32(v___x_1626_);
                v___x_1628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1628_, 0, v_it_x27_1624_);
                crate::leanh::lean_ctor_set(v___x_1628_, 1, v___x_1627_);
                return v___x_1628_;
            }
            3 => {
                v___x_1630_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once
                    ),
                    _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2,
                );
                v___x_1631_ = lean_uint8_dec_le(v___x_1630_, v_c_1621_);
                if v___x_1631_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_it_x27_1624_, 2);
                    state = 1;
                    continue;
                } else {
                    v___x_1632_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3,
                    );
                    v___x_1633_ = lean_uint8_dec_le(v_c_1621_, v___x_1632_);
                    if v___x_1633_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_it_x27_1624_, 2);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1611_);
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1635_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once
                    ),
                    _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4,
                );
                v___x_1636_ = lean_uint8_dec_le(v___x_1635_, v_c_1621_);
                if v___x_1636_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_1637_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5,
                    );
                    v___x_1638_ = lean_uint8_dec_le(v_c_1621_, v___x_1637_);
                    if v___x_1638_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1611_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2() -> u8 {
    let mut v___x_1646_: u32 = 0;
    let mut v___x_1647_: u8 = 0;
    v___x_1646_ = 55;
    v___x_1647_ = lean_uint32_to_uint8(v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_octDigit(
    mut v_a_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u32 = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_unused_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1652_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                v_idx_1653_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                v___x_1654_ = lean_byte_array_size(v_array_1652_);
                v___x_1655_ = lean_nat_dec_lt(v_idx_1653_, v___x_1654_);
                if v___x_1655_ == 0 {
                    v___x_1656_ = crate::leanh::lean_box(0);
                    v___x_1657_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1657_, 0, v_a_1648_);
                    crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1656_);
                    return v___x_1657_;
                } else {
                    v_c_1658_ = lean_byte_array_fget(v_array_1652_, v_idx_1653_);
                    v___x_1659_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_digit___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_digit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2,
                    );
                    v___x_1660_ = lean_uint8_dec_le(v___x_1659_, v_c_1658_);
                    if v___x_1660_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1661_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_octDigit___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2,
                        );
                        v___x_1662_ = lean_uint8_dec_le(v_c_1658_, v___x_1661_);
                        if v___x_1662_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_idx_1653_);
                            crate::leanh::lean_inc_ref(v_array_1652_);
                            v_isSharedCheck_1674_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1648_)) as u8;
                            if v_isSharedCheck_1674_ == 0 {
                                v_unused_1675_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                                crate::leanh::lean_dec(v_unused_1675_);
                                v_unused_1676_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                                crate::leanh::lean_dec(v_unused_1676_);
                                v___x_1664_ = v_a_1648_;
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1648_);
                                v___x_1664_ = crate::leanh::lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1650_ = l_Std_Internal_Parsec_ByteArray_octDigit___closed__1;
                v___x_1651_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1651_, 0, v_a_1648_);
                crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1650_);
                return v___x_1651_;
            }
            2 => {
                v___x_1666_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1667_ = lean_nat_add(v_idx_1653_, v___x_1666_);
                crate::leanh::lean_dec(v_idx_1653_);
                if v_isShared_1665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1664_, 1, v___x_1667_);
                    v_it_x27_1669_ = v___x_1664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_array_1652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1667_);
                    v_it_x27_1669_ = v_reuseFailAlloc_1673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1670_ = lean_uint8_to_uint32(v_c_1658_);
                v___x_1671_ = crate::leanh::lean_box_uint32(v___x_1670_);
                v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1672_, 0, v_it_x27_1669_);
                crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                return v___x_1672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2() -> u8 {
    let mut v___x_1680_: u32 = 0;
    let mut v___x_1681_: u8 = 0;
    v___x_1680_ = 122;
    v___x_1681_ = lean_uint32_to_uint8(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3() -> u8 {
    let mut v___x_1682_: u32 = 0;
    let mut v___x_1683_: u8 = 0;
    v___x_1682_ = 90;
    v___x_1683_ = lean_uint32_to_uint8(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_asciiLetter(
    mut v_a_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1694_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: u32 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1688_ = crate::leanh::lean_ctor_get(v_a_1684_, 0);
                v_idx_1689_ = crate::leanh::lean_ctor_get(v_a_1684_, 1);
                v___x_1690_ = lean_byte_array_size(v_array_1688_);
                v___x_1691_ = lean_nat_dec_lt(v_idx_1689_, v___x_1690_);
                if v___x_1691_ == 0 {
                    v___x_1692_ = crate::leanh::lean_box(0);
                    v___x_1693_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_a_1684_);
                    crate::leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                    return v___x_1693_;
                } else {
                    v_c_1694_ = lean_byte_array_fget(v_array_1688_, v_idx_1689_);
                    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1696_ = lean_nat_add(v_idx_1689_, v___x_1695_);
                    crate::leanh::lean_inc_ref(v_array_1688_);
                    v_it_x27_1697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_it_x27_1697_, 0, v_array_1688_);
                    crate::leanh::lean_ctor_set(v_it_x27_1697_, 1, v___x_1696_);
                    v___x_1707_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2,
                    );
                    v___x_1708_ = lean_uint8_dec_le(v___x_1707_, v_c_1694_);
                    if v___x_1708_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_1709_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3,
                        );
                        v___x_1710_ = lean_uint8_dec_le(v_c_1694_, v___x_1709_);
                        if v___x_1710_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_1684_);
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1686_ = l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1;
                v___x_1687_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1687_, 0, v_a_1684_);
                crate::leanh::lean_ctor_set(v___x_1687_, 1, v___x_1686_);
                return v___x_1687_;
            }
            2 => {
                v___x_1699_ = lean_uint8_to_uint32(v_c_1694_);
                v___x_1700_ = crate::leanh::lean_box_uint32(v___x_1699_);
                v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1701_, 0, v_it_x27_1697_);
                crate::leanh::lean_ctor_set(v___x_1701_, 1, v___x_1700_);
                return v___x_1701_;
            }
            3 => {
                v___x_1703_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once
                    ),
                    _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4,
                );
                v___x_1704_ = lean_uint8_dec_le(v___x_1703_, v_c_1694_);
                if v___x_1704_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_it_x27_1697_, 2);
                    state = 1;
                    continue;
                } else {
                    v___x_1705_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2,
                    );
                    v___x_1706_ = lean_uint8_dec_le(v_c_1694_, v___x_1705_);
                    if v___x_1706_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_it_x27_1697_, 2);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1684_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0()
-> u8 {
    let mut v___x_1711_: u32 = 0;
    let mut v___x_1712_: u8 = 0;
    v___x_1711_ = 9;
    v___x_1712_ = lean_uint32_to_uint8(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1()
-> u8 {
    let mut v___x_1713_: u32 = 0;
    let mut v___x_1714_: u8 = 0;
    v___x_1713_ = 10;
    v___x_1714_ = lean_uint32_to_uint8(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2()
-> u8 {
    let mut v___x_1715_: u32 = 0;
    let mut v___x_1716_: u8 = 0;
    v___x_1715_ = 13;
    v___x_1716_ = lean_uint32_to_uint8(v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3()
-> u8 {
    let mut v___x_1717_: u32 = 0;
    let mut v___x_1718_: u8 = 0;
    v___x_1717_ = 32;
    v___x_1718_ = lean_uint32_to_uint8(v___x_1717_);
    return v___x_1718_;
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(
    mut v_it_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    let mut v_b_1729_: u8 = 0;
    let mut v___x_1730_: u8 = 0;
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1720_ = crate::leanh::lean_ctor_get(v_it_1719_, 0);
                v_idx_1721_ = crate::leanh::lean_ctor_get(v_it_1719_, 1);
                v___x_1727_ = lean_byte_array_size(v_array_1720_);
                v___x_1728_ = lean_nat_dec_lt(v_idx_1721_, v___x_1727_);
                if v___x_1728_ == 0 {
                    return v_it_1719_;
                } else {
                    v_b_1729_ = lean_byte_array_fget(v_array_1720_, v_idx_1721_);
                    v___x_1730_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once), _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0);
                    v___x_1731_ = lean_uint8_dec_eq(v_b_1729_, v___x_1730_);
                    if v___x_1731_ == 0 {
                        v___x_1732_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1), core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once), _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1);
                        v___x_1733_ = lean_uint8_dec_eq(v_b_1729_, v___x_1732_);
                        if v___x_1733_ == 0 {
                            v___x_1734_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2), core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once), _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2);
                            v___x_1735_ = lean_uint8_dec_eq(v_b_1729_, v___x_1734_);
                            if v___x_1735_ == 0 {
                                v___x_1736_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3), core::ptr::addr_of_mut!(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once), _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3);
                                v___x_1737_ = lean_uint8_dec_eq(v_b_1729_, v___x_1736_);
                                if v___x_1737_ == 0 {
                                    return v_it_1719_;
                                } else {
                                    crate::leanh::lean_inc(v_idx_1721_);
                                    crate::leanh::lean_inc_ref(v_array_1720_);
                                    crate::leanh::lean_dec_ref(v_it_1719_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_idx_1721_);
                                crate::leanh::lean_inc_ref(v_array_1720_);
                                crate::leanh::lean_dec_ref(v_it_1719_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_idx_1721_);
                            crate::leanh::lean_inc_ref(v_array_1720_);
                            crate::leanh::lean_dec_ref(v_it_1719_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_idx_1721_);
                        crate::leanh::lean_inc_ref(v_array_1720_);
                        crate::leanh::lean_dec_ref(v_it_1719_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1723_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1724_ = lean_nat_add(v_idx_1721_, v___x_1723_);
                crate::leanh::lean_dec(v_idx_1721_);
                v___x_1725_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1725_, 0, v_array_1720_);
                crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1724_);
                v_it_1719_ = v___x_1725_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_ws(
    mut v_it_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(
        v_it_1738_,
    );
    v___x_1740_ = crate::leanh::lean_box(0);
    v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1741_, 0, v___x_1739_);
    crate::leanh::lean_ctor_set(v___x_1741_, 1, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_take(
    mut v_n_1742_: *mut crate::leanh::LeanObject,
    mut v_it_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: u8 = 0;
    let mut v_array_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ = l_ByteArray_Iterator_remainingBytes(v_it_1743_);
                v___x_1745_ = lean_nat_dec_lt(v___x_1744_, v_n_1742_);
                crate::leanh::lean_dec(v___x_1744_);
                if v___x_1745_ == 0 {
                    v_array_1746_ = crate::leanh::lean_ctor_get(v_it_1743_, 0);
                    v_idx_1747_ = crate::leanh::lean_ctor_get(v_it_1743_, 1);
                    v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_it_1743_)) as u8;
                    if v_isSharedCheck_1766_ == 0 {
                        v___x_1749_ = v_it_1743_;
                        v_isShared_1750_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_1747_);
                        crate::leanh::lean_inc(v_array_1746_);
                        crate::leanh::lean_dec(v_it_1743_);
                        v___x_1749_ = crate::leanh::lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1767_ = crate::leanh::lean_box(0);
                    v___x_1768_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1768_, 0, v_it_1743_);
                    crate::leanh::lean_ctor_set(v___x_1768_, 1, v___x_1767_);
                    return v___x_1768_;
                }
            }
            1 => {
                v___x_1751_ = lean_nat_add(v_idx_1747_, v_n_1742_);
                crate::leanh::lean_inc(v___x_1751_);
                crate::leanh::lean_inc_ref(v_array_1746_);
                if v_isShared_1750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1749_, 1, v___x_1751_);
                    v___x_1753_ = v___x_1749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_array_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1751_);
                    v___x_1753_ = v_reuseFailAlloc_1765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1759_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1760_ = lean_byte_array_size(v_array_1746_);
                v___x_1764_ = lean_nat_dec_le(v_idx_1747_, v___x_1759_);
                if v___x_1764_ == 0 {
                    v___y_1762_ = v_idx_1747_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_1747_);
                    v___y_1762_ = v___x_1759_;
                    state = 4;
                    continue;
                }
            }
            3 => {
                v___x_1757_ = l_ByteArray_toByteSlice(v_array_1746_, v_lower_1755_, v_upper_1756_);
                v___x_1758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1758_, 1, v___x_1757_);
                return v___x_1758_;
            }
            4 => {
                v___x_1763_ = lean_nat_dec_le(v___x_1751_, v___x_1760_);
                if v___x_1763_ == 0 {
                    crate::leanh::lean_dec(v___x_1751_);
                    v_lower_1755_ = v___y_1762_;
                    v_upper_1756_ = v___x_1760_;
                    state = 3;
                    continue;
                } else {
                    v_lower_1755_ = v___y_1762_;
                    v_upper_1756_ = v___x_1751_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_take___boxed(
    mut v_n_1769_: *mut crate::leanh::LeanObject,
    mut v_it_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Std_Internal_Parsec_ByteArray_take(v_n_1769_, v_it_1770_);
    crate::leanh::lean_dec(v_n_1769_);
    return v_res_1771_;
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(
    mut v_pred_1772_: *mut crate::leanh::LeanObject,
    mut v_count_1773_: *mut crate::leanh::LeanObject,
    mut v_iter_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut v_unused_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1775_ = crate::leanh::lean_ctor_get(v_iter_1774_, 0);
                v_idx_1776_ = crate::leanh::lean_ctor_get(v_iter_1774_, 1);
                v___x_1777_ = lean_byte_array_size(v_array_1775_);
                v___x_1778_ = lean_nat_dec_lt(v_idx_1776_, v___x_1777_);
                if v___x_1778_ == 0 {
                    crate::leanh::lean_dec_ref(v_pred_1772_);
                    v___x_1779_ = 1;
                    v___x_1780_ = crate::leanh::lean_box((v___x_1779_) as usize);
                    v___x_1781_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1781_, 0, v_iter_1774_);
                    crate::leanh::lean_ctor_set(v___x_1781_, 1, v___x_1780_);
                    v___x_1782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1782_, 0, v_count_1773_);
                    crate::leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
                    return v___x_1782_;
                } else {
                    v___x_1783_ = lean_byte_array_fget(v_array_1775_, v_idx_1776_);
                    v___x_1784_ = crate::leanh::lean_box((v___x_1783_) as usize);
                    crate::leanh::lean_inc_ref(v_pred_1772_);
                    v___x_1785_ = crate::leanh::lean_apply_1(v_pred_1772_, v___x_1784_);
                    v___x_1786_ = (crate::leanh::lean_unbox(v___x_1785_) as u8);
                    if v___x_1786_ == 0 {
                        crate::leanh::lean_dec_ref(v_pred_1772_);
                        v___x_1787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1787_, 0, v_iter_1774_);
                        crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1785_);
                        v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1788_, 0, v_count_1773_);
                        crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                        return v___x_1788_;
                    } else {
                        crate::leanh::lean_inc(v_idx_1776_);
                        crate::leanh::lean_inc_ref(v_array_1775_);
                        v_isSharedCheck_1799_ =
                            (!crate::leanh::lean_is_exclusive(v_iter_1774_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v_unused_1800_ = crate::leanh::lean_ctor_get(v_iter_1774_, 1);
                            crate::leanh::lean_dec(v_unused_1800_);
                            v_unused_1801_ = crate::leanh::lean_ctor_get(v_iter_1774_, 0);
                            crate::leanh::lean_dec(v_unused_1801_);
                            v___x_1790_ = v_iter_1774_;
                            v_isShared_1791_ = v_isSharedCheck_1799_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_iter_1774_);
                            v___x_1790_ = crate::leanh::lean_box(0);
                            v_isShared_1791_ = v_isSharedCheck_1799_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1792_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1793_ = lean_nat_add(v_count_1773_, v___x_1792_);
                crate::leanh::lean_dec(v_count_1773_);
                v___x_1794_ = lean_nat_add(v_idx_1776_, v___x_1792_);
                crate::leanh::lean_dec(v_idx_1776_);
                if v_isShared_1791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1790_, 1, v___x_1794_);
                    v___x_1796_ = v___x_1790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_array_1775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___x_1794_);
                    v___x_1796_ = v_reuseFailAlloc_1798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_count_1773_ = v___x_1793_;
                v_iter_1774_ = v___x_1796_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(
    mut v_pred_1802_: *mut crate::leanh::LeanObject,
    mut v_limit_1803_: *mut crate::leanh::LeanObject,
    mut v_count_1804_: *mut crate::leanh::LeanObject,
    mut v_iter_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: u8 = 0;
    let mut v_array_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v_unused_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1806_ = lean_nat_dec_le(v_limit_1803_, v_count_1804_);
                if v___x_1806_ == 0 {
                    v_array_1807_ = crate::leanh::lean_ctor_get(v_iter_1805_, 0);
                    v_idx_1808_ = crate::leanh::lean_ctor_get(v_iter_1805_, 1);
                    v___x_1809_ = lean_byte_array_size(v_array_1807_);
                    v___x_1810_ = lean_nat_dec_lt(v_idx_1808_, v___x_1809_);
                    if v___x_1810_ == 0 {
                        crate::leanh::lean_dec_ref(v_pred_1802_);
                        v___x_1811_ = 1;
                        v___x_1812_ = crate::leanh::lean_box((v___x_1811_) as usize);
                        v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1813_, 0, v_iter_1805_);
                        crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1812_);
                        v___x_1814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1814_, 0, v_count_1804_);
                        crate::leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                        return v___x_1814_;
                    } else {
                        v___x_1815_ = lean_byte_array_fget(v_array_1807_, v_idx_1808_);
                        v___x_1816_ = crate::leanh::lean_box((v___x_1815_) as usize);
                        crate::leanh::lean_inc_ref(v_pred_1802_);
                        v___x_1817_ = crate::leanh::lean_apply_1(v_pred_1802_, v___x_1816_);
                        v___x_1818_ = (crate::leanh::lean_unbox(v___x_1817_) as u8);
                        if v___x_1818_ == 0 {
                            crate::leanh::lean_dec_ref(v_pred_1802_);
                            v___x_1819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1819_, 0, v_iter_1805_);
                            crate::leanh::lean_ctor_set(v___x_1819_, 1, v___x_1817_);
                            v___x_1820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1820_, 0, v_count_1804_);
                            crate::leanh::lean_ctor_set(v___x_1820_, 1, v___x_1819_);
                            return v___x_1820_;
                        } else {
                            crate::leanh::lean_inc(v_idx_1808_);
                            crate::leanh::lean_inc_ref(v_array_1807_);
                            v_isSharedCheck_1831_ =
                                (!crate::leanh::lean_is_exclusive(v_iter_1805_)) as u8;
                            if v_isSharedCheck_1831_ == 0 {
                                v_unused_1832_ = crate::leanh::lean_ctor_get(v_iter_1805_, 1);
                                crate::leanh::lean_dec(v_unused_1832_);
                                v_unused_1833_ = crate::leanh::lean_ctor_get(v_iter_1805_, 0);
                                crate::leanh::lean_dec(v_unused_1833_);
                                v___x_1822_ = v_iter_1805_;
                                v_isShared_1823_ = v_isSharedCheck_1831_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_iter_1805_);
                                v___x_1822_ = crate::leanh::lean_box(0);
                                v_isShared_1823_ = v_isSharedCheck_1831_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pred_1802_);
                    v___x_1834_ = 0;
                    v___x_1835_ = crate::leanh::lean_box((v___x_1834_) as usize);
                    v___x_1836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1836_, 0, v_iter_1805_);
                    crate::leanh::lean_ctor_set(v___x_1836_, 1, v___x_1835_);
                    v___x_1837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1837_, 0, v_count_1804_);
                    crate::leanh::lean_ctor_set(v___x_1837_, 1, v___x_1836_);
                    return v___x_1837_;
                }
            }
            1 => {
                v___x_1824_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1825_ = lean_nat_add(v_count_1804_, v___x_1824_);
                crate::leanh::lean_dec(v_count_1804_);
                v___x_1826_ = lean_nat_add(v_idx_1808_, v___x_1824_);
                crate::leanh::lean_dec(v_idx_1808_);
                if v_isShared_1823_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1822_, 1, v___x_1826_);
                    v___x_1828_ = v___x_1822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_array_1807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1826_);
                    v___x_1828_ = v_reuseFailAlloc_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_count_1804_ = v___x_1825_;
                v_iter_1805_ = v___x_1828_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(
    mut v_pred_1838_: *mut crate::leanh::LeanObject,
    mut v_limit_1839_: *mut crate::leanh::LeanObject,
    mut v_count_1840_: *mut crate::leanh::LeanObject,
    mut v_iter_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ =
        l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(
            v_pred_1838_,
            v_limit_1839_,
            v_count_1840_,
            v_iter_1841_,
        );
    crate::leanh::lean_dec(v_limit_1839_);
    return v_res_1842_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhile(
    mut v_pred_1843_: *mut crate::leanh::LeanObject,
    mut v_it_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: u8 = 0;
    let mut v_fst_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v_lower_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: u8 = 0;
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_fst_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_unused_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1845_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_it_1844_);
                v___x_1846_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_1843_, v___x_1845_, v_it_1844_);
                v_snd_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 1);
                crate::leanh::lean_inc(v_snd_1847_);
                v_snd_1848_ = crate::leanh::lean_ctor_get(v_snd_1847_, 1);
                v___x_1849_ = (crate::leanh::lean_unbox(v_snd_1848_) as u8);
                if v___x_1849_ == 0 {
                    v_fst_1850_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                    crate::leanh::lean_inc(v_fst_1850_);
                    crate::leanh::lean_dec_ref(v___x_1846_);
                    v_fst_1851_ = crate::leanh::lean_ctor_get(v_snd_1847_, 0);
                    crate::leanh::lean_inc(v_fst_1851_);
                    crate::leanh::lean_dec(v_snd_1847_);
                    v_array_1852_ = crate::leanh::lean_ctor_get(v_it_1844_, 0);
                    v_idx_1853_ = crate::leanh::lean_ctor_get(v_it_1844_, 1);
                    v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v_it_1844_)) as u8;
                    if v_isSharedCheck_1870_ == 0 {
                        v___x_1855_ = v_it_1844_;
                        v_isShared_1856_ = v_isSharedCheck_1870_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_1853_);
                        crate::leanh::lean_inc(v_array_1852_);
                        crate::leanh::lean_dec(v_it_1844_);
                        v___x_1855_ = crate::leanh::lean_box(0);
                        v_isShared_1856_ = v_isSharedCheck_1870_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1846_);
                    crate::leanh::lean_dec_ref(v_it_1844_);
                    v_fst_1871_ = crate::leanh::lean_ctor_get(v_snd_1847_, 0);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v_snd_1847_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v_unused_1880_ = crate::leanh::lean_ctor_get(v_snd_1847_, 1);
                        crate::leanh::lean_dec(v_unused_1880_);
                        v___x_1873_ = v_snd_1847_;
                        v_isShared_1874_ = v_isSharedCheck_1879_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1871_);
                        crate::leanh::lean_dec(v_snd_1847_);
                        v___x_1873_ = crate::leanh::lean_box(0);
                        v_isShared_1874_ = v_isSharedCheck_1879_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1864_ = lean_nat_add(v_idx_1853_, v_fst_1850_);
                crate::leanh::lean_dec(v_fst_1850_);
                v___x_1865_ = lean_byte_array_size(v_array_1852_);
                v___x_1869_ = lean_nat_dec_le(v_idx_1853_, v___x_1845_);
                if v___x_1869_ == 0 {
                    v___y_1867_ = v_idx_1853_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_1853_);
                    v___y_1867_ = v___x_1845_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1860_ = l_ByteArray_toByteSlice(v_array_1852_, v_lower_1858_, v_upper_1859_);
                if v_isShared_1856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1855_, 1, v___x_1860_);
                    crate::leanh::lean_ctor_set(v___x_1855_, 0, v_fst_1851_);
                    v___x_1862_ = v___x_1855_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_fst_1851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___x_1860_);
                    v___x_1862_ = v_reuseFailAlloc_1863_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1862_;
            }
            4 => {
                v___x_1868_ = lean_nat_dec_le(v___x_1864_, v___x_1865_);
                if v___x_1868_ == 0 {
                    crate::leanh::lean_dec(v___x_1864_);
                    v_lower_1858_ = v___y_1867_;
                    v_upper_1859_ = v___x_1865_;
                    state = 2;
                    continue;
                } else {
                    v_lower_1858_ = v___y_1867_;
                    v_upper_1859_ = v___x_1864_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1875_ = crate::leanh::lean_box(0);
                if v_isShared_1874_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1873_, 1);
                    crate::leanh::lean_ctor_set(v___x_1873_, 1, v___x_1875_);
                    v___x_1877_ = v___x_1873_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_fst_1871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1875_);
                    v___x_1877_ = v_reuseFailAlloc_1878_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(
    mut v_pred_1881_: *mut crate::leanh::LeanObject,
    mut v_b_1882_: u8,
) -> u8 {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    v___x_1883_ = crate::leanh::lean_box((v_b_1882_) as usize);
    v___x_1884_ = crate::leanh::lean_apply_1(v_pred_1881_, v___x_1883_);
    v___x_1885_ = (crate::leanh::lean_unbox(v___x_1884_) as u8);
    if v___x_1885_ == 0 {
        let mut v___x_1886_: u8 = 0;
        v___x_1886_ = 1;
        return v___x_1886_;
    } else {
        let mut v___x_1887_: u8 = 0;
        v___x_1887_ = 0;
        return v___x_1887_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(
    mut v_pred_1888_: *mut crate::leanh::LeanObject,
    mut v_b_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1890_: u8 = 0;
    let mut v_res_1891_: u8 = 0;
    let mut v_r_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1890_ = (crate::leanh::lean_unbox(v_b_1889_) as u8);
    v_res_1891_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_1888_, v_b_boxed_1890_);
    v_r_1892_ = crate::leanh::lean_box((v_res_1891_) as usize);
    return v_r_1892_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeUntil(
    mut v_pred_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v_fst_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v_lower_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: u8 = 0;
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_fst_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_unused_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1895_ = crate::leanh::lean_alloc_closure(
                    l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1895_, 0, v_pred_1893_);
                v___x_1896_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_1894_);
                v___x_1897_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_1895_, v___x_1896_, v_a_1894_);
                v_snd_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 1);
                crate::leanh::lean_inc(v_snd_1898_);
                v_snd_1899_ = crate::leanh::lean_ctor_get(v_snd_1898_, 1);
                v___x_1900_ = (crate::leanh::lean_unbox(v_snd_1899_) as u8);
                if v___x_1900_ == 0 {
                    v_fst_1901_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                    crate::leanh::lean_inc(v_fst_1901_);
                    crate::leanh::lean_dec_ref(v___x_1897_);
                    v_fst_1902_ = crate::leanh::lean_ctor_get(v_snd_1898_, 0);
                    crate::leanh::lean_inc(v_fst_1902_);
                    crate::leanh::lean_dec(v_snd_1898_);
                    v_array_1903_ = crate::leanh::lean_ctor_get(v_a_1894_, 0);
                    v_idx_1904_ = crate::leanh::lean_ctor_get(v_a_1894_, 1);
                    v_isSharedCheck_1921_ = (!crate::leanh::lean_is_exclusive(v_a_1894_)) as u8;
                    if v_isSharedCheck_1921_ == 0 {
                        v___x_1906_ = v_a_1894_;
                        v_isShared_1907_ = v_isSharedCheck_1921_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_1904_);
                        crate::leanh::lean_inc(v_array_1903_);
                        crate::leanh::lean_dec(v_a_1894_);
                        v___x_1906_ = crate::leanh::lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1921_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1897_);
                    crate::leanh::lean_dec_ref(v_a_1894_);
                    v_fst_1922_ = crate::leanh::lean_ctor_get(v_snd_1898_, 0);
                    v_isSharedCheck_1930_ = (!crate::leanh::lean_is_exclusive(v_snd_1898_)) as u8;
                    if v_isSharedCheck_1930_ == 0 {
                        v_unused_1931_ = crate::leanh::lean_ctor_get(v_snd_1898_, 1);
                        crate::leanh::lean_dec(v_unused_1931_);
                        v___x_1924_ = v_snd_1898_;
                        v_isShared_1925_ = v_isSharedCheck_1930_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1922_);
                        crate::leanh::lean_dec(v_snd_1898_);
                        v___x_1924_ = crate::leanh::lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1930_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1915_ = lean_nat_add(v_idx_1904_, v_fst_1901_);
                crate::leanh::lean_dec(v_fst_1901_);
                v___x_1916_ = lean_byte_array_size(v_array_1903_);
                v___x_1920_ = lean_nat_dec_le(v_idx_1904_, v___x_1896_);
                if v___x_1920_ == 0 {
                    v___y_1918_ = v_idx_1904_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_1904_);
                    v___y_1918_ = v___x_1896_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1911_ = l_ByteArray_toByteSlice(v_array_1903_, v_lower_1909_, v_upper_1910_);
                if v_isShared_1907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1911_);
                    crate::leanh::lean_ctor_set(v___x_1906_, 0, v_fst_1902_);
                    v___x_1913_ = v___x_1906_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_fst_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1911_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1913_;
            }
            4 => {
                v___x_1919_ = lean_nat_dec_le(v___x_1915_, v___x_1916_);
                if v___x_1919_ == 0 {
                    crate::leanh::lean_dec(v___x_1915_);
                    v_lower_1909_ = v___y_1918_;
                    v_upper_1910_ = v___x_1916_;
                    state = 2;
                    continue;
                } else {
                    v_lower_1909_ = v___y_1918_;
                    v_upper_1910_ = v___x_1915_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1926_ = crate::leanh::lean_box(0);
                if v_isShared_1925_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1924_, 1);
                    crate::leanh::lean_ctor_set(v___x_1924_, 1, v___x_1926_);
                    v___x_1928_ = v___x_1924_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_fst_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1926_);
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipWhile(
    mut v_pred_1932_: *mut crate::leanh::LeanObject,
    mut v_it_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v_fst_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_unused_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_unused_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1934_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1935_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_1932_, v___x_1934_, v_it_1933_);
                v_snd_1936_ = crate::leanh::lean_ctor_get(v___x_1935_, 1);
                crate::leanh::lean_inc(v_snd_1936_);
                crate::leanh::lean_dec_ref(v___x_1935_);
                v_snd_1937_ = crate::leanh::lean_ctor_get(v_snd_1936_, 1);
                v___x_1938_ = (crate::leanh::lean_unbox(v_snd_1937_) as u8);
                if v___x_1938_ == 0 {
                    v_fst_1939_ = crate::leanh::lean_ctor_get(v_snd_1936_, 0);
                    v_isSharedCheck_1947_ = (!crate::leanh::lean_is_exclusive(v_snd_1936_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v_unused_1948_ = crate::leanh::lean_ctor_get(v_snd_1936_, 1);
                        crate::leanh::lean_dec(v_unused_1948_);
                        v___x_1941_ = v_snd_1936_;
                        v_isShared_1942_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1939_);
                        crate::leanh::lean_dec(v_snd_1936_);
                        v___x_1941_ = crate::leanh::lean_box(0);
                        v_isShared_1942_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_1949_ = crate::leanh::lean_ctor_get(v_snd_1936_, 0);
                    v_isSharedCheck_1957_ = (!crate::leanh::lean_is_exclusive(v_snd_1936_)) as u8;
                    if v_isSharedCheck_1957_ == 0 {
                        v_unused_1958_ = crate::leanh::lean_ctor_get(v_snd_1936_, 1);
                        crate::leanh::lean_dec(v_unused_1958_);
                        v___x_1951_ = v_snd_1936_;
                        v_isShared_1952_ = v_isSharedCheck_1957_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1949_);
                        crate::leanh::lean_dec(v_snd_1936_);
                        v___x_1951_ = crate::leanh::lean_box(0);
                        v_isShared_1952_ = v_isSharedCheck_1957_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1943_ = crate::leanh::lean_box(0);
                if v_isShared_1942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1941_, 1, v___x_1943_);
                    v___x_1945_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_fst_1939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1943_);
                    v___x_1945_ = v_reuseFailAlloc_1946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1945_;
            }
            3 => {
                v___x_1953_ = crate::leanh::lean_box(0);
                if v_isShared_1952_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1951_, 1);
                    crate::leanh::lean_ctor_set(v___x_1951_, 1, v___x_1953_);
                    v___x_1955_ = v___x_1951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fst_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1953_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipUntil(
    mut v_pred_1959_: *mut crate::leanh::LeanObject,
    mut v_a_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u8 = 0;
    let mut v_fst_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_unused_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_unused_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1961_ = crate::leanh::lean_alloc_closure(
                    l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1961_, 0, v_pred_1959_);
                v___x_1962_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1963_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_1961_, v___x_1962_, v_a_1960_);
                v_snd_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                crate::leanh::lean_inc(v_snd_1964_);
                crate::leanh::lean_dec_ref(v___x_1963_);
                v_snd_1965_ = crate::leanh::lean_ctor_get(v_snd_1964_, 1);
                v___x_1966_ = (crate::leanh::lean_unbox(v_snd_1965_) as u8);
                if v___x_1966_ == 0 {
                    v_fst_1967_ = crate::leanh::lean_ctor_get(v_snd_1964_, 0);
                    v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v_snd_1964_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v_unused_1976_ = crate::leanh::lean_ctor_get(v_snd_1964_, 1);
                        crate::leanh::lean_dec(v_unused_1976_);
                        v___x_1969_ = v_snd_1964_;
                        v_isShared_1970_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1967_);
                        crate::leanh::lean_dec(v_snd_1964_);
                        v___x_1969_ = crate::leanh::lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_1977_ = crate::leanh::lean_ctor_get(v_snd_1964_, 0);
                    v_isSharedCheck_1985_ = (!crate::leanh::lean_is_exclusive(v_snd_1964_)) as u8;
                    if v_isSharedCheck_1985_ == 0 {
                        v_unused_1986_ = crate::leanh::lean_ctor_get(v_snd_1964_, 1);
                        crate::leanh::lean_dec(v_unused_1986_);
                        v___x_1979_ = v_snd_1964_;
                        v_isShared_1980_ = v_isSharedCheck_1985_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1977_);
                        crate::leanh::lean_dec(v_snd_1964_);
                        v___x_1979_ = crate::leanh::lean_box(0);
                        v_isShared_1980_ = v_isSharedCheck_1985_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1971_ = crate::leanh::lean_box(0);
                if v_isShared_1970_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1969_, 1, v___x_1971_);
                    v___x_1973_ = v___x_1969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_fst_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1971_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1973_;
            }
            3 => {
                v___x_1981_ = crate::leanh::lean_box(0);
                if v_isShared_1980_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1979_, 1);
                    crate::leanh::lean_ctor_set(v___x_1979_, 1, v___x_1981_);
                    v___x_1983_ = v___x_1979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1984_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_fst_1977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___x_1981_);
                    v___x_1983_ = v_reuseFailAlloc_1984_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(
    mut v_pred_1987_: *mut crate::leanh::LeanObject,
    mut v_limit_1988_: *mut crate::leanh::LeanObject,
    mut v_it_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: u8 = 0;
    let mut v_fst_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v_lower_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_fst_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_unused_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1990_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_it_1989_);
                v___x_1991_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1987_, v_limit_1988_, v___x_1990_, v_it_1989_);
                v_snd_1992_ = crate::leanh::lean_ctor_get(v___x_1991_, 1);
                crate::leanh::lean_inc(v_snd_1992_);
                v_snd_1993_ = crate::leanh::lean_ctor_get(v_snd_1992_, 1);
                v___x_1994_ = (crate::leanh::lean_unbox(v_snd_1993_) as u8);
                if v___x_1994_ == 0 {
                    v_fst_1995_ = crate::leanh::lean_ctor_get(v___x_1991_, 0);
                    crate::leanh::lean_inc(v_fst_1995_);
                    crate::leanh::lean_dec_ref(v___x_1991_);
                    v_fst_1996_ = crate::leanh::lean_ctor_get(v_snd_1992_, 0);
                    crate::leanh::lean_inc(v_fst_1996_);
                    crate::leanh::lean_dec(v_snd_1992_);
                    v_array_1997_ = crate::leanh::lean_ctor_get(v_it_1989_, 0);
                    v_idx_1998_ = crate::leanh::lean_ctor_get(v_it_1989_, 1);
                    v_isSharedCheck_2015_ = (!crate::leanh::lean_is_exclusive(v_it_1989_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v___x_2000_ = v_it_1989_;
                        v_isShared_2001_ = v_isSharedCheck_2015_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_1998_);
                        crate::leanh::lean_inc(v_array_1997_);
                        crate::leanh::lean_dec(v_it_1989_);
                        v___x_2000_ = crate::leanh::lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2015_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1991_);
                    crate::leanh::lean_dec_ref(v_it_1989_);
                    v_fst_2016_ = crate::leanh::lean_ctor_get(v_snd_1992_, 0);
                    v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v_snd_1992_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v_unused_2025_ = crate::leanh::lean_ctor_get(v_snd_1992_, 1);
                        crate::leanh::lean_dec(v_unused_2025_);
                        v___x_2018_ = v_snd_1992_;
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2016_);
                        crate::leanh::lean_dec(v_snd_1992_);
                        v___x_2018_ = crate::leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2009_ = lean_nat_add(v_idx_1998_, v_fst_1995_);
                crate::leanh::lean_dec(v_fst_1995_);
                v___x_2010_ = lean_byte_array_size(v_array_1997_);
                v___x_2014_ = lean_nat_dec_le(v_idx_1998_, v___x_1990_);
                if v___x_2014_ == 0 {
                    v___y_2012_ = v_idx_1998_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_1998_);
                    v___y_2012_ = v___x_1990_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2005_ = l_ByteArray_toByteSlice(v_array_1997_, v_lower_2003_, v_upper_2004_);
                if v_isShared_2001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2000_, 1, v___x_2005_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 0, v_fst_1996_);
                    v___x_2007_ = v___x_2000_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fst_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_2005_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2007_;
            }
            4 => {
                v___x_2013_ = lean_nat_dec_le(v___x_2009_, v___x_2010_);
                if v___x_2013_ == 0 {
                    crate::leanh::lean_dec(v___x_2009_);
                    v_lower_2003_ = v___y_2012_;
                    v_upper_2004_ = v___x_2010_;
                    state = 2;
                    continue;
                } else {
                    v_lower_2003_ = v___y_2012_;
                    v_upper_2004_ = v___x_2009_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2020_ = crate::leanh::lean_box(0);
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2018_, 1);
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v___x_2020_);
                    v___x_2022_ = v___x_2018_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_fst_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2020_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(
    mut v_pred_2026_: *mut crate::leanh::LeanObject,
    mut v_limit_2027_: *mut crate::leanh::LeanObject,
    mut v_it_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ =
        l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_2026_, v_limit_2027_, v_it_2028_);
    crate::leanh::lean_dec(v_limit_2027_);
    return v_res_2029_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(
    mut v_pred_2033_: *mut crate::leanh::LeanObject,
    mut v_limit_2034_: *mut crate::leanh::LeanObject,
    mut v_it_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v_fst_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2046_: u8 = 0;
    let mut v_array_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v_lower_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: u8 = 0;
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2036_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_it_2035_);
                v___x_2037_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_2033_, v_limit_2034_, v___x_2036_, v_it_2035_);
                v_snd_2038_ = crate::leanh::lean_ctor_get(v___x_2037_, 1);
                crate::leanh::lean_inc(v_snd_2038_);
                v_snd_2039_ = crate::leanh::lean_ctor_get(v_snd_2038_, 1);
                v___x_2040_ = (crate::leanh::lean_unbox(v_snd_2039_) as u8);
                if v___x_2040_ == 0 {
                    v_fst_2041_ = crate::leanh::lean_ctor_get(v___x_2037_, 0);
                    crate::leanh::lean_inc(v_fst_2041_);
                    crate::leanh::lean_dec_ref(v___x_2037_);
                    v_fst_2042_ = crate::leanh::lean_ctor_get(v_snd_2038_, 0);
                    v_isSharedCheck_2070_ = (!crate::leanh::lean_is_exclusive(v_snd_2038_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v_unused_2071_ = crate::leanh::lean_ctor_get(v_snd_2038_, 1);
                        crate::leanh::lean_dec(v_unused_2071_);
                        v___x_2044_ = v_snd_2038_;
                        v_isShared_2045_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2042_);
                        crate::leanh::lean_dec(v_snd_2038_);
                        v___x_2044_ = crate::leanh::lean_box(0);
                        v_isShared_2045_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2037_);
                    crate::leanh::lean_dec_ref(v_it_2035_);
                    v_fst_2072_ = crate::leanh::lean_ctor_get(v_snd_2038_, 0);
                    v_isSharedCheck_2080_ = (!crate::leanh::lean_is_exclusive(v_snd_2038_)) as u8;
                    if v_isSharedCheck_2080_ == 0 {
                        v_unused_2081_ = crate::leanh::lean_ctor_get(v_snd_2038_, 1);
                        crate::leanh::lean_dec(v_unused_2081_);
                        v___x_2074_ = v_snd_2038_;
                        v_isShared_2075_ = v_isSharedCheck_2080_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2072_);
                        crate::leanh::lean_dec(v_snd_2038_);
                        v___x_2074_ = crate::leanh::lean_box(0);
                        v_isShared_2075_ = v_isSharedCheck_2080_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2046_ = lean_nat_dec_eq(v_fst_2041_, v___x_2036_);
                if v___x_2046_ == 0 {
                    crate::leanh::lean_del_object(v___x_2044_);
                    v_array_2047_ = crate::leanh::lean_ctor_get(v_it_2035_, 0);
                    v_idx_2048_ = crate::leanh::lean_ctor_get(v_it_2035_, 1);
                    v_isSharedCheck_2065_ = (!crate::leanh::lean_is_exclusive(v_it_2035_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2050_ = v_it_2035_;
                        v_isShared_2051_ = v_isSharedCheck_2065_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_2048_);
                        crate::leanh::lean_inc(v_array_2047_);
                        crate::leanh::lean_dec(v_it_2035_);
                        v___x_2050_ = crate::leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2065_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2042_);
                    crate::leanh::lean_dec(v_fst_2041_);
                    v___x_2066_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1;
                    if v_isShared_2045_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2044_, 1);
                        crate::leanh::lean_ctor_set(v___x_2044_, 1, v___x_2066_);
                        crate::leanh::lean_ctor_set(v___x_2044_, 0, v_it_2035_);
                        v___x_2068_ = v___x_2044_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_it_2035_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2066_);
                        v___x_2068_ = v_reuseFailAlloc_2069_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2059_ = lean_nat_add(v_idx_2048_, v_fst_2041_);
                crate::leanh::lean_dec(v_fst_2041_);
                v___x_2060_ = lean_byte_array_size(v_array_2047_);
                v___x_2064_ = lean_nat_dec_le(v_idx_2048_, v___x_2036_);
                if v___x_2064_ == 0 {
                    v___y_2062_ = v_idx_2048_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_2048_);
                    v___y_2062_ = v___x_2036_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_2055_ = l_ByteArray_toByteSlice(v_array_2047_, v_lower_2053_, v_upper_2054_);
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 1, v___x_2055_);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v_fst_2042_);
                    v___x_2057_ = v___x_2050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_fst_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2055_);
                    v___x_2057_ = v_reuseFailAlloc_2058_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2057_;
            }
            5 => {
                v___x_2063_ = lean_nat_dec_le(v___x_2059_, v___x_2060_);
                if v___x_2063_ == 0 {
                    crate::leanh::lean_dec(v___x_2059_);
                    v_lower_2053_ = v___y_2062_;
                    v_upper_2054_ = v___x_2060_;
                    state = 3;
                    continue;
                } else {
                    v_lower_2053_ = v___y_2062_;
                    v_upper_2054_ = v___x_2059_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                return v___x_2068_;
            }
            7 => {
                v___x_2076_ = crate::leanh::lean_box(0);
                if v_isShared_2075_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2074_, 1);
                    crate::leanh::lean_ctor_set(v___x_2074_, 1, v___x_2076_);
                    v___x_2078_ = v___x_2074_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_fst_2072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
                    v___x_2078_ = v_reuseFailAlloc_2079_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(
    mut v_pred_2082_: *mut crate::leanh::LeanObject,
    mut v_limit_2083_: *mut crate::leanh::LeanObject,
    mut v_it_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ =
        l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_2082_, v_limit_2083_, v_it_2084_);
    crate::leanh::lean_dec(v_limit_2083_);
    return v_res_2085_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(
    mut v_pred_2086_: *mut crate::leanh::LeanObject,
    mut v_limit_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v_fst_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v_lower_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: u8 = 0;
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v_fst_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_unused_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2089_ = crate::leanh::lean_alloc_closure(
                    l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2089_, 0, v_pred_2086_);
                v___x_2090_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_a_2088_);
                v___x_2091_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2089_, v_limit_2087_, v___x_2090_, v_a_2088_);
                v_snd_2092_ = crate::leanh::lean_ctor_get(v___x_2091_, 1);
                crate::leanh::lean_inc(v_snd_2092_);
                v_snd_2093_ = crate::leanh::lean_ctor_get(v_snd_2092_, 1);
                v___x_2094_ = (crate::leanh::lean_unbox(v_snd_2093_) as u8);
                if v___x_2094_ == 0 {
                    v_fst_2095_ = crate::leanh::lean_ctor_get(v___x_2091_, 0);
                    crate::leanh::lean_inc(v_fst_2095_);
                    crate::leanh::lean_dec_ref(v___x_2091_);
                    v_fst_2096_ = crate::leanh::lean_ctor_get(v_snd_2092_, 0);
                    crate::leanh::lean_inc(v_fst_2096_);
                    crate::leanh::lean_dec(v_snd_2092_);
                    v_array_2097_ = crate::leanh::lean_ctor_get(v_a_2088_, 0);
                    v_idx_2098_ = crate::leanh::lean_ctor_get(v_a_2088_, 1);
                    v_isSharedCheck_2115_ = (!crate::leanh::lean_is_exclusive(v_a_2088_)) as u8;
                    if v_isSharedCheck_2115_ == 0 {
                        v___x_2100_ = v_a_2088_;
                        v_isShared_2101_ = v_isSharedCheck_2115_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_2098_);
                        crate::leanh::lean_inc(v_array_2097_);
                        crate::leanh::lean_dec(v_a_2088_);
                        v___x_2100_ = crate::leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2115_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2091_);
                    crate::leanh::lean_dec_ref(v_a_2088_);
                    v_fst_2116_ = crate::leanh::lean_ctor_get(v_snd_2092_, 0);
                    v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v_snd_2092_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v_unused_2125_ = crate::leanh::lean_ctor_get(v_snd_2092_, 1);
                        crate::leanh::lean_dec(v_unused_2125_);
                        v___x_2118_ = v_snd_2092_;
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2116_);
                        crate::leanh::lean_dec(v_snd_2092_);
                        v___x_2118_ = crate::leanh::lean_box(0);
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2109_ = lean_nat_add(v_idx_2098_, v_fst_2095_);
                crate::leanh::lean_dec(v_fst_2095_);
                v___x_2110_ = lean_byte_array_size(v_array_2097_);
                v___x_2114_ = lean_nat_dec_le(v_idx_2098_, v___x_2090_);
                if v___x_2114_ == 0 {
                    v___y_2112_ = v_idx_2098_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_2098_);
                    v___y_2112_ = v___x_2090_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2105_ = l_ByteArray_toByteSlice(v_array_2097_, v_lower_2103_, v_upper_2104_);
                if v_isShared_2101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2100_, 1, v___x_2105_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 0, v_fst_2096_);
                    v___x_2107_ = v___x_2100_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2105_);
                    v___x_2107_ = v_reuseFailAlloc_2108_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2107_;
            }
            4 => {
                v___x_2113_ = lean_nat_dec_le(v___x_2109_, v___x_2110_);
                if v___x_2113_ == 0 {
                    crate::leanh::lean_dec(v___x_2109_);
                    v_lower_2103_ = v___y_2112_;
                    v_upper_2104_ = v___x_2110_;
                    state = 2;
                    continue;
                } else {
                    v_lower_2103_ = v___y_2112_;
                    v_upper_2104_ = v___x_2109_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2120_ = crate::leanh::lean_box(0);
                if v_isShared_2119_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2118_, 1);
                    crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2120_);
                    v___x_2122_ = v___x_2118_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_fst_2116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2123_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(
    mut v_pred_2126_: *mut crate::leanh::LeanObject,
    mut v_limit_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2129_ =
        l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_2126_, v_limit_2127_, v_a_2128_);
    crate::leanh::lean_dec(v_limit_2127_);
    return v_res_2129_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(
    mut v_pred_2130_: *mut crate::leanh::LeanObject,
    mut v_limit_2131_: *mut crate::leanh::LeanObject,
    mut v_it_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v_lower_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: u8 = 0;
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2133_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_it_2132_);
                v___x_2134_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_2130_, v_limit_2131_, v___x_2133_, v_it_2132_);
                v_snd_2135_ = crate::leanh::lean_ctor_get(v___x_2134_, 1);
                crate::leanh::lean_inc(v_snd_2135_);
                v_fst_2136_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                crate::leanh::lean_inc(v_fst_2136_);
                crate::leanh::lean_dec_ref(v___x_2134_);
                v_fst_2137_ = crate::leanh::lean_ctor_get(v_snd_2135_, 0);
                crate::leanh::lean_inc(v_fst_2137_);
                crate::leanh::lean_dec(v_snd_2135_);
                v_array_2138_ = crate::leanh::lean_ctor_get(v_it_2132_, 0);
                v_idx_2139_ = crate::leanh::lean_ctor_get(v_it_2132_, 1);
                v_isSharedCheck_2156_ = (!crate::leanh::lean_is_exclusive(v_it_2132_)) as u8;
                if v_isSharedCheck_2156_ == 0 {
                    v___x_2141_ = v_it_2132_;
                    v_isShared_2142_ = v_isSharedCheck_2156_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_2139_);
                    crate::leanh::lean_inc(v_array_2138_);
                    crate::leanh::lean_dec(v_it_2132_);
                    v___x_2141_ = crate::leanh::lean_box(0);
                    v_isShared_2142_ = v_isSharedCheck_2156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2150_ = lean_nat_add(v_idx_2139_, v_fst_2136_);
                crate::leanh::lean_dec(v_fst_2136_);
                v___x_2151_ = lean_byte_array_size(v_array_2138_);
                v___x_2155_ = lean_nat_dec_le(v_idx_2139_, v___x_2133_);
                if v___x_2155_ == 0 {
                    v___y_2153_ = v_idx_2139_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_2139_);
                    v___y_2153_ = v___x_2133_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2146_ = l_ByteArray_toByteSlice(v_array_2138_, v_lower_2144_, v_upper_2145_);
                if v_isShared_2142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2141_, 1, v___x_2146_);
                    crate::leanh::lean_ctor_set(v___x_2141_, 0, v_fst_2137_);
                    v___x_2148_ = v___x_2141_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_fst_2137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 1, v___x_2146_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2148_;
            }
            4 => {
                v___x_2154_ = lean_nat_dec_le(v___x_2150_, v___x_2151_);
                if v___x_2154_ == 0 {
                    crate::leanh::lean_dec(v___x_2150_);
                    v_lower_2144_ = v___y_2153_;
                    v_upper_2145_ = v___x_2151_;
                    state = 2;
                    continue;
                } else {
                    v_lower_2144_ = v___y_2153_;
                    v_upper_2145_ = v___x_2150_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(
    mut v_pred_2157_: *mut crate::leanh::LeanObject,
    mut v_limit_2158_: *mut crate::leanh::LeanObject,
    mut v_it_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2160_ =
        l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_2157_, v_limit_2158_, v_it_2159_);
    crate::leanh::lean_dec(v_limit_2158_);
    return v_res_2160_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(
    mut v_pred_2161_: *mut crate::leanh::LeanObject,
    mut v_limit_2162_: *mut crate::leanh::LeanObject,
    mut v_it_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2172_: u8 = 0;
    let mut v_array_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_lower_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_unused_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_it_2163_);
                v___x_2165_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_2161_, v_limit_2162_, v___x_2164_, v_it_2163_);
                v_snd_2166_ = crate::leanh::lean_ctor_get(v___x_2165_, 1);
                crate::leanh::lean_inc(v_snd_2166_);
                v_fst_2167_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
                crate::leanh::lean_inc(v_fst_2167_);
                crate::leanh::lean_dec_ref(v___x_2165_);
                v_fst_2168_ = crate::leanh::lean_ctor_get(v_snd_2166_, 0);
                v_isSharedCheck_2196_ = (!crate::leanh::lean_is_exclusive(v_snd_2166_)) as u8;
                if v_isSharedCheck_2196_ == 0 {
                    v_unused_2197_ = crate::leanh::lean_ctor_get(v_snd_2166_, 1);
                    crate::leanh::lean_dec(v_unused_2197_);
                    v___x_2170_ = v_snd_2166_;
                    v_isShared_2171_ = v_isSharedCheck_2196_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2168_);
                    crate::leanh::lean_dec(v_snd_2166_);
                    v___x_2170_ = crate::leanh::lean_box(0);
                    v_isShared_2171_ = v_isSharedCheck_2196_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2172_ = lean_nat_dec_eq(v_fst_2167_, v___x_2164_);
                if v___x_2172_ == 0 {
                    crate::leanh::lean_del_object(v___x_2170_);
                    v_array_2173_ = crate::leanh::lean_ctor_get(v_it_2163_, 0);
                    v_idx_2174_ = crate::leanh::lean_ctor_get(v_it_2163_, 1);
                    v_isSharedCheck_2191_ = (!crate::leanh::lean_is_exclusive(v_it_2163_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2176_ = v_it_2163_;
                        v_isShared_2177_ = v_isSharedCheck_2191_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_2174_);
                        crate::leanh::lean_inc(v_array_2173_);
                        crate::leanh::lean_dec(v_it_2163_);
                        v___x_2176_ = crate::leanh::lean_box(0);
                        v_isShared_2177_ = v_isSharedCheck_2191_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2168_);
                    crate::leanh::lean_dec(v_fst_2167_);
                    v___x_2192_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1;
                    if v_isShared_2171_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2170_, 1);
                        crate::leanh::lean_ctor_set(v___x_2170_, 1, v___x_2192_);
                        crate::leanh::lean_ctor_set(v___x_2170_, 0, v_it_2163_);
                        v___x_2194_ = v___x_2170_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2195_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_it_2163_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2192_);
                        v___x_2194_ = v_reuseFailAlloc_2195_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2185_ = lean_nat_add(v_idx_2174_, v_fst_2167_);
                crate::leanh::lean_dec(v_fst_2167_);
                v___x_2186_ = lean_byte_array_size(v_array_2173_);
                v___x_2190_ = lean_nat_dec_le(v_idx_2174_, v___x_2164_);
                if v___x_2190_ == 0 {
                    v___y_2188_ = v_idx_2174_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_idx_2174_);
                    v___y_2188_ = v___x_2164_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_2181_ = l_ByteArray_toByteSlice(v_array_2173_, v_lower_2179_, v_upper_2180_);
                if v_isShared_2177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2181_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 0, v_fst_2168_);
                    v___x_2183_ = v___x_2176_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_fst_2168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2183_;
            }
            5 => {
                v___x_2189_ = lean_nat_dec_le(v___x_2185_, v___x_2186_);
                if v___x_2189_ == 0 {
                    crate::leanh::lean_dec(v___x_2185_);
                    v_lower_2179_ = v___y_2188_;
                    v_upper_2180_ = v___x_2186_;
                    state = 3;
                    continue;
                } else {
                    v_lower_2179_ = v___y_2188_;
                    v_upper_2180_ = v___x_2185_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                return v___x_2194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(
    mut v_pred_2198_: *mut crate::leanh::LeanObject,
    mut v_limit_2199_: *mut crate::leanh::LeanObject,
    mut v_it_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ =
        l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_2198_, v_limit_2199_, v_it_2200_);
    crate::leanh::lean_dec(v_limit_2199_);
    return v_res_2201_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(
    mut v_pred_2202_: *mut crate::leanh::LeanObject,
    mut v_limit_2203_: *mut crate::leanh::LeanObject,
    mut v_it_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    let mut v_fst_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2218_: u8 = 0;
    let mut v_unused_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2205_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2206_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_2202_, v_limit_2203_, v___x_2205_, v_it_2204_);
                v_snd_2207_ = crate::leanh::lean_ctor_get(v___x_2206_, 1);
                crate::leanh::lean_inc(v_snd_2207_);
                crate::leanh::lean_dec_ref(v___x_2206_);
                v_snd_2208_ = crate::leanh::lean_ctor_get(v_snd_2207_, 1);
                v___x_2209_ = (crate::leanh::lean_unbox(v_snd_2208_) as u8);
                if v___x_2209_ == 0 {
                    v_fst_2210_ = crate::leanh::lean_ctor_get(v_snd_2207_, 0);
                    v_isSharedCheck_2218_ = (!crate::leanh::lean_is_exclusive(v_snd_2207_)) as u8;
                    if v_isSharedCheck_2218_ == 0 {
                        v_unused_2219_ = crate::leanh::lean_ctor_get(v_snd_2207_, 1);
                        crate::leanh::lean_dec(v_unused_2219_);
                        v___x_2212_ = v_snd_2207_;
                        v_isShared_2213_ = v_isSharedCheck_2218_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2210_);
                        crate::leanh::lean_dec(v_snd_2207_);
                        v___x_2212_ = crate::leanh::lean_box(0);
                        v_isShared_2213_ = v_isSharedCheck_2218_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_2220_ = crate::leanh::lean_ctor_get(v_snd_2207_, 0);
                    v_isSharedCheck_2228_ = (!crate::leanh::lean_is_exclusive(v_snd_2207_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v_unused_2229_ = crate::leanh::lean_ctor_get(v_snd_2207_, 1);
                        crate::leanh::lean_dec(v_unused_2229_);
                        v___x_2222_ = v_snd_2207_;
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2220_);
                        crate::leanh::lean_dec(v_snd_2207_);
                        v___x_2222_ = crate::leanh::lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2214_ = crate::leanh::lean_box(0);
                if v_isShared_2213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2212_, 1, v___x_2214_);
                    v___x_2216_ = v___x_2212_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_fst_2210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2214_);
                    v___x_2216_ = v_reuseFailAlloc_2217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2216_;
            }
            3 => {
                v___x_2224_ = crate::leanh::lean_box(0);
                if v_isShared_2223_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2222_, 1);
                    crate::leanh::lean_ctor_set(v___x_2222_, 1, v___x_2224_);
                    v___x_2226_ = v___x_2222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_fst_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2224_);
                    v___x_2226_ = v_reuseFailAlloc_2227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(
    mut v_pred_2230_: *mut crate::leanh::LeanObject,
    mut v_limit_2231_: *mut crate::leanh::LeanObject,
    mut v_it_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ =
        l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_2230_, v_limit_2231_, v_it_2232_);
    crate::leanh::lean_dec(v_limit_2231_);
    return v_res_2233_;
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(
    mut v_pred_2234_: *mut crate::leanh::LeanObject,
    mut v_limit_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v_fst_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_unused_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_unused_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2237_ = crate::leanh::lean_alloc_closure(
                    l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2237_, 0, v_pred_2234_);
                v___x_2238_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2239_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2237_, v_limit_2235_, v___x_2238_, v_a_2236_);
                v_snd_2240_ = crate::leanh::lean_ctor_get(v___x_2239_, 1);
                crate::leanh::lean_inc(v_snd_2240_);
                crate::leanh::lean_dec_ref(v___x_2239_);
                v_snd_2241_ = crate::leanh::lean_ctor_get(v_snd_2240_, 1);
                v___x_2242_ = (crate::leanh::lean_unbox(v_snd_2241_) as u8);
                if v___x_2242_ == 0 {
                    v_fst_2243_ = crate::leanh::lean_ctor_get(v_snd_2240_, 0);
                    v_isSharedCheck_2251_ = (!crate::leanh::lean_is_exclusive(v_snd_2240_)) as u8;
                    if v_isSharedCheck_2251_ == 0 {
                        v_unused_2252_ = crate::leanh::lean_ctor_get(v_snd_2240_, 1);
                        crate::leanh::lean_dec(v_unused_2252_);
                        v___x_2245_ = v_snd_2240_;
                        v_isShared_2246_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2243_);
                        crate::leanh::lean_dec(v_snd_2240_);
                        v___x_2245_ = crate::leanh::lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_2253_ = crate::leanh::lean_ctor_get(v_snd_2240_, 0);
                    v_isSharedCheck_2261_ = (!crate::leanh::lean_is_exclusive(v_snd_2240_)) as u8;
                    if v_isSharedCheck_2261_ == 0 {
                        v_unused_2262_ = crate::leanh::lean_ctor_get(v_snd_2240_, 1);
                        crate::leanh::lean_dec(v_unused_2262_);
                        v___x_2255_ = v_snd_2240_;
                        v_isShared_2256_ = v_isSharedCheck_2261_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2253_);
                        crate::leanh::lean_dec(v_snd_2240_);
                        v___x_2255_ = crate::leanh::lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2261_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2247_ = crate::leanh::lean_box(0);
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 1, v___x_2247_);
                    v___x_2249_ = v___x_2245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_fst_2243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 1, v___x_2247_);
                    v___x_2249_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2249_;
            }
            3 => {
                v___x_2257_ = crate::leanh::lean_box(0);
                if v_isShared_2256_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2255_, 1);
                    crate::leanh::lean_ctor_set(v___x_2255_, 1, v___x_2257_);
                    v___x_2259_ = v___x_2255_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_fst_2253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2257_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(
    mut v_pred_2263_: *mut crate::leanh::LeanObject,
    mut v_limit_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2266_ =
        l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_2263_, v_limit_2264_, v_a_2265_);
    crate::leanh::lean_dec(v_limit_2264_);
    return v_res_2266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Parsec_ByteArray(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ByteSlice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Parsec_ByteArray(
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
pub unsafe fn initialize_Std_Internal_Parsec_ByteArray(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_ByteSlice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Parsec_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Parsec_ByteArray(builtin);
}
