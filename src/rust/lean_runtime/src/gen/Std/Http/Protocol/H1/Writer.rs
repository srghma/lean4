// Lean compiler output
// Module: Std.Http.Protocol.H1.Writer
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message Std.Http.Protocol.H1.Error
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{l_ByteArray_extract, l_ByteArray_isEmpty};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Nat_toDigits, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{l_Char_utf8Size, l_String_decEq___boxed, l_String_hash___boxed};
use crate::r#gen::Std::Http::Data::Chunk::l_Std_Http_Chunk_ExtensionValue_quote;
use crate::r#gen::Std::Http::Data::Headers::Name::l_Std_Http_Header_Name_connection;
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::IndexMultiMap::l_Std_Internal_IndexMultiMap_instDecidableMem___redArg;
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Http::Protocol::H1::Config::{
    initialize_Std_Http_Protocol_H1_Config, runtime_initialize_Std_Http_Protocol_H1_Config,
};
use crate::r#gen::Std::Http::Protocol::H1::Error::{
    initialize_Std_Http_Protocol_H1_Error, runtime_initialize_Std_Http_Protocol_H1_Error,
};
use crate::r#gen::Std::Http::Protocol::H1::Message::{
    initialize_Std_Http_Protocol_H1_Message, l_Std_Http_Protocol_H1_Message_Head_headers,
    l_Std_Http_Protocol_H1_instEncodeV11Head, runtime_initialize_Std_Http_Protocol_H1_Message,
};
use crate::r#gen::Std::Http::Protocol::H1::Parser::{
    initialize_Std_Http_Protocol_H1_Parser, runtime_initialize_Std_Http_Protocol_H1_Parser,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_copy_slice;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_get_fast;
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_add, lean_uint32_to_uint8, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_mk, lean_array_push, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_mk_empty_byte_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq, lean_string_hash, lean_string_utf8_byte_size, lean_uint32_dec_le,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static mut l_Std_Http_Protocol_H1_Writer_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Protocol_H1_Writer_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value: LeanStringObject<
    50,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 119, 97, 105, 116, 105,
        110, 103, 70, 111, 114, 70, 108, 117, 115, 104, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value: LeanStringObject<
    49,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 119, 97, 105, 116, 105,
        110, 103, 72, 101, 97, 100, 101, 114, 115, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value: LeanStringObject<
    42,
> = LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 112, 101, 110, 100, 105,
        110, 103, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value: LeanStringObject<
    53,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 119, 114, 105, 116, 105,
        110, 103, 66, 111, 100, 121, 67, 104, 117, 110, 107, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value: LeanStringObject<
    58,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 119, 114, 105, 116, 105,
        110, 103, 66, 111, 100, 121, 67, 108, 111, 115, 105, 110, 103, 70, 114, 97, 109, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value: LeanStringObject<
    43,
> = LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 99, 111, 109, 112, 108,
        101, 116, 101, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value: LeanStringObject<
    41,
> = LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 99, 108, 111, 115, 101,
        100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value)
        as *mut LeanObject;
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value: LeanStringObject<
    51,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72, 49,
        46, 87, 114, 105, 116, 101, 114, 46, 83, 116, 97, 116, 101, 46, 119, 114, 105, 116, 105,
        110, 103, 66, 111, 100, 121, 70, 105, 120, 101, 100, 0,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_Writer_instReprState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Protocol_H1_Writer_instReprState: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Protocol_H1_Writer_instBEqState: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [13, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [48, 13, 10, 13, 10, 0],
};
static mut l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value
            ) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_String_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 108, 111, 115, 101, 0],
    };
static mut l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_ctorIdx(
    mut v_x_1327_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1327_) {
        0 => {
            let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
            v___x_1328_ = lean_unsigned_to_nat(0);
            return v___x_1328_;
        }
        1 => {
            let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
            v___x_1329_ = lean_unsigned_to_nat(1);
            return v___x_1329_;
        }
        2 => {
            let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
            v___x_1330_ = lean_unsigned_to_nat(2);
            return v___x_1330_;
        }
        3 => {
            let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
            v___x_1331_ = lean_unsigned_to_nat(3);
            return v___x_1331_;
        }
        4 => {
            let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
            v___x_1332_ = lean_unsigned_to_nat(4);
            return v___x_1332_;
        }
        5 => {
            let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
            v___x_1333_ = lean_unsigned_to_nat(5);
            return v___x_1333_;
        }
        6 => {
            let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
            v___x_1334_ = lean_unsigned_to_nat(6);
            return v___x_1334_;
        }
        _ => {
            let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
            v___x_1335_ = lean_unsigned_to_nat(7);
            return v___x_1335_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_ctorIdx___boxed(
    mut v_x_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1337_: *mut LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Std_Http_Protocol_H1_Writer_State_ctorIdx(v_x_1336_);
    lean_dec(v_x_1336_);
    return v_res_1337_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(
    mut v_t_1338_: *mut LeanObject,
    mut v_k_1339_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1338_) == 3 {
        let mut v_n_1340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
        v_n_1340_ = lean_ctor_get(v_t_1338_, 0);
        lean_inc(v_n_1340_);
        lean_dec_ref_known(v_t_1338_, 1);
        v___x_1341_ = lean_apply_1(v_k_1339_, v_n_1340_);
        return v___x_1341_;
    } else {
        lean_dec(v_t_1338_);
        return v_k_1339_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_ctorElim(
    mut v_motive_1342_: *mut LeanObject,
    mut v_ctorIdx_1343_: *mut LeanObject,
    mut v_t_1344_: *mut LeanObject,
    mut v_h_1345_: *mut LeanObject,
    mut v_k_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1344_, v_k_1346_);
    return v___x_1347_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_ctorElim___boxed(
    mut v_motive_1348_: *mut LeanObject,
    mut v_ctorIdx_1349_: *mut LeanObject,
    mut v_t_1350_: *mut LeanObject,
    mut v_h_1351_: *mut LeanObject,
    mut v_k_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1353_: *mut LeanObject = core::ptr::null_mut();
    v_res_1353_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim(
        v_motive_1348_,
        v_ctorIdx_1349_,
        v_t_1350_,
        v_h_1351_,
        v_k_1352_,
    );
    lean_dec(v_ctorIdx_1349_);
    return v_res_1353_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_pending_elim___redArg(
    mut v_t_1354_: *mut LeanObject,
    mut v_pending_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1354_, v_pending_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_pending_elim(
    mut v_motive_1357_: *mut LeanObject,
    mut v_t_1358_: *mut LeanObject,
    mut v_h_1359_: *mut LeanObject,
    mut v_pending_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1361_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1358_, v_pending_1360_);
    return v___x_1361_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim___redArg(
    mut v_t_1362_: *mut LeanObject,
    mut v_waitingHeaders_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1362_, v_waitingHeaders_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim(
    mut v_motive_1365_: *mut LeanObject,
    mut v_t_1366_: *mut LeanObject,
    mut v_h_1367_: *mut LeanObject,
    mut v_waitingHeaders_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1366_, v_waitingHeaders_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim___redArg(
    mut v_t_1370_: *mut LeanObject,
    mut v_waitingForFlush_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1370_, v_waitingForFlush_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim(
    mut v_motive_1373_: *mut LeanObject,
    mut v_t_1374_: *mut LeanObject,
    mut v_h_1375_: *mut LeanObject,
    mut v_waitingForFlush_1376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    v___x_1377_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1374_, v_waitingForFlush_1376_);
    return v___x_1377_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim___redArg(
    mut v_t_1378_: *mut LeanObject,
    mut v_writingBodyFixed_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1378_, v_writingBodyFixed_1379_);
    return v___x_1380_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim(
    mut v_motive_1381_: *mut LeanObject,
    mut v_t_1382_: *mut LeanObject,
    mut v_h_1383_: *mut LeanObject,
    mut v_writingBodyFixed_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1385_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1382_, v_writingBodyFixed_1384_);
    return v___x_1385_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim___redArg(
    mut v_t_1386_: *mut LeanObject,
    mut v_writingBodyChunked_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(
        v_t_1386_,
        v_writingBodyChunked_1387_,
    );
    return v___x_1388_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim(
    mut v_motive_1389_: *mut LeanObject,
    mut v_t_1390_: *mut LeanObject,
    mut v_h_1391_: *mut LeanObject,
    mut v_writingBodyChunked_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(
        v_t_1390_,
        v_writingBodyChunked_1392_,
    );
    return v___x_1393_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim___redArg(
    mut v_t_1394_: *mut LeanObject,
    mut v_writingBodyClosingFrame_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(
        v_t_1394_,
        v_writingBodyClosingFrame_1395_,
    );
    return v___x_1396_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim(
    mut v_motive_1397_: *mut LeanObject,
    mut v_t_1398_: *mut LeanObject,
    mut v_h_1399_: *mut LeanObject,
    mut v_writingBodyClosingFrame_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(
        v_t_1398_,
        v_writingBodyClosingFrame_1400_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_complete_elim___redArg(
    mut v_t_1402_: *mut LeanObject,
    mut v_complete_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1402_, v_complete_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_complete_elim(
    mut v_motive_1405_: *mut LeanObject,
    mut v_t_1406_: *mut LeanObject,
    mut v_h_1407_: *mut LeanObject,
    mut v_complete_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1409_ =
        l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1406_, v_complete_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_closed_elim___redArg(
    mut v_t_1410_: *mut LeanObject,
    mut v_closed_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1410_, v_closed_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_State_closed_elim(
    mut v_motive_1413_: *mut LeanObject,
    mut v_t_1414_: *mut LeanObject,
    mut v_h_1415_: *mut LeanObject,
    mut v_closed_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_1414_, v_closed_1416_);
    return v___x_1417_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    v___x_1418_ = lean_box(0);
    return v___x_1418_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState() -> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = lean_box(0);
    return v___x_1419_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14()
-> *mut LeanObject {
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1441_ = lean_unsigned_to_nat(2);
    v___x_1442_ = lean_nat_to_int(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15()
-> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = lean_unsigned_to_nat(1);
    v___x_1444_ = lean_nat_to_int(v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_instReprState_repr(
    mut v_x_1451_: *mut LeanObject,
    mut v_prec_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___y_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_1451_) {
                    0 => {
                        v___x_1502_ = lean_unsigned_to_nat(1024);
                        v___x_1503_ = lean_nat_dec_le(v___x_1502_, v_prec_1452_);
                        if v___x_1503_ == 0 {
                            v___x_1504_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1468_ = v___x_1504_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1505_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1468_ = v___x_1505_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v___x_1506_ = lean_unsigned_to_nat(1024);
                        v___x_1507_ = lean_nat_dec_le(v___x_1506_, v_prec_1452_);
                        if v___x_1507_ == 0 {
                            v___x_1508_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1461_ = v___x_1508_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1509_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1461_ = v___x_1509_;
                            state = 2;
                            continue;
                        }
                    }
                    2 => {
                        v___x_1510_ = lean_unsigned_to_nat(1024);
                        v___x_1511_ = lean_nat_dec_le(v___x_1510_, v_prec_1452_);
                        if v___x_1511_ == 0 {
                            v___x_1512_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1454_ = v___x_1512_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1513_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1454_ = v___x_1513_;
                            state = 1;
                            continue;
                        }
                    }
                    3 => {
                        v_n_1514_ = lean_ctor_get(v_x_1451_, 0);
                        v_isSharedCheck_1534_ = (!lean_is_exclusive(v_x_1451_)) as u8;
                        if v_isSharedCheck_1534_ == 0 {
                            v___x_1516_ = v_x_1451_;
                            v_isShared_1517_ = v_isSharedCheck_1534_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_n_1514_);
                            lean_dec(v_x_1451_);
                            v___x_1516_ = lean_box(0);
                            v_isShared_1517_ = v_isSharedCheck_1534_;
                            state = 8;
                            continue;
                        }
                    }
                    4 => {
                        v___x_1535_ = lean_unsigned_to_nat(1024);
                        v___x_1536_ = lean_nat_dec_le(v___x_1535_, v_prec_1452_);
                        if v___x_1536_ == 0 {
                            v___x_1537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1475_ = v___x_1537_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1538_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1475_ = v___x_1538_;
                            state = 4;
                            continue;
                        }
                    }
                    5 => {
                        v___x_1539_ = lean_unsigned_to_nat(1024);
                        v___x_1540_ = lean_nat_dec_le(v___x_1539_, v_prec_1452_);
                        if v___x_1540_ == 0 {
                            v___x_1541_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1482_ = v___x_1541_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1542_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1482_ = v___x_1542_;
                            state = 5;
                            continue;
                        }
                    }
                    6 => {
                        v___x_1543_ = lean_unsigned_to_nat(1024);
                        v___x_1544_ = lean_nat_dec_le(v___x_1543_, v_prec_1452_);
                        if v___x_1544_ == 0 {
                            v___x_1545_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1489_ = v___x_1545_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1546_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1489_ = v___x_1546_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1547_ = lean_unsigned_to_nat(1024);
                        v___x_1548_ = lean_nat_dec_le(v___x_1547_, v_prec_1452_);
                        if v___x_1548_ == 0 {
                            v___x_1549_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
                            v___y_1496_ = v___x_1549_;
                            state = 7;
                            continue;
                        } else {
                            v___x_1550_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15), core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once), _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
                            v___y_1496_ = v___x_1550_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1455_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1;
                lean_inc(v___y_1454_);
                v___x_1456_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1456_, 0, v___y_1454_);
                lean_ctor_set(v___x_1456_, 1, v___x_1455_);
                v___x_1457_ = 0;
                v___x_1458_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1458_, 0, v___x_1456_);
                lean_ctor_set_uint8(
                    v___x_1458_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1457_,
                );
                v___x_1459_ = l_Repr_addAppParen(v___x_1458_, v_prec_1452_);
                return v___x_1459_;
            }
            2 => {
                v___x_1462_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3;
                lean_inc(v___y_1461_);
                v___x_1463_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1463_, 0, v___y_1461_);
                lean_ctor_set(v___x_1463_, 1, v___x_1462_);
                v___x_1464_ = 0;
                v___x_1465_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1465_, 0, v___x_1463_);
                lean_ctor_set_uint8(
                    v___x_1465_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1464_,
                );
                v___x_1466_ = l_Repr_addAppParen(v___x_1465_, v_prec_1452_);
                return v___x_1466_;
            }
            3 => {
                v___x_1469_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5;
                lean_inc(v___y_1468_);
                v___x_1470_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1470_, 0, v___y_1468_);
                lean_ctor_set(v___x_1470_, 1, v___x_1469_);
                v___x_1471_ = 0;
                v___x_1472_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1472_, 0, v___x_1470_);
                lean_ctor_set_uint8(
                    v___x_1472_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1471_,
                );
                v___x_1473_ = l_Repr_addAppParen(v___x_1472_, v_prec_1452_);
                return v___x_1473_;
            }
            4 => {
                v___x_1476_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7;
                lean_inc(v___y_1475_);
                v___x_1477_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1477_, 0, v___y_1475_);
                lean_ctor_set(v___x_1477_, 1, v___x_1476_);
                v___x_1478_ = 0;
                v___x_1479_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1479_, 0, v___x_1477_);
                lean_ctor_set_uint8(
                    v___x_1479_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1478_,
                );
                v___x_1480_ = l_Repr_addAppParen(v___x_1479_, v_prec_1452_);
                return v___x_1480_;
            }
            5 => {
                v___x_1483_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9;
                lean_inc(v___y_1482_);
                v___x_1484_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1484_, 0, v___y_1482_);
                lean_ctor_set(v___x_1484_, 1, v___x_1483_);
                v___x_1485_ = 0;
                v___x_1486_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1486_, 0, v___x_1484_);
                lean_ctor_set_uint8(
                    v___x_1486_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1485_,
                );
                v___x_1487_ = l_Repr_addAppParen(v___x_1486_, v_prec_1452_);
                return v___x_1487_;
            }
            6 => {
                v___x_1490_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11;
                lean_inc(v___y_1489_);
                v___x_1491_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1491_, 0, v___y_1489_);
                lean_ctor_set(v___x_1491_, 1, v___x_1490_);
                v___x_1492_ = 0;
                v___x_1493_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1493_, 0, v___x_1491_);
                lean_ctor_set_uint8(
                    v___x_1493_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1492_,
                );
                v___x_1494_ = l_Repr_addAppParen(v___x_1493_, v_prec_1452_);
                return v___x_1494_;
            }
            7 => {
                v___x_1497_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13;
                lean_inc(v___y_1496_);
                v___x_1498_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1498_, 0, v___y_1496_);
                lean_ctor_set(v___x_1498_, 1, v___x_1497_);
                v___x_1499_ = 0;
                v___x_1500_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1500_, 0, v___x_1498_);
                lean_ctor_set_uint8(
                    v___x_1500_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1499_,
                );
                v___x_1501_ = l_Repr_addAppParen(v___x_1500_, v_prec_1452_);
                return v___x_1501_;
            }
            8 => {
                v___x_1530_ = lean_unsigned_to_nat(1024);
                v___x_1531_ = lean_nat_dec_le(v___x_1530_, v_prec_1452_);
                if v___x_1531_ == 0 {
                    v___x_1532_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14,
                    );
                    v___y_1519_ = v___x_1532_;
                    state = 9;
                    continue;
                } else {
                    v___x_1533_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once
                        ),
                        _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15,
                    );
                    v___y_1519_ = v___x_1533_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1520_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18;
                v___x_1521_ = l_Nat_reprFast(v_n_1514_);
                if v_isShared_1517_ == 0 {
                    lean_ctor_set(v___x_1516_, 0, v___x_1521_);
                    v___x_1523_ = v___x_1516_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1521_);
                    v___x_1523_ = v_reuseFailAlloc_1529_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1524_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1524_, 0, v___x_1520_);
                lean_ctor_set(v___x_1524_, 1, v___x_1523_);
                lean_inc(v___y_1519_);
                v___x_1525_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1525_, 0, v___y_1519_);
                lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                v___x_1526_ = 0;
                v___x_1527_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1527_, 0, v___x_1525_);
                lean_ctor_set_uint8(
                    v___x_1527_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1526_,
                );
                v___x_1528_ = l_Repr_addAppParen(v___x_1527_, v_prec_1452_);
                return v___x_1528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed(
    mut v_x_1551_: *mut LeanObject,
    mut v_prec_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr(v_x_1551_, v_prec_1552_);
    lean_dec(v_prec_1552_);
    return v_res_1553_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_instBEqState_beq(
    mut v_x_1556_: *mut LeanObject,
    mut v_x_1557_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1556_) {
        0 => {
            if lean_obj_tag(v_x_1557_) == 0 {
                let mut v___x_1558_: u8 = 0;
                v___x_1558_ = 1;
                return v___x_1558_;
            } else {
                let mut v___x_1559_: u8 = 0;
                v___x_1559_ = 0;
                return v___x_1559_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_1557_) == 1 {
                let mut v___x_1560_: u8 = 0;
                v___x_1560_ = 1;
                return v___x_1560_;
            } else {
                let mut v___x_1561_: u8 = 0;
                v___x_1561_ = 0;
                return v___x_1561_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_1557_) == 2 {
                let mut v___x_1562_: u8 = 0;
                v___x_1562_ = 1;
                return v___x_1562_;
            } else {
                let mut v___x_1563_: u8 = 0;
                v___x_1563_ = 0;
                return v___x_1563_;
            }
        }
        3 => {
            if lean_obj_tag(v_x_1557_) == 3 {
                let mut v_n_1564_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_1565_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1566_: u8 = 0;
                v_n_1564_ = lean_ctor_get(v_x_1556_, 0);
                v_n_1565_ = lean_ctor_get(v_x_1557_, 0);
                v___x_1566_ = lean_nat_dec_eq(v_n_1564_, v_n_1565_);
                return v___x_1566_;
            } else {
                let mut v___x_1567_: u8 = 0;
                v___x_1567_ = 0;
                return v___x_1567_;
            }
        }
        4 => {
            if lean_obj_tag(v_x_1557_) == 4 {
                let mut v___x_1568_: u8 = 0;
                v___x_1568_ = 1;
                return v___x_1568_;
            } else {
                let mut v___x_1569_: u8 = 0;
                v___x_1569_ = 0;
                return v___x_1569_;
            }
        }
        5 => {
            if lean_obj_tag(v_x_1557_) == 5 {
                let mut v___x_1570_: u8 = 0;
                v___x_1570_ = 1;
                return v___x_1570_;
            } else {
                let mut v___x_1571_: u8 = 0;
                v___x_1571_ = 0;
                return v___x_1571_;
            }
        }
        6 => {
            if lean_obj_tag(v_x_1557_) == 6 {
                let mut v___x_1572_: u8 = 0;
                v___x_1572_ = 1;
                return v___x_1572_;
            } else {
                let mut v___x_1573_: u8 = 0;
                v___x_1573_ = 0;
                return v___x_1573_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_1557_) == 7 {
                let mut v___x_1574_: u8 = 0;
                v___x_1574_ = 1;
                return v___x_1574_;
            } else {
                let mut v___x_1575_: u8 = 0;
                v___x_1575_ = 0;
                return v___x_1575_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(
    mut v_x_1576_: *mut LeanObject,
    mut v_x_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: u8 = 0;
    let mut v_r_1579_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_1576_, v_x_1577_);
    lean_dec(v_x_1577_);
    lean_dec(v_x_1576_);
    v_r_1579_ = lean_box((v_res_1578_) as usize);
    return v_r_1579_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(
    mut v_writer_1582_: *mut LeanObject,
) -> u8 {
    let mut v_state_1583_: *mut LeanObject = core::ptr::null_mut();
    v_state_1583_ = lean_ctor_get(v_writer_1582_, 2);
    match lean_obj_tag(v_state_1583_) {
        7 => {
            let mut v___x_1584_: u8 = 0;
            v___x_1584_ = 1;
            return v___x_1584_;
        }
        6 => {
            let mut v___x_1585_: u8 = 0;
            v___x_1585_ = 1;
            return v___x_1585_;
        }
        _ => {
            let mut v_userClosedBody_1586_: u8 = 0;
            v_userClosedBody_1586_ = lean_ctor_get_uint8(
                v_writer_1582_,
                (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
            );
            return v_userClosedBody_1586_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(
    mut v_writer_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1588_: u8 = 0;
    let mut v_r_1589_: *mut LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_1587_);
    lean_dec_ref(v_writer_1587_);
    v_r_1589_ = lean_box((v_res_1588_) as usize);
    return v_r_1589_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_noMoreUserData(
    mut v_dir_1590_: u8,
    mut v_writer_1591_: *mut LeanObject,
) -> u8 {
    let mut v_state_1592_: *mut LeanObject = core::ptr::null_mut();
    v_state_1592_ = lean_ctor_get(v_writer_1591_, 2);
    match lean_obj_tag(v_state_1592_) {
        7 => {
            let mut v___x_1593_: u8 = 0;
            v___x_1593_ = 1;
            return v___x_1593_;
        }
        6 => {
            let mut v___x_1594_: u8 = 0;
            v___x_1594_ = 1;
            return v___x_1594_;
        }
        _ => {
            let mut v_userClosedBody_1595_: u8 = 0;
            v_userClosedBody_1595_ = lean_ctor_get_uint8(
                v_writer_1591_,
                (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
            );
            return v_userClosedBody_1595_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(
    mut v_dir_1596_: *mut LeanObject,
    mut v_writer_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1598_: u8 = 0;
    let mut v_res_1599_: u8 = 0;
    let mut v_r_1600_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1598_ = (lean_unbox(v_dir_1596_) as u8);
    v_res_1599_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_1598_, v_writer_1597_);
    lean_dec_ref(v_writer_1597_);
    v_r_1600_ = lean_box((v_res_1599_) as usize);
    return v_r_1600_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isClosed___redArg(
    mut v_writer_1601_: *mut LeanObject,
) -> u8 {
    let mut v_state_1602_: *mut LeanObject = core::ptr::null_mut();
    v_state_1602_ = lean_ctor_get(v_writer_1601_, 2);
    if lean_obj_tag(v_state_1602_) == 7 {
        let mut v___x_1603_: u8 = 0;
        v___x_1603_ = 1;
        return v___x_1603_;
    } else {
        let mut v___x_1604_: u8 = 0;
        v___x_1604_ = 0;
        return v___x_1604_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(
    mut v_writer_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1606_: u8 = 0;
    let mut v_r_1607_: *mut LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_1605_);
    lean_dec_ref(v_writer_1605_);
    v_r_1607_ = lean_box((v_res_1606_) as usize);
    return v_r_1607_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isClosed(
    mut v_dir_1608_: u8,
    mut v_writer_1609_: *mut LeanObject,
) -> u8 {
    let mut v_state_1610_: *mut LeanObject = core::ptr::null_mut();
    v_state_1610_ = lean_ctor_get(v_writer_1609_, 2);
    if lean_obj_tag(v_state_1610_) == 7 {
        let mut v___x_1611_: u8 = 0;
        v___x_1611_ = 1;
        return v___x_1611_;
    } else {
        let mut v___x_1612_: u8 = 0;
        v___x_1612_ = 0;
        return v___x_1612_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isClosed___boxed(
    mut v_dir_1613_: *mut LeanObject,
    mut v_writer_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1615_: u8 = 0;
    let mut v_res_1616_: u8 = 0;
    let mut v_r_1617_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1615_ = (lean_unbox(v_dir_1613_) as u8);
    v_res_1616_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_1615_, v_writer_1614_);
    lean_dec_ref(v_writer_1614_);
    v_r_1617_ = lean_box((v_res_1616_) as usize);
    return v_r_1617_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isComplete___redArg(
    mut v_writer_1618_: *mut LeanObject,
) -> u8 {
    let mut v_state_1619_: *mut LeanObject = core::ptr::null_mut();
    v_state_1619_ = lean_ctor_get(v_writer_1618_, 2);
    if lean_obj_tag(v_state_1619_) == 6 {
        let mut v___x_1620_: u8 = 0;
        v___x_1620_ = 1;
        return v___x_1620_;
    } else {
        let mut v___x_1621_: u8 = 0;
        v___x_1621_ = 0;
        return v___x_1621_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(
    mut v_writer_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1623_: u8 = 0;
    let mut v_r_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_1622_);
    lean_dec_ref(v_writer_1622_);
    v_r_1624_ = lean_box((v_res_1623_) as usize);
    return v_r_1624_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isComplete(
    mut v_dir_1625_: u8,
    mut v_writer_1626_: *mut LeanObject,
) -> u8 {
    let mut v_state_1627_: *mut LeanObject = core::ptr::null_mut();
    v_state_1627_ = lean_ctor_get(v_writer_1626_, 2);
    if lean_obj_tag(v_state_1627_) == 6 {
        let mut v___x_1628_: u8 = 0;
        v___x_1628_ = 1;
        return v___x_1628_;
    } else {
        let mut v___x_1629_: u8 = 0;
        v___x_1629_ = 0;
        return v___x_1629_;
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_isComplete___boxed(
    mut v_dir_1630_: *mut LeanObject,
    mut v_writer_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1632_: u8 = 0;
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1632_ = (lean_unbox(v_dir_1630_) as u8);
    v_res_1633_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_boxed_1632_, v_writer_1631_);
    lean_dec_ref(v_writer_1631_);
    v_r_1634_ = lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(
    mut v_writer_1635_: *mut LeanObject,
) -> u8 {
    let mut v_state_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userClosedBody_1637_: u8 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_1636_ = lean_ctor_get(v_writer_1635_, 2);
                v_userClosedBody_1637_ = lean_ctor_get_uint8(
                    v_writer_1635_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                match lean_obj_tag(v_state_1636_) {
                    1 => {
                        v___x_1641_ = 1;
                        return v___x_1641_;
                    }
                    2 => {
                        v___x_1642_ = 1;
                        return v___x_1642_;
                    }
                    3 => {
                        if v_userClosedBody_1637_ == 0 {
                            v___x_1643_ = 1;
                            return v___x_1643_;
                        } else {
                            v___x_1644_ = 0;
                            return v___x_1644_;
                        }
                    }
                    4 => {
                        state = 1;
                        continue;
                    }
                    5 => {
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1645_ = 0;
                        return v___x_1645_;
                    }
                }
            }
            1 => {
                if v_userClosedBody_1637_ == 0 {
                    v___x_1639_ = 1;
                    return v___x_1639_;
                } else {
                    v___x_1640_ = 0;
                    return v___x_1640_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(
    mut v_writer_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1647_: u8 = 0;
    let mut v_r_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_1646_);
    lean_dec_ref(v_writer_1646_);
    v_r_1648_ = lean_box((v_res_1647_) as usize);
    return v_r_1648_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_canAcceptData(
    mut v_dir_1649_: u8,
    mut v_writer_1650_: *mut LeanObject,
) -> u8 {
    let mut v_state_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userClosedBody_1652_: u8 = 0;
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_state_1651_ = lean_ctor_get(v_writer_1650_, 2);
                v_userClosedBody_1652_ = lean_ctor_get_uint8(
                    v_writer_1650_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                match lean_obj_tag(v_state_1651_) {
                    1 => {
                        v___x_1656_ = 1;
                        return v___x_1656_;
                    }
                    2 => {
                        v___x_1657_ = 1;
                        return v___x_1657_;
                    }
                    3 => {
                        if v_userClosedBody_1652_ == 0 {
                            v___x_1658_ = 1;
                            return v___x_1658_;
                        } else {
                            v___x_1659_ = 0;
                            return v___x_1659_;
                        }
                    }
                    4 => {
                        state = 1;
                        continue;
                    }
                    5 => {
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1660_ = 0;
                        return v___x_1660_;
                    }
                }
            }
            1 => {
                if v_userClosedBody_1652_ == 0 {
                    v___x_1654_ = 1;
                    return v___x_1654_;
                } else {
                    v___x_1655_ = 0;
                    return v___x_1655_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(
    mut v_dir_1661_: *mut LeanObject,
    mut v_writer_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1663_: u8 = 0;
    let mut v_res_1664_: u8 = 0;
    let mut v_r_1665_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1663_ = (lean_unbox(v_dir_1661_) as u8);
    v_res_1664_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_1663_, v_writer_1662_);
    lean_dec_ref(v_writer_1662_);
    v_r_1665_ = lean_box((v_res_1664_) as usize);
    return v_r_1665_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_closeBody___redArg(
    mut v_writer_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_1672_: u8 = 0;
    let mut v_omitBody_1673_: u8 = 0;
    let mut v_userDataBytes_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1678_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_1667_ = lean_ctor_get(v_writer_1666_, 0);
                v_outputData_1668_ = lean_ctor_get(v_writer_1666_, 1);
                v_state_1669_ = lean_ctor_get(v_writer_1666_, 2);
                v_knownSize_1670_ = lean_ctor_get(v_writer_1666_, 3);
                v_messageHead_1671_ = lean_ctor_get(v_writer_1666_, 4);
                v_sentMessage_1672_ = lean_ctor_get_uint8(
                    v_writer_1666_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_omitBody_1673_ = lean_ctor_get_uint8(
                    v_writer_1666_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_1674_ = lean_ctor_get(v_writer_1666_, 5);
                v_isSharedCheck_1682_ = (!lean_is_exclusive(v_writer_1666_)) as u8;
                if v_isSharedCheck_1682_ == 0 {
                    v___x_1676_ = v_writer_1666_;
                    v_isShared_1677_ = v_isSharedCheck_1682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_1674_);
                    lean_inc(v_messageHead_1671_);
                    lean_inc(v_knownSize_1670_);
                    lean_inc(v_state_1669_);
                    lean_inc(v_outputData_1668_);
                    lean_inc(v_userData_1667_);
                    lean_dec(v_writer_1666_);
                    v___x_1676_ = lean_box(0);
                    v_isShared_1677_ = v_isSharedCheck_1682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1678_ = 1;
                if v_isShared_1677_ == 0 {
                    v___x_1680_ = v___x_1676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_userData_1667_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_outputData_1668_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_state_1669_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_knownSize_1670_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_messageHead_1671_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_userDataBytes_1674_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1681_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_1672_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1681_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_1673_,
                    );
                    v___x_1680_ = v_reuseFailAlloc_1681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1680_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    v___x_1678_,
                );
                return v___x_1680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_closeBody(
    mut v_dir_1683_: u8,
    mut v_writer_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_1690_: u8 = 0;
    let mut v_omitBody_1691_: u8 = 0;
    let mut v_userDataBytes_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_1685_ = lean_ctor_get(v_writer_1684_, 0);
                v_outputData_1686_ = lean_ctor_get(v_writer_1684_, 1);
                v_state_1687_ = lean_ctor_get(v_writer_1684_, 2);
                v_knownSize_1688_ = lean_ctor_get(v_writer_1684_, 3);
                v_messageHead_1689_ = lean_ctor_get(v_writer_1684_, 4);
                v_sentMessage_1690_ = lean_ctor_get_uint8(
                    v_writer_1684_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_omitBody_1691_ = lean_ctor_get_uint8(
                    v_writer_1684_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_1692_ = lean_ctor_get(v_writer_1684_, 5);
                v_isSharedCheck_1700_ = (!lean_is_exclusive(v_writer_1684_)) as u8;
                if v_isSharedCheck_1700_ == 0 {
                    v___x_1694_ = v_writer_1684_;
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_1692_);
                    lean_inc(v_messageHead_1689_);
                    lean_inc(v_knownSize_1688_);
                    lean_inc(v_state_1687_);
                    lean_inc(v_outputData_1686_);
                    lean_inc(v_userData_1685_);
                    lean_dec(v_writer_1684_);
                    v___x_1694_ = lean_box(0);
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1696_ = 1;
                if v_isShared_1695_ == 0 {
                    v___x_1698_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_userData_1685_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_outputData_1686_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_state_1687_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_knownSize_1688_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_messageHead_1689_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_userDataBytes_1692_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1699_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_1690_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1699_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_1691_,
                    );
                    v___x_1698_ = v_reuseFailAlloc_1699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1698_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    v___x_1696_,
                );
                return v___x_1698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_closeBody___boxed(
    mut v_dir_1701_: *mut LeanObject,
    mut v_writer_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1703_: u8 = 0;
    let mut v_res_1704_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1703_ = (lean_unbox(v_dir_1701_) as u8);
    v_res_1704_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_1703_, v_writer_1702_);
    return v_res_1704_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(
    mut v_writer_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_knownSize_1706_: *mut LeanObject = core::ptr::null_mut();
    v_knownSize_1706_ = lean_ctor_get(v_writer_1705_, 3);
    if lean_obj_tag(v_knownSize_1706_) == 1 {
        let mut v_val_1707_: *mut LeanObject = core::ptr::null_mut();
        v_val_1707_ = lean_ctor_get(v_knownSize_1706_, 0);
        lean_inc(v_val_1707_);
        return v_val_1707_;
    } else {
        let mut v_userClosedBody_1708_: u8 = 0;
        v_userClosedBody_1708_ = lean_ctor_get_uint8(
            v_writer_1705_,
            (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
        );
        if v_userClosedBody_1708_ == 0 {
            let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
            v___x_1709_ = lean_box(0);
            return v___x_1709_;
        } else {
            let mut v_userDataBytes_1710_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
            v_userDataBytes_1710_ = lean_ctor_get(v_writer_1705_, 5);
            lean_inc(v_userDataBytes_1710_);
            v___x_1711_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1711_, 0, v_userDataBytes_1710_);
            return v___x_1711_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(
    mut v_writer_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_1712_);
    lean_dec_ref(v_writer_1712_);
    return v_res_1713_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_determineTransferMode(
    mut v_dir_1714_: u8,
    mut v_writer_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(
    mut v_dir_1717_: *mut LeanObject,
    mut v_writer_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1719_: u8 = 0;
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1719_ = (lean_unbox(v_dir_1717_) as u8);
    v_res_1720_ =
        l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_1719_, v_writer_1718_);
    lean_dec_ref(v_writer_1718_);
    return v_res_1720_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(
    mut v_x1_1721_: *mut LeanObject,
    mut v_x2_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v_data_1723_ = lean_ctor_get(v_x2_1722_, 0);
    v___x_1724_ = lean_byte_array_size(v_data_1723_);
    v___x_1725_ = lean_nat_add(v_x1_1721_, v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(
    mut v_x1_1726_: *mut LeanObject,
    mut v_x2_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1728_: *mut LeanObject = core::ptr::null_mut();
    v_res_1728_ =
        l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_1726_, v_x2_1727_);
    lean_dec_ref(v_x2_1727_);
    lean_dec(v_x1_1726_);
    return v_res_1728_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_addUserData___redArg(
    mut v_data_1749_: *mut LeanObject,
    mut v_writer_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_1756_: u8 = 0;
    let mut v_userClosedBody_1757_: u8 = 0;
    let mut v_omitBody_1758_: u8 = 0;
    let mut v_userDataBytes_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: usize = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: usize = 0;
    let mut v___x_1776_: usize = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_1751_ = lean_ctor_get(v_writer_1750_, 0);
                v_outputData_1752_ = lean_ctor_get(v_writer_1750_, 1);
                v_state_1753_ = lean_ctor_get(v_writer_1750_, 2);
                v_knownSize_1754_ = lean_ctor_get(v_writer_1750_, 3);
                v_messageHead_1755_ = lean_ctor_get(v_writer_1750_, 4);
                v_sentMessage_1756_ = lean_ctor_get_uint8(
                    v_writer_1750_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_1757_ = lean_ctor_get_uint8(
                    v_writer_1750_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_1758_ = lean_ctor_get_uint8(
                    v_writer_1750_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_1759_ = lean_ctor_get(v_writer_1750_, 5);
                v___f_1765_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0;
                match lean_obj_tag(v_state_1753_) {
                    1 => {
                        lean_inc(v_state_1753_);
                        lean_inc(v_userDataBytes_1759_);
                        lean_inc(v_messageHead_1755_);
                        lean_inc(v_knownSize_1754_);
                        lean_inc_ref(v_outputData_1752_);
                        lean_inc_ref(v_userData_1751_);
                        lean_dec_ref(v_writer_1750_);
                        state = 2;
                        continue;
                    }
                    2 => {
                        lean_inc(v_state_1753_);
                        lean_inc(v_userDataBytes_1759_);
                        lean_inc(v_messageHead_1755_);
                        lean_inc(v_knownSize_1754_);
                        lean_inc_ref(v_outputData_1752_);
                        lean_inc_ref(v_userData_1751_);
                        lean_dec_ref(v_writer_1750_);
                        state = 2;
                        continue;
                    }
                    3 => {
                        if v_userClosedBody_1757_ == 0 {
                            lean_inc_ref(v_state_1753_);
                            lean_inc(v_userDataBytes_1759_);
                            lean_inc(v_messageHead_1755_);
                            lean_inc(v_knownSize_1754_);
                            lean_inc_ref(v_outputData_1752_);
                            lean_inc_ref(v_userData_1751_);
                            lean_dec_ref(v_writer_1750_);
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v_data_1749_);
                            return v_writer_1750_;
                        }
                    }
                    4 => {
                        state = 3;
                        continue;
                    }
                    5 => {
                        state = 3;
                        continue;
                    }
                    _ => {
                        lean_dec_ref(v_data_1749_);
                        return v_writer_1750_;
                    }
                }
            }
            1 => {
                v___x_1762_ = l_Array_append___redArg(v_userData_1751_, v_data_1749_);
                lean_dec_ref(v_data_1749_);
                v___x_1763_ = lean_nat_add(v_userDataBytes_1759_, v___y_1761_);
                lean_dec(v___y_1761_);
                lean_dec(v_userDataBytes_1759_);
                v___x_1764_ = lean_alloc_ctor(0, 6, (3) as u32);
                lean_ctor_set(v___x_1764_, 0, v___x_1762_);
                lean_ctor_set(v___x_1764_, 1, v_outputData_1752_);
                lean_ctor_set(v___x_1764_, 2, v_state_1753_);
                lean_ctor_set(v___x_1764_, 3, v_knownSize_1754_);
                lean_ctor_set(v___x_1764_, 4, v_messageHead_1755_);
                lean_ctor_set(v___x_1764_, 5, v___x_1763_);
                lean_ctor_set_uint8(
                    v___x_1764_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    v_sentMessage_1756_,
                );
                lean_ctor_set_uint8(
                    v___x_1764_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    v_userClosedBody_1757_,
                );
                lean_ctor_set_uint8(
                    v___x_1764_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                    v_omitBody_1758_,
                );
                return v___x_1764_;
            }
            2 => {
                v___x_1767_ = lean_unsigned_to_nat(0);
                v___x_1768_ = lean_array_get_size(v_data_1749_);
                v___x_1769_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10;
                v___x_1770_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
                if v___x_1770_ == 0 {
                    v___y_1761_ = v___x_1767_;
                    state = 1;
                    continue;
                } else {
                    v___x_1771_ = lean_nat_dec_le(v___x_1768_, v___x_1768_);
                    if v___x_1771_ == 0 {
                        if v___x_1770_ == 0 {
                            v___y_1761_ = v___x_1767_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1772_ = 0usize;
                            v___x_1773_ = lean_usize_of_nat(v___x_1768_);
                            lean_inc_ref(v_data_1749_);
                            v___x_1774_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1769_,
                                    v___f_1765_,
                                    v_data_1749_,
                                    v___x_1772_,
                                    v___x_1773_,
                                    v___x_1767_,
                                );
                            v___y_1761_ = v___x_1774_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1775_ = 0usize;
                        v___x_1776_ = lean_usize_of_nat(v___x_1768_);
                        lean_inc_ref(v_data_1749_);
                        v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_1769_,
                            v___f_1765_,
                            v_data_1749_,
                            v___x_1775_,
                            v___x_1776_,
                            v___x_1767_,
                        );
                        v___y_1761_ = v___x_1777_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v_userClosedBody_1757_ == 0 {
                    lean_inc(v_userDataBytes_1759_);
                    lean_inc(v_messageHead_1755_);
                    lean_inc(v_knownSize_1754_);
                    lean_inc(v_state_1753_);
                    lean_inc_ref(v_outputData_1752_);
                    lean_inc_ref(v_userData_1751_);
                    lean_dec_ref(v_writer_1750_);
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_data_1749_);
                    return v_writer_1750_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_addUserData(
    mut v_dir_1779_: u8,
    mut v_data_1780_: *mut LeanObject,
    mut v_writer_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_1787_: u8 = 0;
    let mut v_userClosedBody_1788_: u8 = 0;
    let mut v_omitBody_1789_: u8 = 0;
    let mut v_userDataBytes_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: u8 = 0;
    let mut v___x_1803_: usize = 0;
    let mut v___x_1804_: usize = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: usize = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_1782_ = lean_ctor_get(v_writer_1781_, 0);
                v_outputData_1783_ = lean_ctor_get(v_writer_1781_, 1);
                v_state_1784_ = lean_ctor_get(v_writer_1781_, 2);
                v_knownSize_1785_ = lean_ctor_get(v_writer_1781_, 3);
                v_messageHead_1786_ = lean_ctor_get(v_writer_1781_, 4);
                v_sentMessage_1787_ = lean_ctor_get_uint8(
                    v_writer_1781_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_1788_ = lean_ctor_get_uint8(
                    v_writer_1781_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_1789_ = lean_ctor_get_uint8(
                    v_writer_1781_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_1790_ = lean_ctor_get(v_writer_1781_, 5);
                v___f_1796_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0;
                match lean_obj_tag(v_state_1784_) {
                    1 => {
                        lean_inc(v_state_1784_);
                        lean_inc(v_userDataBytes_1790_);
                        lean_inc(v_messageHead_1786_);
                        lean_inc(v_knownSize_1785_);
                        lean_inc_ref(v_outputData_1783_);
                        lean_inc_ref(v_userData_1782_);
                        lean_dec_ref(v_writer_1781_);
                        state = 2;
                        continue;
                    }
                    2 => {
                        lean_inc(v_state_1784_);
                        lean_inc(v_userDataBytes_1790_);
                        lean_inc(v_messageHead_1786_);
                        lean_inc(v_knownSize_1785_);
                        lean_inc_ref(v_outputData_1783_);
                        lean_inc_ref(v_userData_1782_);
                        lean_dec_ref(v_writer_1781_);
                        state = 2;
                        continue;
                    }
                    3 => {
                        if v_userClosedBody_1788_ == 0 {
                            lean_inc_ref(v_state_1784_);
                            lean_inc(v_userDataBytes_1790_);
                            lean_inc(v_messageHead_1786_);
                            lean_inc(v_knownSize_1785_);
                            lean_inc_ref(v_outputData_1783_);
                            lean_inc_ref(v_userData_1782_);
                            lean_dec_ref(v_writer_1781_);
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v_data_1780_);
                            return v_writer_1781_;
                        }
                    }
                    4 => {
                        state = 3;
                        continue;
                    }
                    5 => {
                        state = 3;
                        continue;
                    }
                    _ => {
                        lean_dec_ref(v_data_1780_);
                        return v_writer_1781_;
                    }
                }
            }
            1 => {
                v___x_1793_ = l_Array_append___redArg(v_userData_1782_, v_data_1780_);
                lean_dec_ref(v_data_1780_);
                v___x_1794_ = lean_nat_add(v_userDataBytes_1790_, v___y_1792_);
                lean_dec(v___y_1792_);
                lean_dec(v_userDataBytes_1790_);
                v___x_1795_ = lean_alloc_ctor(0, 6, (3) as u32);
                lean_ctor_set(v___x_1795_, 0, v___x_1793_);
                lean_ctor_set(v___x_1795_, 1, v_outputData_1783_);
                lean_ctor_set(v___x_1795_, 2, v_state_1784_);
                lean_ctor_set(v___x_1795_, 3, v_knownSize_1785_);
                lean_ctor_set(v___x_1795_, 4, v_messageHead_1786_);
                lean_ctor_set(v___x_1795_, 5, v___x_1794_);
                lean_ctor_set_uint8(
                    v___x_1795_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    v_sentMessage_1787_,
                );
                lean_ctor_set_uint8(
                    v___x_1795_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    v_userClosedBody_1788_,
                );
                lean_ctor_set_uint8(
                    v___x_1795_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                    v_omitBody_1789_,
                );
                return v___x_1795_;
            }
            2 => {
                v___x_1798_ = lean_unsigned_to_nat(0);
                v___x_1799_ = lean_array_get_size(v_data_1780_);
                v___x_1800_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10;
                v___x_1801_ = lean_nat_dec_lt(v___x_1798_, v___x_1799_);
                if v___x_1801_ == 0 {
                    v___y_1792_ = v___x_1798_;
                    state = 1;
                    continue;
                } else {
                    v___x_1802_ = lean_nat_dec_le(v___x_1799_, v___x_1799_);
                    if v___x_1802_ == 0 {
                        if v___x_1801_ == 0 {
                            v___y_1792_ = v___x_1798_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1803_ = 0usize;
                            v___x_1804_ = lean_usize_of_nat(v___x_1799_);
                            lean_inc_ref(v_data_1780_);
                            v___x_1805_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1800_,
                                    v___f_1796_,
                                    v_data_1780_,
                                    v___x_1803_,
                                    v___x_1804_,
                                    v___x_1798_,
                                );
                            v___y_1792_ = v___x_1805_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1806_ = 0usize;
                        v___x_1807_ = lean_usize_of_nat(v___x_1799_);
                        lean_inc_ref(v_data_1780_);
                        v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_1800_,
                            v___f_1796_,
                            v_data_1780_,
                            v___x_1806_,
                            v___x_1807_,
                            v___x_1798_,
                        );
                        v___y_1792_ = v___x_1808_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v_userClosedBody_1788_ == 0 {
                    lean_inc(v_userDataBytes_1790_);
                    lean_inc(v_messageHead_1786_);
                    lean_inc(v_knownSize_1785_);
                    lean_inc(v_state_1784_);
                    lean_inc_ref(v_outputData_1783_);
                    lean_inc_ref(v_userData_1782_);
                    lean_dec_ref(v_writer_1781_);
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_data_1780_);
                    return v_writer_1781_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_addUserData___boxed(
    mut v_dir_1810_: *mut LeanObject,
    mut v_data_1811_: *mut LeanObject,
    mut v_writer_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_1813_: u8 = 0;
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_1813_ = (lean_unbox(v_dir_1810_) as u8);
    v_res_1814_ =
        l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_1813_, v_data_1811_, v_writer_1812_);
    return v_res_1814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(
    mut v_limitSize_1815_: *mut LeanObject,
    mut v_as_1816_: *mut LeanObject,
    mut v_i_1817_: usize,
    mut v_stop_1818_: usize,
    mut v_b_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: usize = 0;
    let mut v___x_1823_: usize = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v_snd_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v_fst_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u8 = 0;
    let mut v_data_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingChunk_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v_dataPart_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1825_ = lean_usize_dec_eq(v_i_1817_, v_stop_1818_);
                if v___x_1825_ == 0 {
                    v_snd_1826_ = lean_ctor_get(v_b_1819_, 1);
                    v_fst_1827_ = lean_ctor_get(v_b_1819_, 0);
                    v_isSharedCheck_1883_ = (!lean_is_exclusive(v_b_1819_)) as u8;
                    if v_isSharedCheck_1883_ == 0 {
                        v___x_1829_ = v_b_1819_;
                        v_isShared_1830_ = v_isSharedCheck_1883_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1826_);
                        lean_inc(v_fst_1827_);
                        lean_dec(v_b_1819_);
                        v___x_1829_ = lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1883_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_1819_;
                }
            }
            1 => {
                v___x_1822_ = 1usize;
                v___x_1823_ = lean_usize_add(v_i_1817_, v___x_1822_);
                v_i_1817_ = v___x_1823_;
                v_b_1819_ = v___y_1821_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_1831_ = lean_ctor_get(v_snd_1826_, 0);
                v_snd_1832_ = lean_ctor_get(v_snd_1826_, 1);
                v_isSharedCheck_1882_ = (!lean_is_exclusive(v_snd_1826_)) as u8;
                if v_isSharedCheck_1882_ == 0 {
                    v___x_1834_ = v_snd_1826_;
                    v_isShared_1835_ = v_isSharedCheck_1882_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_1832_);
                    lean_inc(v_fst_1831_);
                    lean_dec(v_snd_1826_);
                    v___x_1834_ = lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1836_ = lean_array_uget(v_as_1816_, v_i_1817_);
                v___x_1837_ = lean_nat_dec_le(v_limitSize_1815_, v_snd_1832_);
                if v___x_1837_ == 0 {
                    v_data_1838_ = lean_ctor_get(v___x_1836_, 0);
                    v_extensions_1839_ = lean_ctor_get(v___x_1836_, 1);
                    v_isSharedCheck_1874_ = (!lean_is_exclusive(v___x_1836_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1841_ = v___x_1836_;
                        v_isShared_1842_ = v_isSharedCheck_1874_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_extensions_1839_);
                        lean_inc(v_data_1838_);
                        lean_dec(v___x_1836_);
                        v___x_1841_ = lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1874_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1875_ = lean_array_push(v_fst_1831_, v___x_1836_);
                    if v_isShared_1835_ == 0 {
                        lean_ctor_set(v___x_1834_, 0, v___x_1875_);
                        v___x_1877_ = v___x_1834_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1875_);
                        lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_snd_1832_);
                        v___x_1877_ = v_reuseFailAlloc_1881_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1843_ = lean_unsigned_to_nat(0);
                v_remaining_1844_ = lean_nat_sub(v_limitSize_1815_, v_snd_1832_);
                v___x_1845_ = lean_byte_array_size(v_data_1838_);
                v___x_1873_ = lean_nat_dec_le(v___x_1845_, v_remaining_1844_);
                if v___x_1873_ == 0 {
                    v___y_1869_ = v_remaining_1844_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_remaining_1844_);
                    v___y_1869_ = v___x_1845_;
                    state = 11;
                    continue;
                }
            }
            5 => {
                v_size_1849_ = lean_nat_add(v_snd_1832_, v___y_1847_);
                lean_dec(v_snd_1832_);
                v___x_1850_ = lean_nat_dec_lt(v___y_1847_, v___x_1845_);
                if v___x_1850_ == 0 {
                    lean_dec(v___y_1847_);
                    lean_del_object(v___x_1841_);
                    lean_dec_ref(v_extensions_1839_);
                    lean_dec_ref(v_data_1838_);
                    if v_isShared_1835_ == 0 {
                        lean_ctor_set(v___x_1834_, 1, v_size_1849_);
                        v___x_1852_ = v___x_1834_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_fst_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_size_1849_);
                        v___x_1852_ = v_reuseFailAlloc_1856_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1857_ = l_ByteArray_extract(v_data_1838_, v___y_1847_, v___x_1845_);
                    lean_dec_ref(v_data_1838_);
                    if v_isShared_1842_ == 0 {
                        lean_ctor_set(v___x_1841_, 0, v___x_1857_);
                        v_pendingChunk_1859_ = v___x_1841_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1857_);
                        lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_extensions_1839_);
                        v_pendingChunk_1859_ = v_reuseFailAlloc_1867_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1830_ == 0 {
                    lean_ctor_set(v___x_1829_, 1, v___x_1852_);
                    lean_ctor_set(v___x_1829_, 0, v___y_1848_);
                    v___x_1854_ = v___x_1829_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___y_1848_);
                    lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1852_);
                    v___x_1854_ = v_reuseFailAlloc_1855_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1821_ = v___x_1854_;
                state = 1;
                continue;
            }
            8 => {
                v___x_1860_ = lean_array_push(v_fst_1831_, v_pendingChunk_1859_);
                if v_isShared_1835_ == 0 {
                    lean_ctor_set(v___x_1834_, 1, v_size_1849_);
                    lean_ctor_set(v___x_1834_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1834_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_size_1849_);
                    v___x_1862_ = v_reuseFailAlloc_1866_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1830_ == 0 {
                    lean_ctor_set(v___x_1829_, 1, v___x_1862_);
                    lean_ctor_set(v___x_1829_, 0, v___y_1848_);
                    v___x_1864_ = v___x_1829_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___y_1848_);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1862_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1821_ = v___x_1864_;
                state = 1;
                continue;
            }
            11 => {
                v___x_1870_ = lean_nat_dec_eq(v___y_1869_, v___x_1843_);
                if v___x_1870_ == 0 {
                    v_dataPart_1871_ = l_ByteArray_extract(v_data_1838_, v___x_1843_, v___y_1869_);
                    v___x_1872_ = lean_array_push(v_fst_1827_, v_dataPart_1871_);
                    v___y_1847_ = v___y_1869_;
                    v___y_1848_ = v___x_1872_;
                    state = 5;
                    continue;
                } else {
                    v___y_1847_ = v___y_1869_;
                    v___y_1848_ = v_fst_1827_;
                    state = 5;
                    continue;
                }
            }
            12 => {
                if v_isShared_1830_ == 0 {
                    lean_ctor_set(v___x_1829_, 1, v___x_1877_);
                    v___x_1879_ = v___x_1829_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_fst_1827_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_1821_ = v___x_1879_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(
    mut v_limitSize_1884_: *mut LeanObject,
    mut v_as_1885_: *mut LeanObject,
    mut v_i_1886_: *mut LeanObject,
    mut v_stop_1887_: *mut LeanObject,
    mut v_b_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1889_: usize = 0;
    let mut v_stop_boxed_1890_: usize = 0;
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
    lean_dec(v_i_1886_);
    v_stop_boxed_1890_ = lean_unbox_usize(v_stop_1887_);
    lean_dec(v_stop_1887_);
    v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_1884_, v_as_1885_, v_i_boxed_1889_, v_stop_boxed_1890_, v_b_1888_);
    lean_dec_ref(v_as_1885_);
    lean_dec(v_limitSize_1884_);
    return v_res_1891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(
    mut v_as_1892_: *mut LeanObject,
    mut v_i_1893_: usize,
    mut v_stop_1894_: usize,
    mut v_b_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1896_ = lean_usize_dec_eq(v_i_1893_, v_stop_1894_);
                if v___x_1896_ == 0 {
                    v___x_1897_ = lean_array_uget_borrowed(v_as_1892_, v_i_1893_);
                    v___x_1898_ = lean_byte_array_size(v___x_1897_);
                    v___x_1899_ = lean_nat_add(v_b_1895_, v___x_1898_);
                    lean_dec(v_b_1895_);
                    v___x_1900_ = 1usize;
                    v___x_1901_ = lean_usize_add(v_i_1893_, v___x_1900_);
                    v_i_1893_ = v___x_1901_;
                    v_b_1895_ = v___x_1899_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1895_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(
    mut v_as_1903_: *mut LeanObject,
    mut v_i_1904_: *mut LeanObject,
    mut v_stop_1905_: *mut LeanObject,
    mut v_b_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1907_: usize = 0;
    let mut v_stop_boxed_1908_: usize = 0;
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1907_ = lean_unbox_usize(v_i_1904_);
    lean_dec(v_i_1904_);
    v_stop_boxed_1908_ = lean_unbox_usize(v_stop_1905_);
    lean_dec(v_stop_1905_);
    v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_1903_, v_i_boxed_1907_, v_stop_boxed_1908_, v_b_1906_);
    lean_dec_ref(v_as_1903_);
    return v_res_1909_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(
    mut v_writer_1918_: *mut LeanObject,
    mut v_limitSize_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: u8 = 0;
    let mut v___y_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: u8 = 0;
    let mut v___y_1927_: u8 = 0;
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v_data_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v_userData_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_1960_: u8 = 0;
    let mut v_userClosedBody_1961_: u8 = 0;
    let mut v_omitBody_1962_: u8 = 0;
    let mut v_userDataBytes_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: usize = 0;
    let mut v___x_1975_: usize = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: usize = 0;
    let mut v___x_1979_: usize = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: u8 = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: usize = 0;
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_1955_ = lean_ctor_get(v_writer_1918_, 0);
                v_outputData_1956_ = lean_ctor_get(v_writer_1918_, 1);
                v_state_1957_ = lean_ctor_get(v_writer_1918_, 2);
                v_knownSize_1958_ = lean_ctor_get(v_writer_1918_, 3);
                v_messageHead_1959_ = lean_ctor_get(v_writer_1918_, 4);
                v_sentMessage_1960_ = lean_ctor_get_uint8(
                    v_writer_1918_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_1961_ = lean_ctor_get_uint8(
                    v_writer_1918_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_1962_ = lean_ctor_get_uint8(
                    v_writer_1918_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_1963_ = lean_ctor_get(v_writer_1918_, 5);
                v___x_1988_ = lean_array_get_size(v_userData_1955_);
                v___x_1989_ = lean_unsigned_to_nat(0);
                v___x_1990_ = lean_nat_dec_eq(v___x_1988_, v___x_1989_);
                if v___x_1990_ == 0 {
                    lean_inc(v_userDataBytes_1963_);
                    lean_inc(v_messageHead_1959_);
                    lean_inc(v_knownSize_1958_);
                    lean_inc(v_state_1957_);
                    lean_inc_ref(v_outputData_1956_);
                    lean_inc_ref(v_userData_1955_);
                    lean_dec_ref(v_writer_1918_);
                    v___x_1991_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0;
                    v___x_1992_ = lean_nat_dec_lt(v___x_1989_, v___x_1988_);
                    if v___x_1992_ == 0 {
                        lean_dec_ref(v_userData_1955_);
                        v_fst_1965_ = v___x_1991_;
                        v_fst_1966_ = v___x_1991_;
                        v_snd_1967_ = v___x_1989_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1993_ =
                            l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2;
                        v___x_1994_ = lean_nat_dec_le(v___x_1988_, v___x_1988_);
                        if v___x_1994_ == 0 {
                            if v___x_1992_ == 0 {
                                lean_dec_ref(v_userData_1955_);
                                v_fst_1965_ = v___x_1991_;
                                v_fst_1966_ = v___x_1991_;
                                v_snd_1967_ = v___x_1989_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1995_ = 0usize;
                                v___x_1996_ = lean_usize_of_nat(v___x_1988_);
                                v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_1919_, v_userData_1955_, v___x_1995_, v___x_1996_, v___x_1993_);
                                lean_dec_ref(v_userData_1955_);
                                v___y_1983_ = v___x_1997_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_1998_ = 0usize;
                            v___x_1999_ = lean_usize_of_nat(v___x_1988_);
                            v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_1919_, v_userData_1955_, v___x_1998_, v___x_1999_, v___x_1993_);
                            lean_dec_ref(v_userData_1955_);
                            v___y_1983_ = v___x_2000_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2001_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2001_, 0, v_writer_1918_);
                    lean_ctor_set(v___x_2001_, 1, v_limitSize_1919_);
                    return v___x_2001_;
                }
            }
            1 => {
                v_data_1932_ = lean_ctor_get(v___y_1928_, 0);
                v_size_1933_ = lean_ctor_get(v___y_1928_, 1);
                v_isSharedCheck_1954_ = (!lean_is_exclusive(v___y_1928_)) as u8;
                if v_isSharedCheck_1954_ == 0 {
                    v___x_1935_ = v___y_1928_;
                    v_isShared_1936_ = v_isSharedCheck_1954_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_size_1933_);
                    lean_inc(v_data_1932_);
                    lean_dec(v___y_1928_);
                    v___x_1935_ = lean_box(0);
                    v_isShared_1936_ = v_isSharedCheck_1954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_data_1937_ = lean_ctor_get(v___y_1931_, 0);
                v_size_1938_ = lean_ctor_get(v___y_1931_, 1);
                v_isSharedCheck_1953_ = (!lean_is_exclusive(v___y_1931_)) as u8;
                if v_isSharedCheck_1953_ == 0 {
                    v___x_1940_ = v___y_1931_;
                    v_isShared_1941_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_size_1938_);
                    lean_inc(v_data_1937_);
                    lean_dec(v___y_1931_);
                    v___x_1940_ = lean_box(0);
                    v_isShared_1941_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1942_ = l_Array_append___redArg(v_data_1932_, v_data_1937_);
                lean_dec_ref(v_data_1937_);
                v___x_1943_ = lean_nat_add(v_size_1933_, v_size_1938_);
                lean_dec(v_size_1938_);
                lean_dec(v_size_1933_);
                if v_isShared_1941_ == 0 {
                    lean_ctor_set(v___x_1940_, 1, v___x_1943_);
                    lean_ctor_set(v___x_1940_, 0, v___x_1942_);
                    v_outputData_1945_ = v___x_1940_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1942_);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1943_);
                    v_outputData_1945_ = v_reuseFailAlloc_1952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_remaining_1946_ = lean_nat_sub(v_limitSize_1919_, v___y_1930_);
                lean_dec(v_limitSize_1919_);
                v___x_1947_ = lean_nat_sub(v___y_1923_, v___y_1930_);
                lean_dec(v___y_1930_);
                lean_dec(v___y_1923_);
                v___x_1948_ = lean_alloc_ctor(0, 6, (3) as u32);
                lean_ctor_set(v___x_1948_, 0, v___y_1925_);
                lean_ctor_set(v___x_1948_, 1, v_outputData_1945_);
                lean_ctor_set(v___x_1948_, 2, v___y_1924_);
                lean_ctor_set(v___x_1948_, 3, v___y_1929_);
                lean_ctor_set(v___x_1948_, 4, v___y_1921_);
                lean_ctor_set(v___x_1948_, 5, v___x_1947_);
                lean_ctor_set_uint8(
                    v___x_1948_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    v___y_1927_,
                );
                lean_ctor_set_uint8(
                    v___x_1948_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    v___y_1922_,
                );
                lean_ctor_set_uint8(
                    v___x_1948_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                    v___y_1926_,
                );
                if v_isShared_1936_ == 0 {
                    lean_ctor_set(v___x_1935_, 1, v_remaining_1946_);
                    lean_ctor_set(v___x_1935_, 0, v___x_1948_);
                    v___x_1950_ = v___x_1935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_remaining_1946_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1950_;
            }
            6 => {
                v___x_1968_ = lean_unsigned_to_nat(0);
                v___x_1969_ = lean_array_get_size(v_fst_1965_);
                v___x_1970_ = lean_nat_dec_lt(v___x_1968_, v___x_1969_);
                if v___x_1970_ == 0 {
                    v___x_1971_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1971_, 0, v_fst_1965_);
                    lean_ctor_set(v___x_1971_, 1, v___x_1968_);
                    v___y_1921_ = v_messageHead_1959_;
                    v___y_1922_ = v_userClosedBody_1961_;
                    v___y_1923_ = v_userDataBytes_1963_;
                    v___y_1924_ = v_state_1957_;
                    v___y_1925_ = v_fst_1966_;
                    v___y_1926_ = v_omitBody_1962_;
                    v___y_1927_ = v_sentMessage_1960_;
                    v___y_1928_ = v_outputData_1956_;
                    v___y_1929_ = v_knownSize_1958_;
                    v___y_1930_ = v_snd_1967_;
                    v___y_1931_ = v___x_1971_;
                    state = 1;
                    continue;
                } else {
                    v___x_1972_ = lean_nat_dec_le(v___x_1969_, v___x_1969_);
                    if v___x_1972_ == 0 {
                        if v___x_1970_ == 0 {
                            v___x_1973_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1973_, 0, v_fst_1965_);
                            lean_ctor_set(v___x_1973_, 1, v___x_1968_);
                            v___y_1921_ = v_messageHead_1959_;
                            v___y_1922_ = v_userClosedBody_1961_;
                            v___y_1923_ = v_userDataBytes_1963_;
                            v___y_1924_ = v_state_1957_;
                            v___y_1925_ = v_fst_1966_;
                            v___y_1926_ = v_omitBody_1962_;
                            v___y_1927_ = v_sentMessage_1960_;
                            v___y_1928_ = v_outputData_1956_;
                            v___y_1929_ = v_knownSize_1958_;
                            v___y_1930_ = v_snd_1967_;
                            v___y_1931_ = v___x_1973_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1974_ = 0usize;
                            v___x_1975_ = lean_usize_of_nat(v___x_1969_);
                            v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_1965_, v___x_1974_, v___x_1975_, v___x_1968_);
                            v___x_1977_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1977_, 0, v_fst_1965_);
                            lean_ctor_set(v___x_1977_, 1, v___x_1976_);
                            v___y_1921_ = v_messageHead_1959_;
                            v___y_1922_ = v_userClosedBody_1961_;
                            v___y_1923_ = v_userDataBytes_1963_;
                            v___y_1924_ = v_state_1957_;
                            v___y_1925_ = v_fst_1966_;
                            v___y_1926_ = v_omitBody_1962_;
                            v___y_1927_ = v_sentMessage_1960_;
                            v___y_1928_ = v_outputData_1956_;
                            v___y_1929_ = v_knownSize_1958_;
                            v___y_1930_ = v_snd_1967_;
                            v___y_1931_ = v___x_1977_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1978_ = 0usize;
                        v___x_1979_ = lean_usize_of_nat(v___x_1969_);
                        v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_1965_, v___x_1978_, v___x_1979_, v___x_1968_);
                        v___x_1981_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1981_, 0, v_fst_1965_);
                        lean_ctor_set(v___x_1981_, 1, v___x_1980_);
                        v___y_1921_ = v_messageHead_1959_;
                        v___y_1922_ = v_userClosedBody_1961_;
                        v___y_1923_ = v_userDataBytes_1963_;
                        v___y_1924_ = v_state_1957_;
                        v___y_1925_ = v_fst_1966_;
                        v___y_1926_ = v_omitBody_1962_;
                        v___y_1927_ = v_sentMessage_1960_;
                        v___y_1928_ = v_outputData_1956_;
                        v___y_1929_ = v_knownSize_1958_;
                        v___y_1930_ = v_snd_1967_;
                        v___y_1931_ = v___x_1981_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                v_snd_1984_ = lean_ctor_get(v___y_1983_, 1);
                lean_inc(v_snd_1984_);
                v_fst_1985_ = lean_ctor_get(v___y_1983_, 0);
                lean_inc(v_fst_1985_);
                lean_dec_ref(v___y_1983_);
                v_fst_1986_ = lean_ctor_get(v_snd_1984_, 0);
                lean_inc(v_fst_1986_);
                v_snd_1987_ = lean_ctor_get(v_snd_1984_, 1);
                lean_inc(v_snd_1987_);
                lean_dec(v_snd_1984_);
                v_fst_1965_ = v_fst_1985_;
                v_fst_1966_ = v_fst_1986_;
                v_snd_1967_ = v_snd_1987_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFixedBody(
    mut v_dir_2002_: u8,
    mut v_writer_2003_: *mut LeanObject,
    mut v_limitSize_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v___x_2005_ =
        l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_2003_, v_limitSize_2004_);
    return v___x_2005_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(
    mut v_dir_2006_: *mut LeanObject,
    mut v_writer_2007_: *mut LeanObject,
    mut v_limitSize_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2009_: u8 = 0;
    let mut v_res_2010_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2009_ = (lean_unbox(v_dir_2006_) as u8);
    v_res_2010_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(
        v_dir_boxed_2009_,
        v_writer_2007_,
        v_limitSize_2008_,
    );
    return v_res_2010_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(
    mut v_as_2011_: *mut LeanObject,
    mut v_i_2012_: usize,
    mut v_stop_2013_: usize,
    mut v_b_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: usize = 0;
    let mut v___x_2018_: usize = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2020_ = lean_usize_dec_eq(v_i_2012_, v_stop_2013_);
                if v___x_2020_ == 0 {
                    v___x_2021_ = lean_array_uget_borrowed(v_as_2011_, v_i_2012_);
                    v_data_2022_ = lean_ctor_get(v___x_2021_, 0);
                    v___x_2023_ = l_ByteArray_isEmpty(v_data_2022_);
                    if v___x_2023_ == 0 {
                        lean_inc(v___x_2021_);
                        v___x_2024_ = lean_array_push(v_b_2014_, v___x_2021_);
                        v___y_2016_ = v___x_2024_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2016_ = v_b_2014_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2014_;
                }
            }
            1 => {
                v___x_2017_ = 1usize;
                v___x_2018_ = lean_usize_add(v_i_2012_, v___x_2017_);
                v_i_2012_ = v___x_2018_;
                v_b_2014_ = v___y_2016_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(
    mut v_as_2025_: *mut LeanObject,
    mut v_i_2026_: *mut LeanObject,
    mut v_stop_2027_: *mut LeanObject,
    mut v_b_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2029_: usize = 0;
    let mut v_stop_boxed_2030_: usize = 0;
    let mut v_res_2031_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
    lean_dec(v_i_2026_);
    v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2027_);
    lean_dec(v_stop_2027_);
    v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_2025_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2028_);
    lean_dec_ref(v_as_2025_);
    return v_res_2031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(
    mut v_sz_2032_: usize,
    mut v_i_2033_: usize,
    mut v_bs_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2035_: u8 = 0;
    let mut v_v_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u32 = 0;
    let mut v___x_2040_: u8 = 0;
    let mut v___x_2041_: usize = 0;
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2035_ = lean_usize_dec_lt(v_i_2033_, v_sz_2032_);
                if v___x_2035_ == 0 {
                    return v_bs_2034_;
                } else {
                    v_v_2036_ = lean_array_uget(v_bs_2034_, v_i_2033_);
                    v___x_2037_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2038_ = lean_array_uset(v_bs_2034_, v_i_2033_, v___x_2037_);
                    v___x_2039_ = lean_unbox_uint32(v_v_2036_);
                    lean_dec(v_v_2036_);
                    v___x_2040_ = lean_uint32_to_uint8(v___x_2039_);
                    v___x_2041_ = 1usize;
                    v___x_2042_ = lean_usize_add(v_i_2033_, v___x_2041_);
                    v___x_2043_ = lean_box((v___x_2040_) as usize);
                    v___x_2044_ = lean_array_uset(v_bs_x27_2038_, v_i_2033_, v___x_2043_);
                    v_i_2033_ = v___x_2042_;
                    v_bs_2034_ = v___x_2044_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(
    mut v_sz_2046_: *mut LeanObject,
    mut v_i_2047_: *mut LeanObject,
    mut v_bs_2048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2049_: usize = 0;
    let mut v_i_boxed_2050_: usize = 0;
    let mut v_res_2051_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2046_);
    lean_dec(v_sz_2046_);
    v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
    lean_dec(v_i_2047_);
    v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_2049_, v_i_boxed_2050_, v_bs_2048_);
    return v_res_2051_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(
    mut v_as_2054_: *mut LeanObject,
    mut v_i_2055_: usize,
    mut v_stop_2056_: usize,
    mut v_b_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: usize = 0;
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2063_ = lean_usize_dec_eq(v_i_2055_, v_stop_2056_);
                if v___x_2063_ == 0 {
                    v___x_2064_ = lean_array_uget_borrowed(v_as_2054_, v_i_2055_);
                    v_fst_2065_ = lean_ctor_get(v___x_2064_, 0);
                    v_snd_2066_ = lean_ctor_get(v___x_2064_, 1);
                    v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0;
                    v___x_2068_ = lean_string_append(v_b_2057_, v___x_2067_);
                    v___x_2069_ = lean_string_append(v___x_2068_, v_fst_2065_);
                    if lean_obj_tag(v_snd_2066_) == 0 {
                        v___y_2059_ = v___x_2069_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2070_ = lean_ctor_get(v_snd_2066_, 0);
                        v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1;
                        lean_inc(v_val_2070_);
                        v___x_2072_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_2070_);
                        v___x_2073_ = lean_string_append(v___x_2071_, v___x_2072_);
                        lean_dec_ref(v___x_2072_);
                        v___x_2074_ = lean_string_append(v___x_2069_, v___x_2073_);
                        lean_dec_ref(v___x_2073_);
                        v___y_2059_ = v___x_2074_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2057_;
                }
            }
            1 => {
                v___x_2060_ = 1usize;
                v___x_2061_ = lean_usize_add(v_i_2055_, v___x_2060_);
                v_i_2055_ = v___x_2061_;
                v_b_2057_ = v___y_2059_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(
    mut v_as_2075_: *mut LeanObject,
    mut v_i_2076_: *mut LeanObject,
    mut v_stop_2077_: *mut LeanObject,
    mut v_b_2078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2079_: usize = 0;
    let mut v_stop_boxed_2080_: usize = 0;
    let mut v_res_2081_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
    lean_dec(v_i_2076_);
    v_stop_boxed_2080_ = lean_unbox_usize(v_stop_2077_);
    lean_dec(v_stop_2077_);
    v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_2075_, v_i_boxed_2079_, v_stop_boxed_2080_, v_b_2078_);
    lean_dec_ref(v_as_2075_);
    return v_res_2081_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0;
    v___x_2084_ = lean_string_to_utf8(v___x_2083_);
    return v___x_2084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(
    mut v_as_2086_: *mut LeanObject,
    mut v_i_2087_: usize,
    mut v_stop_2088_: usize,
    mut v_b_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: usize = 0;
    let mut v___x_2104_: usize = 0;
    let mut v_reuseFailAlloc_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v_chunkLen_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2121_: usize = 0;
    let mut v___x_2122_: usize = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: usize = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: usize = 0;
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: usize = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = lean_usize_dec_eq(v_i_2087_, v_stop_2088_);
                if v___x_2108_ == 0 {
                    v___x_2109_ = lean_array_uget(v_as_2086_, v_i_2087_);
                    v_data_2110_ = lean_ctor_get(v___x_2109_, 0);
                    v_extensions_2111_ = lean_ctor_get(v___x_2109_, 1);
                    v_isSharedCheck_2165_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2165_ == 0 {
                        v___x_2113_ = v___x_2109_;
                        v_isShared_2114_ = v_isSharedCheck_2165_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_extensions_2111_);
                        lean_inc(v_data_2110_);
                        lean_dec(v___x_2109_);
                        v___x_2113_ = lean_box(0);
                        v_isShared_2114_ = v_isSharedCheck_2165_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v_b_2089_;
                }
            }
            1 => {
                v_data_2092_ = lean_ctor_get(v_b_2089_, 0);
                lean_inc_ref(v_data_2092_);
                v_size_2093_ = lean_ctor_get(v_b_2089_, 1);
                lean_inc(v_size_2093_);
                lean_dec_ref(v_b_2089_);
                v_data_2094_ = lean_ctor_get(v___y_2091_, 0);
                v_size_2095_ = lean_ctor_get(v___y_2091_, 1);
                v_isSharedCheck_2107_ = (!lean_is_exclusive(v___y_2091_)) as u8;
                if v_isSharedCheck_2107_ == 0 {
                    v___x_2097_ = v___y_2091_;
                    v_isShared_2098_ = v_isSharedCheck_2107_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_size_2095_);
                    lean_inc(v_data_2094_);
                    lean_dec(v___y_2091_);
                    v___x_2097_ = lean_box(0);
                    v_isShared_2098_ = v_isSharedCheck_2107_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2099_ = l_Array_append___redArg(v_data_2092_, v_data_2094_);
                lean_dec_ref(v_data_2094_);
                v___x_2100_ = lean_nat_add(v_size_2093_, v_size_2095_);
                lean_dec(v_size_2095_);
                lean_dec(v_size_2093_);
                if v_isShared_2098_ == 0 {
                    lean_ctor_set(v___x_2097_, 1, v___x_2100_);
                    lean_ctor_set(v___x_2097_, 0, v___x_2099_);
                    v___x_2102_ = v___x_2097_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2100_);
                    v___x_2102_ = v_reuseFailAlloc_2106_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2103_ = 1usize;
                v___x_2104_ = lean_usize_add(v_i_2087_, v___x_2103_);
                v_i_2087_ = v___x_2104_;
                v_b_2089_ = v___x_2102_;
                state = 0;
                continue;
            }
            4 => {
                v_chunkLen_2115_ = lean_byte_array_size(v_data_2110_);
                v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2;
                v___x_2155_ = lean_unsigned_to_nat(0);
                v___x_2156_ = lean_array_get_size(v_extensions_2111_);
                v___x_2157_ = lean_nat_dec_lt(v___x_2155_, v___x_2156_);
                if v___x_2157_ == 0 {
                    lean_dec_ref(v_extensions_2111_);
                    v___y_2117_ = v___x_2154_;
                    state = 5;
                    continue;
                } else {
                    v___x_2158_ = lean_nat_dec_le(v___x_2156_, v___x_2156_);
                    if v___x_2158_ == 0 {
                        if v___x_2157_ == 0 {
                            lean_dec_ref(v_extensions_2111_);
                            v___y_2117_ = v___x_2154_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2159_ = 0usize;
                            v___x_2160_ = lean_usize_of_nat(v___x_2156_);
                            v___x_2161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_2111_, v___x_2159_, v___x_2160_, v___x_2154_);
                            lean_dec_ref(v_extensions_2111_);
                            v___y_2117_ = v___x_2161_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2162_ = 0usize;
                        v___x_2163_ = lean_usize_of_nat(v___x_2156_);
                        v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_2111_, v___x_2162_, v___x_2163_, v___x_2154_);
                        lean_dec_ref(v_extensions_2111_);
                        v___y_2117_ = v___x_2164_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2118_ = lean_unsigned_to_nat(16);
                v___x_2119_ = l_Nat_toDigits(v___x_2118_, v_chunkLen_2115_);
                v___x_2120_ = lean_array_mk(v___x_2119_);
                v_sz_2121_ = lean_array_size(v___x_2120_);
                v___x_2122_ = 0usize;
                v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_2121_, v___x_2122_, v___x_2120_);
                v_size_2124_ = lean_byte_array_mk(v___x_2123_);
                v___x_2125_ = lean_string_to_utf8(v___y_2117_);
                lean_dec_ref(v___y_2117_);
                v___x_2126_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
                v___x_2127_ = lean_unsigned_to_nat(5);
                v___x_2128_ = lean_mk_empty_array_with_capacity(v___x_2127_);
                v___x_2129_ = lean_array_push(v___x_2128_, v_size_2124_);
                v___x_2130_ = lean_array_push(v___x_2129_, v___x_2125_);
                v___x_2131_ = lean_array_push(v___x_2130_, v___x_2126_);
                v___x_2132_ = lean_array_push(v___x_2131_, v_data_2110_);
                v___x_2133_ = lean_array_push(v___x_2132_, v___x_2126_);
                v___x_2134_ = lean_unsigned_to_nat(0);
                v___x_2135_ = lean_array_get_size(v___x_2133_);
                v___x_2136_ = lean_nat_dec_lt(v___x_2134_, v___x_2135_);
                if v___x_2136_ == 0 {
                    if v_isShared_2114_ == 0 {
                        lean_ctor_set(v___x_2113_, 1, v___x_2134_);
                        lean_ctor_set(v___x_2113_, 0, v___x_2133_);
                        v___x_2138_ = v___x_2113_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2133_);
                        lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2134_);
                        v___x_2138_ = v_reuseFailAlloc_2139_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2140_ = lean_nat_dec_le(v___x_2135_, v___x_2135_);
                    if v___x_2140_ == 0 {
                        if v___x_2136_ == 0 {
                            if v_isShared_2114_ == 0 {
                                lean_ctor_set(v___x_2113_, 1, v___x_2134_);
                                lean_ctor_set(v___x_2113_, 0, v___x_2133_);
                                v___x_2142_ = v___x_2113_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2133_);
                                lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2134_);
                                v___x_2142_ = v_reuseFailAlloc_2143_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_2144_ = lean_usize_of_nat(v___x_2135_);
                            v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_2133_, v___x_2122_, v___x_2144_, v___x_2134_);
                            if v_isShared_2114_ == 0 {
                                lean_ctor_set(v___x_2113_, 1, v___x_2145_);
                                lean_ctor_set(v___x_2113_, 0, v___x_2133_);
                                v___x_2147_ = v___x_2113_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2133_);
                                lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2145_);
                                v___x_2147_ = v_reuseFailAlloc_2148_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___x_2149_ = lean_usize_of_nat(v___x_2135_);
                        v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_2133_, v___x_2122_, v___x_2149_, v___x_2134_);
                        if v_isShared_2114_ == 0 {
                            lean_ctor_set(v___x_2113_, 1, v___x_2150_);
                            lean_ctor_set(v___x_2113_, 0, v___x_2133_);
                            v___x_2152_ = v___x_2113_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2133_);
                            lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2150_);
                            v___x_2152_ = v_reuseFailAlloc_2153_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___y_2091_ = v___x_2138_;
                state = 1;
                continue;
            }
            7 => {
                v___y_2091_ = v___x_2142_;
                state = 1;
                continue;
            }
            8 => {
                v___y_2091_ = v___x_2147_;
                state = 1;
                continue;
            }
            9 => {
                v___y_2091_ = v___x_2152_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(
    mut v_as_2166_: *mut LeanObject,
    mut v_i_2167_: *mut LeanObject,
    mut v_stop_2168_: *mut LeanObject,
    mut v_b_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2170_: usize = 0;
    let mut v_stop_boxed_2171_: usize = 0;
    let mut v_res_2172_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2170_ = lean_unbox_usize(v_i_2167_);
    lean_dec(v_i_2167_);
    v_stop_boxed_2171_ = lean_unbox_usize(v_stop_2168_);
    lean_dec(v_stop_2168_);
    v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_2166_, v_i_boxed_2170_, v_stop_boxed_2171_, v_b_2169_);
    lean_dec_ref(v_as_2166_);
    return v_res_2172_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(
    mut v_writer_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2181_: u8 = 0;
    let mut v_userClosedBody_2182_: u8 = 0;
    let mut v_omitBody_2183_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: u8 = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: usize = 0;
    let mut v___x_2195_: usize = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: usize = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: usize = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2176_ = lean_ctor_get(v_writer_2175_, 0);
                v_outputData_2177_ = lean_ctor_get(v_writer_2175_, 1);
                v_state_2178_ = lean_ctor_get(v_writer_2175_, 2);
                v_knownSize_2179_ = lean_ctor_get(v_writer_2175_, 3);
                v_messageHead_2180_ = lean_ctor_get(v_writer_2175_, 4);
                v_sentMessage_2181_ = lean_ctor_get_uint8(
                    v_writer_2175_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2182_ = lean_ctor_get_uint8(
                    v_writer_2175_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2183_ = lean_ctor_get_uint8(
                    v_writer_2175_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v___x_2184_ = lean_array_get_size(v_userData_2176_);
                v___x_2185_ = lean_unsigned_to_nat(0);
                v___x_2202_ = lean_nat_dec_eq(v___x_2184_, v___x_2185_);
                if v___x_2202_ == 0 {
                    lean_inc(v_messageHead_2180_);
                    lean_inc(v_knownSize_2179_);
                    lean_inc(v_state_2178_);
                    lean_inc_ref(v_outputData_2177_);
                    lean_inc_ref(v_userData_2176_);
                    lean_dec_ref(v_writer_2175_);
                    v___x_2203_ =
                        l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0;
                    v___x_2204_ = lean_nat_dec_lt(v___x_2185_, v___x_2184_);
                    if v___x_2204_ == 0 {
                        lean_dec_ref(v_userData_2176_);
                        v___y_2187_ = v___x_2203_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2205_ = lean_nat_dec_le(v___x_2184_, v___x_2184_);
                        if v___x_2205_ == 0 {
                            if v___x_2204_ == 0 {
                                lean_dec_ref(v_userData_2176_);
                                v___y_2187_ = v___x_2203_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2206_ = 0usize;
                                v___x_2207_ = lean_usize_of_nat(v___x_2184_);
                                v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_2176_, v___x_2206_, v___x_2207_, v___x_2203_);
                                lean_dec_ref(v_userData_2176_);
                                v___y_2187_ = v___x_2208_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2209_ = 0usize;
                            v___x_2210_ = lean_usize_of_nat(v___x_2184_);
                            v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_2176_, v___x_2209_, v___x_2210_, v___x_2203_);
                            lean_dec_ref(v_userData_2176_);
                            v___y_2187_ = v___x_2211_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_writer_2175_;
                }
            }
            1 => {
                v___x_2188_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0;
                v___x_2189_ = lean_array_get_size(v___y_2187_);
                v___x_2190_ = lean_nat_dec_lt(v___x_2185_, v___x_2189_);
                if v___x_2190_ == 0 {
                    lean_dec_ref(v___y_2187_);
                    v___x_2191_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v___x_2191_, 0, v___x_2188_);
                    lean_ctor_set(v___x_2191_, 1, v_outputData_2177_);
                    lean_ctor_set(v___x_2191_, 2, v_state_2178_);
                    lean_ctor_set(v___x_2191_, 3, v_knownSize_2179_);
                    lean_ctor_set(v___x_2191_, 4, v_messageHead_2180_);
                    lean_ctor_set(v___x_2191_, 5, v___x_2185_);
                    lean_ctor_set_uint8(
                        v___x_2191_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2181_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2191_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2182_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2191_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2183_,
                    );
                    return v___x_2191_;
                } else {
                    v___x_2192_ = lean_nat_dec_le(v___x_2189_, v___x_2189_);
                    if v___x_2192_ == 0 {
                        if v___x_2190_ == 0 {
                            lean_dec_ref(v___y_2187_);
                            v___x_2193_ = lean_alloc_ctor(0, 6, (3) as u32);
                            lean_ctor_set(v___x_2193_, 0, v___x_2188_);
                            lean_ctor_set(v___x_2193_, 1, v_outputData_2177_);
                            lean_ctor_set(v___x_2193_, 2, v_state_2178_);
                            lean_ctor_set(v___x_2193_, 3, v_knownSize_2179_);
                            lean_ctor_set(v___x_2193_, 4, v_messageHead_2180_);
                            lean_ctor_set(v___x_2193_, 5, v___x_2185_);
                            lean_ctor_set_uint8(
                                v___x_2193_,
                                (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                                v_sentMessage_2181_,
                            );
                            lean_ctor_set_uint8(
                                v___x_2193_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                                v_userClosedBody_2182_,
                            );
                            lean_ctor_set_uint8(
                                v___x_2193_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                                v_omitBody_2183_,
                            );
                            return v___x_2193_;
                        } else {
                            v___x_2194_ = 0usize;
                            v___x_2195_ = lean_usize_of_nat(v___x_2189_);
                            v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_2187_, v___x_2194_, v___x_2195_, v_outputData_2177_);
                            lean_dec_ref(v___y_2187_);
                            v___x_2197_ = lean_alloc_ctor(0, 6, (3) as u32);
                            lean_ctor_set(v___x_2197_, 0, v___x_2188_);
                            lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                            lean_ctor_set(v___x_2197_, 2, v_state_2178_);
                            lean_ctor_set(v___x_2197_, 3, v_knownSize_2179_);
                            lean_ctor_set(v___x_2197_, 4, v_messageHead_2180_);
                            lean_ctor_set(v___x_2197_, 5, v___x_2185_);
                            lean_ctor_set_uint8(
                                v___x_2197_,
                                (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                                v_sentMessage_2181_,
                            );
                            lean_ctor_set_uint8(
                                v___x_2197_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                                v_userClosedBody_2182_,
                            );
                            lean_ctor_set_uint8(
                                v___x_2197_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                                v_omitBody_2183_,
                            );
                            return v___x_2197_;
                        }
                    } else {
                        v___x_2198_ = 0usize;
                        v___x_2199_ = lean_usize_of_nat(v___x_2189_);
                        v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_2187_, v___x_2198_, v___x_2199_, v_outputData_2177_);
                        lean_dec_ref(v___y_2187_);
                        v___x_2201_ = lean_alloc_ctor(0, 6, (3) as u32);
                        lean_ctor_set(v___x_2201_, 0, v___x_2188_);
                        lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                        lean_ctor_set(v___x_2201_, 2, v_state_2178_);
                        lean_ctor_set(v___x_2201_, 3, v_knownSize_2179_);
                        lean_ctor_set(v___x_2201_, 4, v_messageHead_2180_);
                        lean_ctor_set(v___x_2201_, 5, v___x_2185_);
                        lean_ctor_set_uint8(
                            v___x_2201_,
                            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                            v_sentMessage_2181_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2201_,
                            (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                            v_userClosedBody_2182_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2201_,
                            (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                            v_omitBody_2183_,
                        );
                        return v___x_2201_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeChunkedBody(
    mut v_dir_2212_: u8,
    mut v_writer_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_2213_);
    return v___x_2214_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(
    mut v_dir_2215_: *mut LeanObject,
    mut v_writer_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2217_: u8 = 0;
    let mut v_res_2218_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2217_ = (lean_unbox(v_dir_2215_) as u8);
    v_res_2218_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_2217_, v_writer_2216_);
    return v_res_2218_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2220_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0;
    v___x_2221_ = lean_string_to_utf8(v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    v___x_2222_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once
        ),
        _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1,
    );
    v___x_2223_ = lean_byte_array_size(v___x_2222_);
    return v___x_2223_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(
    mut v_writer_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_writer_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userData_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2230_: u8 = 0;
    let mut v_userClosedBody_2231_: u8 = 0;
    let mut v_omitBody_2232_: u8 = 0;
    let mut v_userDataBytes_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v_data_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut v_unused_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_writer_2225_ =
                    l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_2224_);
                v_outputData_2226_ = lean_ctor_get(v_writer_2225_, 1);
                v_userData_2227_ = lean_ctor_get(v_writer_2225_, 0);
                v_knownSize_2228_ = lean_ctor_get(v_writer_2225_, 3);
                v_messageHead_2229_ = lean_ctor_get(v_writer_2225_, 4);
                v_sentMessage_2230_ = lean_ctor_get_uint8(
                    v_writer_2225_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2231_ = lean_ctor_get_uint8(
                    v_writer_2225_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2232_ = lean_ctor_get_uint8(
                    v_writer_2225_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2233_ = lean_ctor_get(v_writer_2225_, 5);
                v_isSharedCheck_2254_ = (!lean_is_exclusive(v_writer_2225_)) as u8;
                if v_isSharedCheck_2254_ == 0 {
                    v_unused_2255_ = lean_ctor_get(v_writer_2225_, 2);
                    lean_dec(v_unused_2255_);
                    v___x_2235_ = v_writer_2225_;
                    v_isShared_2236_ = v_isSharedCheck_2254_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2233_);
                    lean_inc(v_messageHead_2229_);
                    lean_inc(v_knownSize_2228_);
                    lean_inc(v_outputData_2226_);
                    lean_inc(v_userData_2227_);
                    lean_dec(v_writer_2225_);
                    v___x_2235_ = lean_box(0);
                    v_isShared_2236_ = v_isSharedCheck_2254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_2237_ = lean_ctor_get(v_outputData_2226_, 0);
                v_size_2238_ = lean_ctor_get(v_outputData_2226_, 1);
                v_isSharedCheck_2253_ = (!lean_is_exclusive(v_outputData_2226_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v___x_2240_ = v_outputData_2226_;
                    v_isShared_2241_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_size_2238_);
                    lean_inc(v_data_2237_);
                    lean_dec(v_outputData_2226_);
                    v___x_2240_ = lean_box(0);
                    v_isShared_2241_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2242_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once
                    ),
                    _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1,
                );
                v___x_2243_ = lean_array_push(v_data_2237_, v___x_2242_);
                v___x_2244_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once
                    ),
                    _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2,
                );
                v___x_2245_ = lean_nat_add(v_size_2238_, v___x_2244_);
                lean_dec(v_size_2238_);
                if v_isShared_2241_ == 0 {
                    lean_ctor_set(v___x_2240_, 1, v___x_2245_);
                    lean_ctor_set(v___x_2240_, 0, v___x_2243_);
                    v___x_2247_ = v___x_2240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2243_);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2245_);
                    v___x_2247_ = v_reuseFailAlloc_2252_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2248_ = lean_box(6);
                if v_isShared_2236_ == 0 {
                    lean_ctor_set(v___x_2235_, 2, v___x_2248_);
                    lean_ctor_set(v___x_2235_, 1, v___x_2247_);
                    v___x_2250_ = v___x_2235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_userData_2227_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2247_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 2, v___x_2248_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_knownSize_2228_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_messageHead_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 5, v_userDataBytes_2233_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2251_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2230_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2251_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2231_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2251_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2232_,
                    );
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFinalChunk(
    mut v_dir_2256_: u8,
    mut v_writer_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    v___x_2258_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(
    mut v_dir_2259_: *mut LeanObject,
    mut v_writer_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2261_: u8 = 0;
    let mut v_res_2262_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2261_ = (lean_unbox(v_dir_2259_) as u8);
    v_res_2262_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_2261_, v_writer_2260_);
    return v_res_2262_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(
    mut v_as_2263_: *mut LeanObject,
    mut v_i_2264_: usize,
    mut v_stop_2265_: usize,
    mut v_b_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: usize = 0;
    let mut v_reuseFailAlloc_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2267_ = lean_usize_dec_eq(v_i_2264_, v_stop_2265_);
                if v___x_2267_ == 0 {
                    v___x_2268_ = lean_array_uget_borrowed(v_as_2263_, v_i_2264_);
                    v_data_2269_ = lean_ctor_get(v___x_2268_, 0);
                    v_data_2270_ = lean_ctor_get(v_b_2266_, 0);
                    v_size_2271_ = lean_ctor_get(v_b_2266_, 1);
                    v_isSharedCheck_2284_ = (!lean_is_exclusive(v_b_2266_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2273_ = v_b_2266_;
                        v_isShared_2274_ = v_isSharedCheck_2284_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_size_2271_);
                        lean_inc(v_data_2270_);
                        lean_dec(v_b_2266_);
                        v___x_2273_ = lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2284_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2266_;
                }
            }
            1 => {
                lean_inc_ref(v_data_2269_);
                v___x_2275_ = lean_array_push(v_data_2270_, v_data_2269_);
                v___x_2276_ = lean_byte_array_size(v_data_2269_);
                v___x_2277_ = lean_nat_add(v_size_2271_, v___x_2276_);
                lean_dec(v_size_2271_);
                if v_isShared_2274_ == 0 {
                    lean_ctor_set(v___x_2273_, 1, v___x_2277_);
                    lean_ctor_set(v___x_2273_, 0, v___x_2275_);
                    v___x_2279_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2275_);
                    lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2277_);
                    v___x_2279_ = v_reuseFailAlloc_2283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2280_ = 1usize;
                v___x_2281_ = lean_usize_add(v_i_2264_, v___x_2280_);
                v_i_2264_ = v___x_2281_;
                v_b_2266_ = v___x_2279_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(
    mut v_as_2285_: *mut LeanObject,
    mut v_i_2286_: *mut LeanObject,
    mut v_stop_2287_: *mut LeanObject,
    mut v_b_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2289_: usize = 0;
    let mut v_stop_boxed_2290_: usize = 0;
    let mut v_res_2291_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2289_ = lean_unbox_usize(v_i_2286_);
    lean_dec(v_i_2286_);
    v_stop_boxed_2290_ = lean_unbox_usize(v_stop_2287_);
    lean_dec(v_stop_2287_);
    v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_2285_, v_i_boxed_2289_, v_stop_boxed_2290_, v_b_2288_);
    lean_dec_ref(v_as_2285_);
    return v_res_2291_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(
    mut v_writer_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2298_: u8 = 0;
    let mut v_userClosedBody_2299_: u8 = 0;
    let mut v_omitBody_2300_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: usize = 0;
    let mut v___x_2322_: usize = 0;
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v_unused_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2293_ = lean_ctor_get(v_writer_2292_, 0);
                v_outputData_2294_ = lean_ctor_get(v_writer_2292_, 1);
                v_state_2295_ = lean_ctor_get(v_writer_2292_, 2);
                v_knownSize_2296_ = lean_ctor_get(v_writer_2292_, 3);
                v_messageHead_2297_ = lean_ctor_get(v_writer_2292_, 4);
                v_sentMessage_2298_ = lean_ctor_get_uint8(
                    v_writer_2292_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2299_ = lean_ctor_get_uint8(
                    v_writer_2292_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2300_ = lean_ctor_get_uint8(
                    v_writer_2292_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_isSharedCheck_2327_ = (!lean_is_exclusive(v_writer_2292_)) as u8;
                if v_isSharedCheck_2327_ == 0 {
                    v_unused_2328_ = lean_ctor_get(v_writer_2292_, 5);
                    lean_dec(v_unused_2328_);
                    v___x_2302_ = v_writer_2292_;
                    v_isShared_2303_ = v_isSharedCheck_2327_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_messageHead_2297_);
                    lean_inc(v_knownSize_2296_);
                    lean_inc(v_state_2295_);
                    lean_inc(v_outputData_2294_);
                    lean_inc(v_userData_2293_);
                    lean_dec(v_writer_2292_);
                    v___x_2302_ = lean_box(0);
                    v_isShared_2303_ = v_isSharedCheck_2327_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2304_ = lean_unsigned_to_nat(0);
                v___x_2305_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0;
                v___x_2306_ = lean_array_get_size(v_userData_2293_);
                v___x_2307_ = lean_nat_dec_lt(v___x_2304_, v___x_2306_);
                if v___x_2307_ == 0 {
                    lean_dec_ref(v_userData_2293_);
                    if v_isShared_2303_ == 0 {
                        lean_ctor_set(v___x_2302_, 5, v___x_2304_);
                        lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                        v___x_2309_ = v___x_2302_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 6, (3) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2305_);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_outputData_2294_);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_state_2295_);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_knownSize_2296_);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_messageHead_2297_);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 5, v___x_2304_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2310_,
                            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                            v_sentMessage_2298_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2310_,
                            (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                            v_userClosedBody_2299_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2310_,
                            (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                            v_omitBody_2300_,
                        );
                        v___x_2309_ = v_reuseFailAlloc_2310_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2311_ = lean_nat_dec_le(v___x_2306_, v___x_2306_);
                    if v___x_2311_ == 0 {
                        if v___x_2307_ == 0 {
                            lean_dec_ref(v_userData_2293_);
                            if v_isShared_2303_ == 0 {
                                lean_ctor_set(v___x_2302_, 5, v___x_2304_);
                                lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                                v___x_2313_ = v___x_2302_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 6, (3) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2305_);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_outputData_2294_);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_state_2295_);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_knownSize_2296_);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_messageHead_2297_);
                                lean_ctor_set(v_reuseFailAlloc_2314_, 5, v___x_2304_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2314_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                                    v_sentMessage_2298_,
                                );
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2314_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                                    v_userClosedBody_2299_,
                                );
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2314_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                                    v_omitBody_2300_,
                                );
                                v___x_2313_ = v_reuseFailAlloc_2314_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_2315_ = 0usize;
                            v___x_2316_ = lean_usize_of_nat(v___x_2306_);
                            v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_2293_, v___x_2315_, v___x_2316_, v_outputData_2294_);
                            lean_dec_ref(v_userData_2293_);
                            if v_isShared_2303_ == 0 {
                                lean_ctor_set(v___x_2302_, 5, v___x_2304_);
                                lean_ctor_set(v___x_2302_, 1, v___x_2317_);
                                lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                                v___x_2319_ = v___x_2302_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 6, (3) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2305_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2317_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_state_2295_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_knownSize_2296_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_messageHead_2297_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 5, v___x_2304_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2320_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                                    v_sentMessage_2298_,
                                );
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2320_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                                    v_userClosedBody_2299_,
                                );
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_2320_,
                                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                                    v_omitBody_2300_,
                                );
                                v___x_2319_ = v_reuseFailAlloc_2320_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_2321_ = 0usize;
                        v___x_2322_ = lean_usize_of_nat(v___x_2306_);
                        v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_2293_, v___x_2321_, v___x_2322_, v_outputData_2294_);
                        lean_dec_ref(v_userData_2293_);
                        if v_isShared_2303_ == 0 {
                            lean_ctor_set(v___x_2302_, 5, v___x_2304_);
                            lean_ctor_set(v___x_2302_, 1, v___x_2323_);
                            lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                            v___x_2325_ = v___x_2302_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 6, (3) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2305_);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_state_2295_);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_knownSize_2296_);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_messageHead_2297_);
                            lean_ctor_set(v_reuseFailAlloc_2326_, 5, v___x_2304_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2326_,
                                (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                                v_sentMessage_2298_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2326_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                                v_userClosedBody_2299_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2326_,
                                (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                                v_omitBody_2300_,
                            );
                            v___x_2325_ = v_reuseFailAlloc_2326_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2309_;
            }
            3 => {
                return v___x_2313_;
            }
            4 => {
                return v___x_2319_;
            }
            5 => {
                return v___x_2325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeRawBody(
    mut v_dir_2329_: u8,
    mut v_writer_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_2330_);
    return v___x_2331_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(
    mut v_dir_2332_: *mut LeanObject,
    mut v_writer_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2334_: u8 = 0;
    let mut v_res_2335_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2334_ = (lean_unbox(v_dir_2332_) as u8);
    v_res_2335_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_2334_, v_writer_2333_);
    return v_res_2335_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(
    mut v___x_2336_: u8,
    mut v_x1_2337_: *mut LeanObject,
    mut v_x2_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    v___x_2339_ = lean_unsigned_to_nat(0);
    v___x_2340_ = lean_byte_array_size(v_x1_2337_);
    v___x_2341_ = lean_byte_array_size(v_x2_2338_);
    v___x_2342_ = lean_byte_array_copy_slice(
        v_x2_2338_,
        v___x_2339_,
        v_x1_2337_,
        v___x_2340_,
        v___x_2341_,
        v___x_2336_,
    );
    return v___x_2342_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(
    mut v___x_2343_: *mut LeanObject,
    mut v_x1_2344_: *mut LeanObject,
    mut v_x2_2345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_120__boxed_2346_: u8 = 0;
    let mut v_res_2347_: *mut LeanObject = core::ptr::null_mut();
    v___x_120__boxed_2346_ = (lean_unbox(v___x_2343_) as u8);
    v_res_2347_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(
        v___x_120__boxed_2346_,
        v_x1_2344_,
        v_x2_2345_,
    );
    lean_dec_ref(v_x2_2345_);
    return v_res_2347_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(
    mut v_writer_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2357_: u8 = 0;
    let mut v_userClosedBody_2358_: u8 = 0;
    let mut v_omitBody_2359_: u8 = 0;
    let mut v_userDataBytes_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2363_: u8 = 0;
    let mut v___y_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u8 = 0;
    let mut v___x_2384_: usize = 0;
    let mut v___x_2385_: usize = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: usize = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2352_ = lean_ctor_get(v_writer_2351_, 0);
                v_outputData_2353_ = lean_ctor_get(v_writer_2351_, 1);
                v_state_2354_ = lean_ctor_get(v_writer_2351_, 2);
                v_knownSize_2355_ = lean_ctor_get(v_writer_2351_, 3);
                v_messageHead_2356_ = lean_ctor_get(v_writer_2351_, 4);
                v_sentMessage_2357_ = lean_ctor_get_uint8(
                    v_writer_2351_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2358_ = lean_ctor_get_uint8(
                    v_writer_2351_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2359_ = lean_ctor_get_uint8(
                    v_writer_2351_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2360_ = lean_ctor_get(v_writer_2351_, 5);
                v_isSharedCheck_2392_ = (!lean_is_exclusive(v_writer_2351_)) as u8;
                if v_isSharedCheck_2392_ == 0 {
                    v___x_2362_ = v_writer_2351_;
                    v_isShared_2363_ = v_isSharedCheck_2392_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2360_);
                    lean_inc(v_messageHead_2356_);
                    lean_inc(v_knownSize_2355_);
                    lean_inc(v_state_2354_);
                    lean_inc(v_outputData_2353_);
                    lean_inc(v_userData_2352_);
                    lean_dec(v_writer_2351_);
                    v___x_2362_ = lean_box(0);
                    v_isShared_2363_ = v_isSharedCheck_2392_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_2372_ = lean_ctor_get(v_outputData_2353_, 0);
                lean_inc_ref(v_data_2372_);
                v_size_2373_ = lean_ctor_get(v_outputData_2353_, 1);
                lean_inc(v_size_2373_);
                lean_dec_ref(v_outputData_2353_);
                v___x_2374_ = lean_unsigned_to_nat(1);
                v___x_2375_ = lean_array_get_size(v_data_2372_);
                v___x_2376_ = lean_nat_dec_eq(v___x_2374_, v___x_2375_);
                if v___x_2376_ == 0 {
                    v___x_2377_ = lean_mk_empty_byte_array(v_size_2373_);
                    lean_dec(v_size_2373_);
                    v___x_2378_ = lean_unsigned_to_nat(0);
                    v___x_2379_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10;
                    v___x_2380_ = lean_nat_dec_lt(v___x_2378_, v___x_2375_);
                    if v___x_2380_ == 0 {
                        lean_dec_ref(v_data_2372_);
                        v___y_2365_ = v___x_2377_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2381_ = lean_box((v___x_2376_) as usize);
                        v___f_2382_ = lean_alloc_closure(
                            l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_2382_, 0, v___x_2381_);
                        v___x_2383_ = lean_nat_dec_le(v___x_2375_, v___x_2375_);
                        if v___x_2383_ == 0 {
                            if v___x_2380_ == 0 {
                                lean_dec_ref(v___f_2382_);
                                lean_dec_ref(v_data_2372_);
                                v___y_2365_ = v___x_2377_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2384_ = 0usize;
                                v___x_2385_ = lean_usize_of_nat(v___x_2375_);
                                v___x_2386_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_2379_,
                                        v___f_2382_,
                                        v_data_2372_,
                                        v___x_2384_,
                                        v___x_2385_,
                                        v___x_2377_,
                                    );
                                v___y_2365_ = v___x_2386_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_2387_ = 0usize;
                            v___x_2388_ = lean_usize_of_nat(v___x_2375_);
                            v___x_2389_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2379_,
                                    v___f_2382_,
                                    v_data_2372_,
                                    v___x_2387_,
                                    v___x_2388_,
                                    v___x_2377_,
                                );
                            v___y_2365_ = v___x_2389_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_2373_);
                    v___x_2390_ = lean_unsigned_to_nat(0);
                    v___x_2391_ = lean_array_fget(v_data_2372_, v___x_2390_);
                    lean_dec_ref(v_data_2372_);
                    v___y_2365_ = v___x_2391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2366_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0;
                if v_isShared_2363_ == 0 {
                    lean_ctor_set(v___x_2362_, 1, v___x_2366_);
                    v___x_2368_ = v___x_2362_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_userData_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2366_);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_state_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_knownSize_2355_);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_messageHead_2356_);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 5, v_userDataBytes_2360_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2371_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2357_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2371_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2358_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2371_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2359_,
                    );
                    v___x_2368_ = v_reuseFailAlloc_2371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2369_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                lean_ctor_set(v___x_2369_, 1, v___y_2365_);
                v___x_2370_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2370_, 0, v___x_2369_);
                return v___x_2370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_takeOutput(
    mut v_dir_2393_: u8,
    mut v_writer_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2400_: u8 = 0;
    let mut v_userClosedBody_2401_: u8 = 0;
    let mut v_omitBody_2402_: u8 = 0;
    let mut v_userDataBytes_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___y_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: usize = 0;
    let mut v___x_2428_: usize = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2395_ = lean_ctor_get(v_writer_2394_, 0);
                v_outputData_2396_ = lean_ctor_get(v_writer_2394_, 1);
                v_state_2397_ = lean_ctor_get(v_writer_2394_, 2);
                v_knownSize_2398_ = lean_ctor_get(v_writer_2394_, 3);
                v_messageHead_2399_ = lean_ctor_get(v_writer_2394_, 4);
                v_sentMessage_2400_ = lean_ctor_get_uint8(
                    v_writer_2394_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2401_ = lean_ctor_get_uint8(
                    v_writer_2394_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2402_ = lean_ctor_get_uint8(
                    v_writer_2394_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2403_ = lean_ctor_get(v_writer_2394_, 5);
                v_isSharedCheck_2435_ = (!lean_is_exclusive(v_writer_2394_)) as u8;
                if v_isSharedCheck_2435_ == 0 {
                    v___x_2405_ = v_writer_2394_;
                    v_isShared_2406_ = v_isSharedCheck_2435_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2403_);
                    lean_inc(v_messageHead_2399_);
                    lean_inc(v_knownSize_2398_);
                    lean_inc(v_state_2397_);
                    lean_inc(v_outputData_2396_);
                    lean_inc(v_userData_2395_);
                    lean_dec(v_writer_2394_);
                    v___x_2405_ = lean_box(0);
                    v_isShared_2406_ = v_isSharedCheck_2435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_2415_ = lean_ctor_get(v_outputData_2396_, 0);
                lean_inc_ref(v_data_2415_);
                v_size_2416_ = lean_ctor_get(v_outputData_2396_, 1);
                lean_inc(v_size_2416_);
                lean_dec_ref(v_outputData_2396_);
                v___x_2417_ = lean_unsigned_to_nat(1);
                v___x_2418_ = lean_array_get_size(v_data_2415_);
                v___x_2419_ = lean_nat_dec_eq(v___x_2417_, v___x_2418_);
                if v___x_2419_ == 0 {
                    v___x_2420_ = lean_mk_empty_byte_array(v_size_2416_);
                    lean_dec(v_size_2416_);
                    v___x_2421_ = lean_unsigned_to_nat(0);
                    v___x_2422_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10;
                    v___x_2423_ = lean_nat_dec_lt(v___x_2421_, v___x_2418_);
                    if v___x_2423_ == 0 {
                        lean_dec_ref(v_data_2415_);
                        v___y_2408_ = v___x_2420_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2424_ = lean_box((v___x_2419_) as usize);
                        v___f_2425_ = lean_alloc_closure(
                            l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_2425_, 0, v___x_2424_);
                        v___x_2426_ = lean_nat_dec_le(v___x_2418_, v___x_2418_);
                        if v___x_2426_ == 0 {
                            if v___x_2423_ == 0 {
                                lean_dec_ref(v___f_2425_);
                                lean_dec_ref(v_data_2415_);
                                v___y_2408_ = v___x_2420_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2427_ = 0usize;
                                v___x_2428_ = lean_usize_of_nat(v___x_2418_);
                                v___x_2429_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_2422_,
                                        v___f_2425_,
                                        v_data_2415_,
                                        v___x_2427_,
                                        v___x_2428_,
                                        v___x_2420_,
                                    );
                                v___y_2408_ = v___x_2429_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_2430_ = 0usize;
                            v___x_2431_ = lean_usize_of_nat(v___x_2418_);
                            v___x_2432_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2422_,
                                    v___f_2425_,
                                    v_data_2415_,
                                    v___x_2430_,
                                    v___x_2431_,
                                    v___x_2420_,
                                );
                            v___y_2408_ = v___x_2432_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_2416_);
                    v___x_2433_ = lean_unsigned_to_nat(0);
                    v___x_2434_ = lean_array_fget(v_data_2415_, v___x_2433_);
                    lean_dec_ref(v_data_2415_);
                    v___y_2408_ = v___x_2434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2409_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0;
                if v_isShared_2406_ == 0 {
                    lean_ctor_set(v___x_2405_, 1, v___x_2409_);
                    v___x_2411_ = v___x_2405_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_userData_2395_);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_state_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_knownSize_2398_);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_messageHead_2399_);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 5, v_userDataBytes_2403_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2414_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2400_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2414_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2401_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2414_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2402_,
                    );
                    v___x_2411_ = v_reuseFailAlloc_2414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2412_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2412_, 0, v___x_2411_);
                lean_ctor_set(v___x_2412_, 1, v___y_2408_);
                v___x_2413_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2413_, 0, v___x_2412_);
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(
    mut v_dir_2436_: *mut LeanObject,
    mut v_writer_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2438_: u8 = 0;
    let mut v_res_2439_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2438_ = (lean_unbox(v_dir_2436_) as u8);
    v_res_2439_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_2438_, v_writer_2437_);
    return v_res_2439_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_setState___redArg(
    mut v_state_2440_: *mut LeanObject,
    mut v_writer_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2446_: u8 = 0;
    let mut v_userClosedBody_2447_: u8 = 0;
    let mut v_omitBody_2448_: u8 = 0;
    let mut v_userDataBytes_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_unused_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2442_ = lean_ctor_get(v_writer_2441_, 0);
                v_outputData_2443_ = lean_ctor_get(v_writer_2441_, 1);
                v_knownSize_2444_ = lean_ctor_get(v_writer_2441_, 3);
                v_messageHead_2445_ = lean_ctor_get(v_writer_2441_, 4);
                v_sentMessage_2446_ = lean_ctor_get_uint8(
                    v_writer_2441_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2447_ = lean_ctor_get_uint8(
                    v_writer_2441_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2448_ = lean_ctor_get_uint8(
                    v_writer_2441_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2449_ = lean_ctor_get(v_writer_2441_, 5);
                v_isSharedCheck_2456_ = (!lean_is_exclusive(v_writer_2441_)) as u8;
                if v_isSharedCheck_2456_ == 0 {
                    v_unused_2457_ = lean_ctor_get(v_writer_2441_, 2);
                    lean_dec(v_unused_2457_);
                    v___x_2451_ = v_writer_2441_;
                    v_isShared_2452_ = v_isSharedCheck_2456_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2449_);
                    lean_inc(v_messageHead_2445_);
                    lean_inc(v_knownSize_2444_);
                    lean_inc(v_outputData_2443_);
                    lean_inc(v_userData_2442_);
                    lean_dec(v_writer_2441_);
                    v___x_2451_ = lean_box(0);
                    v_isShared_2452_ = v_isSharedCheck_2456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2452_ == 0 {
                    lean_ctor_set(v___x_2451_, 2, v_state_2440_);
                    v___x_2454_ = v___x_2451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_userData_2442_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_outputData_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_state_2440_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_knownSize_2444_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_messageHead_2445_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 5, v_userDataBytes_2449_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2455_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2446_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2455_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2447_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2455_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2448_,
                    );
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_setState(
    mut v_dir_2458_: u8,
    mut v_state_2459_: *mut LeanObject,
    mut v_writer_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2465_: u8 = 0;
    let mut v_userClosedBody_2466_: u8 = 0;
    let mut v_omitBody_2467_: u8 = 0;
    let mut v_userDataBytes_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v_unused_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2461_ = lean_ctor_get(v_writer_2460_, 0);
                v_outputData_2462_ = lean_ctor_get(v_writer_2460_, 1);
                v_knownSize_2463_ = lean_ctor_get(v_writer_2460_, 3);
                v_messageHead_2464_ = lean_ctor_get(v_writer_2460_, 4);
                v_sentMessage_2465_ = lean_ctor_get_uint8(
                    v_writer_2460_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2466_ = lean_ctor_get_uint8(
                    v_writer_2460_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2467_ = lean_ctor_get_uint8(
                    v_writer_2460_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2468_ = lean_ctor_get(v_writer_2460_, 5);
                v_isSharedCheck_2475_ = (!lean_is_exclusive(v_writer_2460_)) as u8;
                if v_isSharedCheck_2475_ == 0 {
                    v_unused_2476_ = lean_ctor_get(v_writer_2460_, 2);
                    lean_dec(v_unused_2476_);
                    v___x_2470_ = v_writer_2460_;
                    v_isShared_2471_ = v_isSharedCheck_2475_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2468_);
                    lean_inc(v_messageHead_2464_);
                    lean_inc(v_knownSize_2463_);
                    lean_inc(v_outputData_2462_);
                    lean_inc(v_userData_2461_);
                    lean_dec(v_writer_2460_);
                    v___x_2470_ = lean_box(0);
                    v_isShared_2471_ = v_isSharedCheck_2475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2471_ == 0 {
                    lean_ctor_set(v___x_2470_, 2, v_state_2459_);
                    v___x_2473_ = v___x_2470_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_userData_2461_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_outputData_2462_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_state_2459_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_knownSize_2463_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_messageHead_2464_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 5, v_userDataBytes_2468_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2474_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2465_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2474_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2466_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2474_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2467_,
                    );
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_setState___boxed(
    mut v_dir_2477_: *mut LeanObject,
    mut v_state_2478_: *mut LeanObject,
    mut v_writer_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2480_: u8 = 0;
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2480_ = (lean_unbox(v_dir_2477_) as u8);
    v_res_2481_ =
        l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_2480_, v_state_2478_, v_writer_2479_);
    return v_res_2481_;
}
pub unsafe fn l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(
    mut v_dir_2482_: u8,
    mut v_messageHead_2483_: *mut LeanObject,
    mut v_writer_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2490_: u8 = 0;
    let mut v_userClosedBody_2491_: u8 = 0;
    let mut v_omitBody_2492_: u8 = 0;
    let mut v_userDataBytes_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___y_2498_: u8 = 0;
    let mut v___x_6__overap_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2485_ = lean_ctor_get(v_writer_2484_, 0);
                v_outputData_2486_ = lean_ctor_get(v_writer_2484_, 1);
                v_state_2487_ = lean_ctor_get(v_writer_2484_, 2);
                v_knownSize_2488_ = lean_ctor_get(v_writer_2484_, 3);
                v_messageHead_2489_ = lean_ctor_get(v_writer_2484_, 4);
                v_sentMessage_2490_ = lean_ctor_get_uint8(
                    v_writer_2484_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2491_ = lean_ctor_get_uint8(
                    v_writer_2484_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2492_ = lean_ctor_get_uint8(
                    v_writer_2484_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2493_ = lean_ctor_get(v_writer_2484_, 5);
                v_isSharedCheck_2506_ = (!lean_is_exclusive(v_writer_2484_)) as u8;
                if v_isSharedCheck_2506_ == 0 {
                    v___x_2495_ = v_writer_2484_;
                    v_isShared_2496_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2493_);
                    lean_inc(v_messageHead_2489_);
                    lean_inc(v_knownSize_2488_);
                    lean_inc(v_state_2487_);
                    lean_inc(v_outputData_2486_);
                    lean_inc(v_userData_2485_);
                    lean_dec(v_writer_2484_);
                    v___x_2495_ = lean_box(0);
                    v_isShared_2496_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_dir_2482_ == 0 {
                    v___x_2504_ = 1;
                    v___y_2498_ = v___x_2504_;
                    state = 2;
                    continue;
                } else {
                    v___x_2505_ = 0;
                    v___y_2498_ = v___x_2505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6__overap_2499_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_2498_);
                v___x_2500_ = lean_apply_2(
                    v___x_6__overap_2499_,
                    v_outputData_2486_,
                    v_messageHead_2483_,
                );
                if v_isShared_2496_ == 0 {
                    lean_ctor_set(v___x_2495_, 1, v___x_2500_);
                    v___x_2502_ = v___x_2495_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_userData_2485_);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2500_);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_state_2487_);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_knownSize_2488_);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_messageHead_2489_);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 5, v_userDataBytes_2493_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2503_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2490_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2503_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2491_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2503_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2492_,
                    );
                    v___x_2502_ = v_reuseFailAlloc_2503_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(
    mut v_dir_2507_: *mut LeanObject,
    mut v_messageHead_2508_: *mut LeanObject,
    mut v_writer_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2510_: u8 = 0;
    let mut v_res_2511_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2510_ = (lean_unbox(v_dir_2507_) as u8);
    v_res_2511_ =
        l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(
            v_dir_boxed_2510_,
            v_messageHead_2508_,
            v_writer_2509_,
        );
    return v_res_2511_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(
    mut v_a_2512_: *mut LeanObject,
    mut v_x_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_2514_ = lean_ctor_get(v_x_2513_, 0);
                v_value_2515_ = lean_ctor_get(v_x_2513_, 1);
                v_tail_2516_ = lean_ctor_get(v_x_2513_, 2);
                v___x_2517_ = lean_string_dec_eq(v_key_2514_, v_a_2512_);
                if v___x_2517_ == 0 {
                    v_x_2513_ = v_tail_2516_;
                    state = 0;
                    continue;
                } else {
                    lean_inc(v_value_2515_);
                    return v_value_2515_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(
    mut v_a_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2521_: *mut LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_2519_, v_x_2520_);
    lean_dec(v_x_2520_);
    lean_dec_ref(v_a_2519_);
    return v_res_2521_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(
    mut v_m_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u64 = 0;
    let mut v___x_2527_: u64 = 0;
    let mut v___x_2528_: u64 = 0;
    let mut v_fold_2529_: u64 = 0;
    let mut v___x_2530_: u64 = 0;
    let mut v___x_2531_: u64 = 0;
    let mut v___x_2532_: u64 = 0;
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: usize = 0;
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut v___x_2537_: usize = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2524_ = lean_ctor_get(v_m_2522_, 1);
    v___x_2525_ = lean_array_get_size(v_buckets_2524_);
    v___x_2526_ = lean_string_hash(v_a_2523_);
    v___x_2527_ = 32u64;
    v___x_2528_ = lean_uint64_shift_right(v___x_2526_, v___x_2527_);
    v_fold_2529_ = lean_uint64_xor(v___x_2526_, v___x_2528_);
    v___x_2530_ = 16u64;
    v___x_2531_ = lean_uint64_shift_right(v_fold_2529_, v___x_2530_);
    v___x_2532_ = lean_uint64_xor(v_fold_2529_, v___x_2531_);
    v___x_2533_ = lean_uint64_to_usize(v___x_2532_);
    v___x_2534_ = lean_usize_of_nat(v___x_2525_);
    v___x_2535_ = 1usize;
    v___x_2536_ = lean_usize_sub(v___x_2534_, v___x_2535_);
    v___x_2537_ = lean_usize_land(v___x_2533_, v___x_2536_);
    v___x_2538_ = lean_array_uget_borrowed(v_buckets_2524_, v___x_2537_);
    v___x_2539_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_2523_, v___x_2538_);
    return v___x_2539_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(
    mut v_m_2540_: *mut LeanObject,
    mut v_a_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2542_: *mut LeanObject = core::ptr::null_mut();
    v_res_2542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_2540_, v_a_2541_);
    lean_dec_ref(v_a_2541_);
    lean_dec_ref(v_m_2540_);
    return v_res_2542_;
}
pub unsafe fn l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(
    mut v_s_2543_: *mut LeanObject,
    mut v_p_2544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2546_: u32 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: u32 = 0;
    let mut v___x_2554_: u32 = 0;
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: u32 = 0;
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: u32 = 0;
    let mut v___x_2559_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2551_ = lean_string_utf8_byte_size(v_s_2543_);
                v___x_2552_ = lean_nat_dec_eq(v_p_2544_, v___x_2551_);
                if v___x_2552_ == 0 {
                    v___x_2553_ = lean_string_utf8_get_fast(v_s_2543_, v_p_2544_);
                    v___x_2554_ = 65;
                    v___x_2555_ = lean_uint32_dec_le(v___x_2554_, v___x_2553_);
                    if v___x_2555_ == 0 {
                        v___y_2546_ = v___x_2553_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2556_ = 90;
                        v___x_2557_ = lean_uint32_dec_le(v___x_2553_, v___x_2556_);
                        if v___x_2557_ == 0 {
                            v___y_2546_ = v___x_2553_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2558_ = 32;
                            v___x_2559_ = lean_uint32_add(v___x_2553_, v___x_2558_);
                            v___y_2546_ = v___x_2559_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_p_2544_);
                    return v_s_2543_;
                }
            }
            1 => {
                lean_inc(v_p_2544_);
                v___x_2547_ = lean_string_utf8_set(v_s_2543_, v_p_2544_, v___y_2546_);
                v___x_2548_ = l_Char_utf8Size(v___y_2546_);
                v___x_2549_ = lean_nat_add(v_p_2544_, v___x_2548_);
                lean_dec(v___x_2548_);
                lean_dec(v_p_2544_);
                v_s_2543_ = v___x_2547_;
                v_p_2544_ = v___x_2549_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(
    mut v_dir_2563_: u8,
    mut v_writer_2564_: *mut LeanObject,
) -> u8 {
    let mut v___y_2566_: u8 = 0;
    let mut v_messageHead_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    let mut v___x_2573_: u8 = 0;
    let mut v_entries_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_dir_2563_ == 0 {
                    v___x_2585_ = 1;
                    v___y_2566_ = v___x_2585_;
                    state = 1;
                    continue;
                } else {
                    v___x_2586_ = 0;
                    v___y_2566_ = v___x_2586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_messageHead_2567_ = lean_ctor_get(v_writer_2564_, 4);
                v___x_2568_ =
                    l_Std_Http_Protocol_H1_Message_Head_headers(v___y_2566_, v_messageHead_2567_);
                v___x_2569_ = l_Std_Http_Header_Name_connection;
                v___f_2570_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0;
                v___f_2571_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1;
                v___x_2572_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_2570_,
                    v___f_2571_,
                    v___x_2569_,
                    v___x_2568_,
                );
                if v___x_2572_ == 0 {
                    lean_dec_ref(v___x_2568_);
                    v___x_2573_ = 1;
                    return v___x_2573_;
                } else {
                    v_entries_2574_ = lean_ctor_get(v___x_2568_, 0);
                    lean_inc_ref(v_entries_2574_);
                    v_indexes_2575_ = lean_ctor_get(v___x_2568_, 1);
                    lean_inc_ref(v_indexes_2575_);
                    lean_dec_ref(v___x_2568_);
                    v___x_2576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_2575_, v___x_2569_);
                    lean_dec_ref(v_indexes_2575_);
                    v___x_2577_ = lean_unsigned_to_nat(0);
                    v_entry_2578_ = lean_array_fget(v___x_2576_, v___x_2577_);
                    lean_dec(v___x_2576_);
                    v___x_2579_ = lean_array_fget(v_entries_2574_, v_entry_2578_);
                    lean_dec(v_entry_2578_);
                    lean_dec_ref(v_entries_2574_);
                    v_snd_2580_ = lean_ctor_get(v___x_2579_, 1);
                    lean_inc(v_snd_2580_);
                    lean_dec(v___x_2579_);
                    v___x_2581_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_2580_, v___x_2577_);
                    v___x_2582_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2;
                    v___x_2583_ = lean_string_dec_eq(v___x_2581_, v___x_2582_);
                    lean_dec_ref(v___x_2581_);
                    if v___x_2583_ == 0 {
                        return v___x_2572_;
                    } else {
                        v___x_2584_ = 0;
                        return v___x_2584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(
    mut v_dir_2587_: *mut LeanObject,
    mut v_writer_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2589_: u8 = 0;
    let mut v_res_2590_: u8 = 0;
    let mut v_r_2591_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2589_ = (lean_unbox(v_dir_2587_) as u8);
    v_res_2590_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_2589_, v_writer_2588_);
    lean_dec_ref(v_writer_2588_);
    v_r_2591_ = lean_box((v_res_2590_) as usize);
    return v_r_2591_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(
    mut v_00_u03b2_2592_: *mut LeanObject,
    mut v_m_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_hma_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    v___x_2596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_2593_, v_a_2594_);
    return v___x_2596_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(
    mut v_00_u03b2_2597_: *mut LeanObject,
    mut v_m_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_hma_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2601_: *mut LeanObject = core::ptr::null_mut();
    v_res_2601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_2597_, v_m_2598_, v_a_2599_, v_hma_2600_);
    lean_dec_ref(v_a_2599_);
    lean_dec_ref(v_m_2598_);
    return v_res_2601_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(
    mut v_00_u03b2_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
    mut v_x_2604_: *mut LeanObject,
    mut v_x_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    v___x_2606_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_2603_, v_x_2604_);
    return v___x_2606_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(
    mut v_00_u03b2_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_x_2609_: *mut LeanObject,
    mut v_x_2610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2611_: *mut LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_2607_, v_a_2608_, v_x_2609_, v_x_2610_);
    lean_dec(v_x_2609_);
    lean_dec_ref(v_a_2608_);
    return v_res_2611_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_close___redArg(
    mut v_writer_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2617_: u8 = 0;
    let mut v_userClosedBody_2618_: u8 = 0;
    let mut v_omitBody_2619_: u8 = 0;
    let mut v_userDataBytes_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_unused_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2613_ = lean_ctor_get(v_writer_2612_, 0);
                v_outputData_2614_ = lean_ctor_get(v_writer_2612_, 1);
                v_knownSize_2615_ = lean_ctor_get(v_writer_2612_, 3);
                v_messageHead_2616_ = lean_ctor_get(v_writer_2612_, 4);
                v_sentMessage_2617_ = lean_ctor_get_uint8(
                    v_writer_2612_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2618_ = lean_ctor_get_uint8(
                    v_writer_2612_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2619_ = lean_ctor_get_uint8(
                    v_writer_2612_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2620_ = lean_ctor_get(v_writer_2612_, 5);
                v_isSharedCheck_2628_ = (!lean_is_exclusive(v_writer_2612_)) as u8;
                if v_isSharedCheck_2628_ == 0 {
                    v_unused_2629_ = lean_ctor_get(v_writer_2612_, 2);
                    lean_dec(v_unused_2629_);
                    v___x_2622_ = v_writer_2612_;
                    v_isShared_2623_ = v_isSharedCheck_2628_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2620_);
                    lean_inc(v_messageHead_2616_);
                    lean_inc(v_knownSize_2615_);
                    lean_inc(v_outputData_2614_);
                    lean_inc(v_userData_2613_);
                    lean_dec(v_writer_2612_);
                    v___x_2622_ = lean_box(0);
                    v_isShared_2623_ = v_isSharedCheck_2628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2624_ = lean_box(7);
                if v_isShared_2623_ == 0 {
                    lean_ctor_set(v___x_2622_, 2, v___x_2624_);
                    v___x_2626_ = v___x_2622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_userData_2613_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_outputData_2614_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 2, v___x_2624_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 3, v_knownSize_2615_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 4, v_messageHead_2616_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 5, v_userDataBytes_2620_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2617_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2618_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2619_,
                    );
                    v___x_2626_ = v_reuseFailAlloc_2627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_close(
    mut v_dir_2630_: u8,
    mut v_writer_2631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userData_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outputData_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messageHead_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sentMessage_2636_: u8 = 0;
    let mut v_userClosedBody_2637_: u8 = 0;
    let mut v_omitBody_2638_: u8 = 0;
    let mut v_userDataBytes_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2642_: u8 = 0;
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v_unused_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userData_2632_ = lean_ctor_get(v_writer_2631_, 0);
                v_outputData_2633_ = lean_ctor_get(v_writer_2631_, 1);
                v_knownSize_2634_ = lean_ctor_get(v_writer_2631_, 3);
                v_messageHead_2635_ = lean_ctor_get(v_writer_2631_, 4);
                v_sentMessage_2636_ = lean_ctor_get_uint8(
                    v_writer_2631_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_userClosedBody_2637_ = lean_ctor_get_uint8(
                    v_writer_2631_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_omitBody_2638_ = lean_ctor_get_uint8(
                    v_writer_2631_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                );
                v_userDataBytes_2639_ = lean_ctor_get(v_writer_2631_, 5);
                v_isSharedCheck_2647_ = (!lean_is_exclusive(v_writer_2631_)) as u8;
                if v_isSharedCheck_2647_ == 0 {
                    v_unused_2648_ = lean_ctor_get(v_writer_2631_, 2);
                    lean_dec(v_unused_2648_);
                    v___x_2641_ = v_writer_2631_;
                    v_isShared_2642_ = v_isSharedCheck_2647_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_userDataBytes_2639_);
                    lean_inc(v_messageHead_2635_);
                    lean_inc(v_knownSize_2634_);
                    lean_inc(v_outputData_2633_);
                    lean_inc(v_userData_2632_);
                    lean_dec(v_writer_2631_);
                    v___x_2641_ = lean_box(0);
                    v_isShared_2642_ = v_isSharedCheck_2647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2643_ = lean_box(7);
                if v_isShared_2642_ == 0 {
                    lean_ctor_set(v___x_2641_, 2, v___x_2643_);
                    v___x_2645_ = v___x_2641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 6, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_userData_2632_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_outputData_2633_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 2, v___x_2643_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_knownSize_2634_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_messageHead_2635_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 5, v_userDataBytes_2639_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2646_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        v_sentMessage_2636_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2646_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                        v_userClosedBody_2637_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2646_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                        v_omitBody_2638_,
                    );
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Writer_close___boxed(
    mut v_dir_2649_: *mut LeanObject,
    mut v_writer_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_2651_: u8 = 0;
    let mut v_res_2652_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_2651_ = (lean_unbox(v_dir_2649_) as u8);
    v_res_2652_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_2651_, v_writer_2650_);
    return v_res_2652_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Writer(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Http_Protocol_H1_Writer_instInhabitedState_default =
        _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default();
    lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState_default);
    l_Std_Http_Protocol_H1_Writer_instInhabitedState =
        _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState();
    lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Writer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Protocol_H1_Writer(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Writer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Writer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Writer(builtin);
}
