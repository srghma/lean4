// Lean compiler output
// Module: Lake.Util.Url
// Imports: Lake.Util.Log Lake.Util.JsonObject Lake.Util.Proc Init.Data.String.TakeDrop Init.Data.String.Search Init.TacticsExtra
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::Log::{initialize_Lake_Util_Log, runtime_initialize_Lake_Util_Log};
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, l_Lake_captureProc_x27, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getNat_x3f, l_Lean_Json_getObj_x3f};
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_land, lean_uint8_lor, lean_uint8_shift_right, lean_uint32_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_to_uint8, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size, lean_uint8_dec_eq,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
pub static l_Lake_foldlUtf8___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_foldlUtf8___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_foldlUtf8___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_foldlUtf8___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_foldlUtf8___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_foldlUtf8___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_foldlUtf8___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
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
static mut l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 72, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_getUrl_x3f___closed__0_value: crate::leanh::LeanStringObject<61> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 61,
        m_capacity: 61,
        m_length: 60,
        m_data: [
            99, 117, 114, 108, 39, 115, 32, 74, 83, 79, 78, 32, 111, 117, 116, 112, 117, 116, 32,
            99, 111, 110, 116, 97, 105, 110, 101, 100, 32, 97, 110, 32, 105, 110, 118, 97, 108,
            105, 100, 32, 74, 83, 79, 78, 32, 114, 101, 115, 112, 111, 110, 115, 101, 32, 99, 111,
            100, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__1_value: crate::leanh::LeanStringObject<51> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            99, 117, 114, 108, 39, 115, 32, 74, 83, 79, 78, 32, 111, 117, 116, 112, 117, 116, 32,
            100, 105, 100, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 97, 32, 114,
            101, 115, 112, 111, 110, 115, 101, 32, 99, 111, 100, 101, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            3 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__3_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            99, 117, 114, 108, 32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 105, 110, 118, 97,
            108, 105, 100, 32, 74, 83, 79, 78, 32, 111, 117, 116, 112, 117, 116, 58, 32, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__4_value: crate::leanh::LeanStringObject<26> =
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
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 71, 69, 84, 32, 85, 82, 76, 44, 32, 101,
            114, 114, 111, 114, 32, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__5_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [59, 32, 114, 101, 99, 101, 105, 118, 101, 100, 58, 10, 0],
    };
static mut l_Lake_getUrl_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__6_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [104, 116, 116, 112, 95, 99, 111, 100, 101, 0],
    };
static mut l_Lake_getUrl_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__7_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [104, 116, 116, 112, 95, 99, 111, 100, 101, 58, 32, 0],
    };
static mut l_Lake_getUrl_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [65793 as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_getUrl_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__9_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 117, 114, 108, 0],
    };
static mut l_Lake_getUrl_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__10_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_getUrl_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__11_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            114, 101, 115, 112, 111, 110, 115, 101, 95, 99, 111, 100, 101, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__12_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [45, 115, 0],
    };
static mut l_Lake_getUrl_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__13_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [45, 76, 0],
    };
static mut l_Lake_getUrl_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__14_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [45, 119, 0],
    };
static mut l_Lake_getUrl_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__15_value: crate::leanh::LeanStringObject<18> =
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
            37, 123, 115, 116, 100, 101, 114, 114, 125, 37, 123, 106, 115, 111, 110, 125, 10, 0,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__16_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [45, 45, 114, 101, 116, 114, 121, 0],
    };
static mut l_Lake_getUrl_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__17_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [51, 0],
    };
static mut l_Lake_getUrl_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl_x3f___closed__18_value: crate::leanh::LeanArrayObject<6> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 6,
        m_capacity: 6,
        m_data: [
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_getUrl_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUrl___closed__0_value: crate::leanh::LeanArrayObject<4> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_getUrl_x3f___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_getUrl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUrl___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_hexEncodeByte(mut v_b_751_: u8) -> u32 {
    let mut v___x_752_: u8 = 0;
    let mut v___x_753_: u8 = 0;
    v___x_752_ = 0;
    v___x_753_ = lean_uint8_dec_eq(v_b_751_, v___x_752_);
    if v___x_753_ == 0 {
        let mut v___x_754_: u8 = 0;
        let mut v___x_755_: u8 = 0;
        v___x_754_ = 1;
        v___x_755_ = lean_uint8_dec_eq(v_b_751_, v___x_754_);
        if v___x_755_ == 0 {
            let mut v___x_756_: u8 = 0;
            let mut v___x_757_: u8 = 0;
            v___x_756_ = 2;
            v___x_757_ = lean_uint8_dec_eq(v_b_751_, v___x_756_);
            if v___x_757_ == 0 {
                let mut v___x_758_: u8 = 0;
                let mut v___x_759_: u8 = 0;
                v___x_758_ = 3;
                v___x_759_ = lean_uint8_dec_eq(v_b_751_, v___x_758_);
                if v___x_759_ == 0 {
                    let mut v___x_760_: u8 = 0;
                    let mut v___x_761_: u8 = 0;
                    v___x_760_ = 4;
                    v___x_761_ = lean_uint8_dec_eq(v_b_751_, v___x_760_);
                    if v___x_761_ == 0 {
                        let mut v___x_762_: u8 = 0;
                        let mut v___x_763_: u8 = 0;
                        v___x_762_ = 5;
                        v___x_763_ = lean_uint8_dec_eq(v_b_751_, v___x_762_);
                        if v___x_763_ == 0 {
                            let mut v___x_764_: u8 = 0;
                            let mut v___x_765_: u8 = 0;
                            v___x_764_ = 6;
                            v___x_765_ = lean_uint8_dec_eq(v_b_751_, v___x_764_);
                            if v___x_765_ == 0 {
                                let mut v___x_766_: u8 = 0;
                                let mut v___x_767_: u8 = 0;
                                v___x_766_ = 7;
                                v___x_767_ = lean_uint8_dec_eq(v_b_751_, v___x_766_);
                                if v___x_767_ == 0 {
                                    let mut v___x_768_: u8 = 0;
                                    let mut v___x_769_: u8 = 0;
                                    v___x_768_ = 8;
                                    v___x_769_ = lean_uint8_dec_eq(v_b_751_, v___x_768_);
                                    if v___x_769_ == 0 {
                                        let mut v___x_770_: u8 = 0;
                                        let mut v___x_771_: u8 = 0;
                                        v___x_770_ = 9;
                                        v___x_771_ = lean_uint8_dec_eq(v_b_751_, v___x_770_);
                                        if v___x_771_ == 0 {
                                            let mut v___x_772_: u8 = 0;
                                            let mut v___x_773_: u8 = 0;
                                            v___x_772_ = 10;
                                            v___x_773_ = lean_uint8_dec_eq(v_b_751_, v___x_772_);
                                            if v___x_773_ == 0 {
                                                let mut v___x_774_: u8 = 0;
                                                let mut v___x_775_: u8 = 0;
                                                v___x_774_ = 11;
                                                v___x_775_ =
                                                    lean_uint8_dec_eq(v_b_751_, v___x_774_);
                                                if v___x_775_ == 0 {
                                                    let mut v___x_776_: u8 = 0;
                                                    let mut v___x_777_: u8 = 0;
                                                    v___x_776_ = 12;
                                                    v___x_777_ =
                                                        lean_uint8_dec_eq(v_b_751_, v___x_776_);
                                                    if v___x_777_ == 0 {
                                                        let mut v___x_778_: u8 = 0;
                                                        let mut v___x_779_: u8 = 0;
                                                        v___x_778_ = 13;
                                                        v___x_779_ =
                                                            lean_uint8_dec_eq(v_b_751_, v___x_778_);
                                                        if v___x_779_ == 0 {
                                                            let mut v___x_780_: u8 = 0;
                                                            let mut v___x_781_: u8 = 0;
                                                            v___x_780_ = 14;
                                                            v___x_781_ = lean_uint8_dec_eq(
                                                                v_b_751_, v___x_780_,
                                                            );
                                                            if v___x_781_ == 0 {
                                                                let mut v___x_782_: u8 = 0;
                                                                let mut v___x_783_: u8 = 0;
                                                                v___x_782_ = 15;
                                                                v___x_783_ = lean_uint8_dec_eq(
                                                                    v_b_751_, v___x_782_,
                                                                );
                                                                if v___x_783_ == 0 {
                                                                    let mut v___x_784_: u32 = 0;
                                                                    v___x_784_ = 42;
                                                                    return v___x_784_;
                                                                } else {
                                                                    let mut v___x_785_: u32 = 0;
                                                                    v___x_785_ = 70;
                                                                    return v___x_785_;
                                                                }
                                                            } else {
                                                                let mut v___x_786_: u32 = 0;
                                                                v___x_786_ = 69;
                                                                return v___x_786_;
                                                            }
                                                        } else {
                                                            let mut v___x_787_: u32 = 0;
                                                            v___x_787_ = 68;
                                                            return v___x_787_;
                                                        }
                                                    } else {
                                                        let mut v___x_788_: u32 = 0;
                                                        v___x_788_ = 67;
                                                        return v___x_788_;
                                                    }
                                                } else {
                                                    let mut v___x_789_: u32 = 0;
                                                    v___x_789_ = 66;
                                                    return v___x_789_;
                                                }
                                            } else {
                                                let mut v___x_790_: u32 = 0;
                                                v___x_790_ = 65;
                                                return v___x_790_;
                                            }
                                        } else {
                                            let mut v___x_791_: u32 = 0;
                                            v___x_791_ = 57;
                                            return v___x_791_;
                                        }
                                    } else {
                                        let mut v___x_792_: u32 = 0;
                                        v___x_792_ = 56;
                                        return v___x_792_;
                                    }
                                } else {
                                    let mut v___x_793_: u32 = 0;
                                    v___x_793_ = 55;
                                    return v___x_793_;
                                }
                            } else {
                                let mut v___x_794_: u32 = 0;
                                v___x_794_ = 54;
                                return v___x_794_;
                            }
                        } else {
                            let mut v___x_795_: u32 = 0;
                            v___x_795_ = 53;
                            return v___x_795_;
                        }
                    } else {
                        let mut v___x_796_: u32 = 0;
                        v___x_796_ = 52;
                        return v___x_796_;
                    }
                } else {
                    let mut v___x_797_: u32 = 0;
                    v___x_797_ = 51;
                    return v___x_797_;
                }
            } else {
                let mut v___x_798_: u32 = 0;
                v___x_798_ = 50;
                return v___x_798_;
            }
        } else {
            let mut v___x_799_: u32 = 0;
            v___x_799_ = 49;
            return v___x_799_;
        }
    } else {
        let mut v___x_800_: u32 = 0;
        v___x_800_ = 48;
        return v___x_800_;
    }
}
pub unsafe fn l_Lake_hexEncodeByte___boxed(
    mut v_b_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_802_: u8 = 0;
    let mut v_res_803_: u32 = 0;
    let mut v_r_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_802_ = (crate::leanh::lean_unbox(v_b_801_) as u8);
    v_res_803_ = l_Lake_hexEncodeByte(v_b_boxed_802_);
    v_r_804_ = crate::leanh::lean_box_uint32(v_res_803_);
    return v_r_804_;
}
pub unsafe fn l_Lake_uriEscapeByte(
    mut v_b_805_: u8,
    mut v_s_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: u32 = 0;
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: u32 = 0;
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: u8 = 0;
    let mut v___x_815_: u32 = 0;
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = 37;
    v___x_808_ = lean_string_push(v_s_806_, v___x_807_);
    v___x_809_ = 4;
    v___x_810_ = lean_uint8_shift_right(v_b_805_, v___x_809_);
    v___x_811_ = l_Lake_hexEncodeByte(v___x_810_);
    v___x_812_ = lean_string_push(v___x_808_, v___x_811_);
    v___x_813_ = 15;
    v___x_814_ = lean_uint8_land(v_b_805_, v___x_813_);
    v___x_815_ = l_Lake_hexEncodeByte(v___x_814_);
    v___x_816_ = lean_string_push(v___x_812_, v___x_815_);
    return v___x_816_;
}
pub unsafe fn l_Lake_uriEscapeByte___boxed(
    mut v_b_817_: *mut crate::leanh::LeanObject,
    mut v_s_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_819_: u8 = 0;
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_819_ = (crate::leanh::lean_unbox(v_b_817_) as u8);
    v_res_820_ = l_Lake_uriEscapeByte(v_b_boxed_819_, v_s_818_);
    return v_res_820_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__0(
    mut v_c_821_: u32,
    mut v___x_822_: u8,
    mut v___x_823_: u8,
    mut v_f_824_: *mut crate::leanh::LeanObject,
    mut v_s_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = lean_uint32_to_uint8(v_c_821_);
    v___x_827_ = lean_uint8_land(v___x_826_, v___x_822_);
    v___x_828_ = lean_uint8_lor(v___x_827_, v___x_823_);
    v___x_829_ = crate::leanh::lean_box((v___x_828_) as usize);
    v___x_830_ = crate::leanh::lean_apply_2(v_f_824_, v_s_825_, v___x_829_);
    return v___x_830_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__0___boxed(
    mut v_c_831_: *mut crate::leanh::LeanObject,
    mut v___x_832_: *mut crate::leanh::LeanObject,
    mut v___x_833_: *mut crate::leanh::LeanObject,
    mut v_f_834_: *mut crate::leanh::LeanObject,
    mut v_s_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_836_: u32 = 0;
    let mut v___x_393__boxed_837_: u8 = 0;
    let mut v___x_394__boxed_838_: u8 = 0;
    let mut v_res_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_836_ = crate::leanh::lean_unbox_uint32(v_c_831_);
    crate::leanh::lean_dec(v_c_831_);
    v___x_393__boxed_837_ = (crate::leanh::lean_unbox(v___x_832_) as u8);
    v___x_394__boxed_838_ = (crate::leanh::lean_unbox(v___x_833_) as u8);
    v_res_839_ = l_Lake_foldlUtf8M___redArg___lam__0(
        v_c_boxed_836_,
        v___x_393__boxed_837_,
        v___x_394__boxed_838_,
        v_f_834_,
        v_s_835_,
    );
    return v_res_839_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__1(
    mut v_c_840_: u32,
    mut v___x_841_: u8,
    mut v___x_842_: u8,
    mut v_f_843_: *mut crate::leanh::LeanObject,
    mut v_toBind_844_: *mut crate::leanh::LeanObject,
    mut v___f_845_: *mut crate::leanh::LeanObject,
    mut v_s_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: u32 = 0;
    let mut v___x_848_: u32 = 0;
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = 6;
    v___x_848_ = lean_uint32_shift_right(v_c_840_, v___x_847_);
    v___x_849_ = lean_uint32_to_uint8(v___x_848_);
    v___x_850_ = lean_uint8_land(v___x_849_, v___x_841_);
    v___x_851_ = lean_uint8_lor(v___x_850_, v___x_842_);
    v___x_852_ = crate::leanh::lean_box((v___x_851_) as usize);
    v___x_853_ = crate::leanh::lean_apply_2(v_f_843_, v_s_846_, v___x_852_);
    v___x_854_ = crate::leanh::lean_apply_4(
        v_toBind_844_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_853_,
        v___f_845_,
    );
    return v___x_854_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__1___boxed(
    mut v_c_855_: *mut crate::leanh::LeanObject,
    mut v___x_856_: *mut crate::leanh::LeanObject,
    mut v___x_857_: *mut crate::leanh::LeanObject,
    mut v_f_858_: *mut crate::leanh::LeanObject,
    mut v_toBind_859_: *mut crate::leanh::LeanObject,
    mut v___f_860_: *mut crate::leanh::LeanObject,
    mut v_s_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_862_: u32 = 0;
    let mut v___x_409__boxed_863_: u8 = 0;
    let mut v___x_410__boxed_864_: u8 = 0;
    let mut v_res_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_862_ = crate::leanh::lean_unbox_uint32(v_c_855_);
    crate::leanh::lean_dec(v_c_855_);
    v___x_409__boxed_863_ = (crate::leanh::lean_unbox(v___x_856_) as u8);
    v___x_410__boxed_864_ = (crate::leanh::lean_unbox(v___x_857_) as u8);
    v_res_865_ = l_Lake_foldlUtf8M___redArg___lam__1(
        v_c_boxed_862_,
        v___x_409__boxed_863_,
        v___x_410__boxed_864_,
        v_f_858_,
        v_toBind_859_,
        v___f_860_,
        v_s_861_,
    );
    return v_res_865_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__2(
    mut v_c_866_: u32,
    mut v_f_867_: *mut crate::leanh::LeanObject,
    mut v_toBind_868_: *mut crate::leanh::LeanObject,
    mut v_s_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: u32 = 0;
    let mut v___x_871_: u32 = 0;
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: u8 = 0;
    let mut v___x_874_: u8 = 0;
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = 12;
    v___x_871_ = lean_uint32_shift_right(v_c_866_, v___x_870_);
    v___x_872_ = lean_uint32_to_uint8(v___x_871_);
    v___x_873_ = 63;
    v___x_874_ = lean_uint8_land(v___x_872_, v___x_873_);
    v___x_875_ = 128;
    v___x_876_ = crate::leanh::lean_box_uint32(v_c_866_);
    v___x_877_ = crate::leanh::lean_box((v___x_873_) as usize);
    v___x_878_ = crate::leanh::lean_box((v___x_875_) as usize);
    crate::leanh::lean_inc_n(v_f_867_, 2);
    v___f_879_ = crate::leanh::lean_alloc_closure(
        l_Lake_foldlUtf8M___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_879_, 0, v___x_876_);
    crate::leanh::lean_closure_set(v___f_879_, 1, v___x_877_);
    crate::leanh::lean_closure_set(v___f_879_, 2, v___x_878_);
    crate::leanh::lean_closure_set(v___f_879_, 3, v_f_867_);
    v___x_880_ = crate::leanh::lean_box_uint32(v_c_866_);
    v___x_881_ = crate::leanh::lean_box((v___x_873_) as usize);
    v___x_882_ = crate::leanh::lean_box((v___x_875_) as usize);
    crate::leanh::lean_inc(v_toBind_868_);
    v___f_883_ = crate::leanh::lean_alloc_closure(
        l_Lake_foldlUtf8M___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_883_, 0, v___x_880_);
    crate::leanh::lean_closure_set(v___f_883_, 1, v___x_881_);
    crate::leanh::lean_closure_set(v___f_883_, 2, v___x_882_);
    crate::leanh::lean_closure_set(v___f_883_, 3, v_f_867_);
    crate::leanh::lean_closure_set(v___f_883_, 4, v_toBind_868_);
    crate::leanh::lean_closure_set(v___f_883_, 5, v___f_879_);
    v___x_884_ = lean_uint8_lor(v___x_874_, v___x_875_);
    v___x_885_ = crate::leanh::lean_box((v___x_884_) as usize);
    v___x_886_ = crate::leanh::lean_apply_2(v_f_867_, v_s_869_, v___x_885_);
    v___x_887_ = crate::leanh::lean_apply_4(
        v_toBind_868_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_886_,
        v___f_883_,
    );
    return v___x_887_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__2___boxed(
    mut v_c_888_: *mut crate::leanh::LeanObject,
    mut v_f_889_: *mut crate::leanh::LeanObject,
    mut v_toBind_890_: *mut crate::leanh::LeanObject,
    mut v_s_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_892_: u32 = 0;
    let mut v_res_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_892_ = crate::leanh::lean_unbox_uint32(v_c_888_);
    crate::leanh::lean_dec(v_c_888_);
    v_res_893_ =
        l_Lake_foldlUtf8M___redArg___lam__2(v_c_boxed_892_, v_f_889_, v_toBind_890_, v_s_891_);
    return v_res_893_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__4(
    mut v_c_894_: u32,
    mut v_f_895_: *mut crate::leanh::LeanObject,
    mut v_toBind_896_: *mut crate::leanh::LeanObject,
    mut v_s_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_898_: u32 = 0;
    let mut v___x_899_: u32 = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_898_ = 6;
    v___x_899_ = lean_uint32_shift_right(v_c_894_, v___x_898_);
    v___x_900_ = lean_uint32_to_uint8(v___x_899_);
    v___x_901_ = 63;
    v___x_902_ = lean_uint8_land(v___x_900_, v___x_901_);
    v___x_903_ = 128;
    v___x_904_ = crate::leanh::lean_box_uint32(v_c_894_);
    v___x_905_ = crate::leanh::lean_box((v___x_901_) as usize);
    v___x_906_ = crate::leanh::lean_box((v___x_903_) as usize);
    crate::leanh::lean_inc(v_f_895_);
    v___f_907_ = crate::leanh::lean_alloc_closure(
        l_Lake_foldlUtf8M___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_907_, 0, v___x_904_);
    crate::leanh::lean_closure_set(v___f_907_, 1, v___x_905_);
    crate::leanh::lean_closure_set(v___f_907_, 2, v___x_906_);
    crate::leanh::lean_closure_set(v___f_907_, 3, v_f_895_);
    v___x_908_ = lean_uint8_lor(v___x_902_, v___x_903_);
    v___x_909_ = crate::leanh::lean_box((v___x_908_) as usize);
    v___x_910_ = crate::leanh::lean_apply_2(v_f_895_, v_s_897_, v___x_909_);
    v___x_911_ = crate::leanh::lean_apply_4(
        v_toBind_896_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_910_,
        v___f_907_,
    );
    return v___x_911_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__4___boxed(
    mut v_c_912_: *mut crate::leanh::LeanObject,
    mut v_f_913_: *mut crate::leanh::LeanObject,
    mut v_toBind_914_: *mut crate::leanh::LeanObject,
    mut v_s_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_916_: u32 = 0;
    let mut v_res_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_916_ = crate::leanh::lean_unbox_uint32(v_c_912_);
    crate::leanh::lean_dec(v_c_912_);
    v_res_917_ =
        l_Lake_foldlUtf8M___redArg___lam__4(v_c_boxed_916_, v_f_913_, v_toBind_914_, v_s_915_);
    return v_res_917_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__3(
    mut v_c_918_: u32,
    mut v_f_919_: *mut crate::leanh::LeanObject,
    mut v_s_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: u8 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = lean_uint32_to_uint8(v_c_918_);
    v___x_922_ = 63;
    v___x_923_ = lean_uint8_land(v___x_921_, v___x_922_);
    v___x_924_ = 128;
    v___x_925_ = lean_uint8_lor(v___x_923_, v___x_924_);
    v___x_926_ = crate::leanh::lean_box((v___x_925_) as usize);
    v___x_927_ = crate::leanh::lean_apply_2(v_f_919_, v_s_920_, v___x_926_);
    return v___x_927_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___lam__3___boxed(
    mut v_c_928_: *mut crate::leanh::LeanObject,
    mut v_f_929_: *mut crate::leanh::LeanObject,
    mut v_s_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_931_: u32 = 0;
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_931_ = crate::leanh::lean_unbox_uint32(v_c_928_);
    crate::leanh::lean_dec(v_c_928_);
    v_res_932_ = l_Lake_foldlUtf8M___redArg___lam__3(v_c_boxed_931_, v_f_929_, v_s_930_);
    return v_res_932_;
}
pub unsafe fn l_Lake_foldlUtf8M___redArg(
    mut v_inst_933_: *mut crate::leanh::LeanObject,
    mut v_c_934_: u32,
    mut v_f_935_: *mut crate::leanh::LeanObject,
    mut v_init_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: u32 = 0;
    let mut v___x_938_: u8 = 0;
    v___x_937_ = 127;
    v___x_938_ = lean_uint32_dec_le(v_c_934_, v___x_937_);
    if v___x_938_ == 0 {
        let mut v___x_939_: u32 = 0;
        let mut v___x_940_: u8 = 0;
        v___x_939_ = 2047;
        v___x_940_ = lean_uint32_dec_le(v_c_934_, v___x_939_);
        if v___x_940_ == 0 {
            let mut v___x_941_: u32 = 0;
            let mut v___x_942_: u8 = 0;
            v___x_941_ = 65535;
            v___x_942_ = lean_uint32_dec_le(v_c_934_, v___x_941_);
            if v___x_942_ == 0 {
                let mut v_toBind_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_946_: u32 = 0;
                let mut v___x_947_: u32 = 0;
                let mut v___x_948_: u8 = 0;
                let mut v___x_949_: u8 = 0;
                let mut v___x_950_: u8 = 0;
                let mut v___x_951_: u8 = 0;
                let mut v___x_952_: u8 = 0;
                let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_toBind_943_ = crate::leanh::lean_ctor_get(v_inst_933_, 1);
                crate::leanh::lean_inc_n(v_toBind_943_, 2);
                crate::leanh::lean_dec_ref(v_inst_933_);
                v___x_944_ = crate::leanh::lean_box_uint32(v_c_934_);
                crate::leanh::lean_inc(v_f_935_);
                v___f_945_ = crate::leanh::lean_alloc_closure(
                    l_Lake_foldlUtf8M___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_945_, 0, v___x_944_);
                crate::leanh::lean_closure_set(v___f_945_, 1, v_f_935_);
                crate::leanh::lean_closure_set(v___f_945_, 2, v_toBind_943_);
                v___x_946_ = 18;
                v___x_947_ = lean_uint32_shift_right(v_c_934_, v___x_946_);
                v___x_948_ = lean_uint32_to_uint8(v___x_947_);
                v___x_949_ = 7;
                v___x_950_ = lean_uint8_land(v___x_948_, v___x_949_);
                v___x_951_ = 240;
                v___x_952_ = lean_uint8_lor(v___x_950_, v___x_951_);
                v___x_953_ = crate::leanh::lean_box((v___x_952_) as usize);
                v___x_954_ = crate::leanh::lean_apply_2(v_f_935_, v_init_936_, v___x_953_);
                v___x_955_ = crate::leanh::lean_apply_4(
                    v_toBind_943_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_954_,
                    v___f_945_,
                );
                return v___x_955_;
            } else {
                let mut v_toBind_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_959_: u32 = 0;
                let mut v___x_960_: u32 = 0;
                let mut v___x_961_: u8 = 0;
                let mut v___x_962_: u8 = 0;
                let mut v___x_963_: u8 = 0;
                let mut v___x_964_: u8 = 0;
                let mut v___x_965_: u8 = 0;
                let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_toBind_956_ = crate::leanh::lean_ctor_get(v_inst_933_, 1);
                crate::leanh::lean_inc_n(v_toBind_956_, 2);
                crate::leanh::lean_dec_ref(v_inst_933_);
                v___x_957_ = crate::leanh::lean_box_uint32(v_c_934_);
                crate::leanh::lean_inc(v_f_935_);
                v___f_958_ = crate::leanh::lean_alloc_closure(
                    l_Lake_foldlUtf8M___redArg___lam__4___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_958_, 0, v___x_957_);
                crate::leanh::lean_closure_set(v___f_958_, 1, v_f_935_);
                crate::leanh::lean_closure_set(v___f_958_, 2, v_toBind_956_);
                v___x_959_ = 12;
                v___x_960_ = lean_uint32_shift_right(v_c_934_, v___x_959_);
                v___x_961_ = lean_uint32_to_uint8(v___x_960_);
                v___x_962_ = 15;
                v___x_963_ = lean_uint8_land(v___x_961_, v___x_962_);
                v___x_964_ = 224;
                v___x_965_ = lean_uint8_lor(v___x_963_, v___x_964_);
                v___x_966_ = crate::leanh::lean_box((v___x_965_) as usize);
                v___x_967_ = crate::leanh::lean_apply_2(v_f_935_, v_init_936_, v___x_966_);
                v___x_968_ = crate::leanh::lean_apply_4(
                    v_toBind_956_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_967_,
                    v___f_958_,
                );
                return v___x_968_;
            }
        } else {
            let mut v_toBind_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_972_: u32 = 0;
            let mut v___x_973_: u32 = 0;
            let mut v___x_974_: u8 = 0;
            let mut v___x_975_: u8 = 0;
            let mut v___x_976_: u8 = 0;
            let mut v___x_977_: u8 = 0;
            let mut v___x_978_: u8 = 0;
            let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_969_ = crate::leanh::lean_ctor_get(v_inst_933_, 1);
            crate::leanh::lean_inc(v_toBind_969_);
            crate::leanh::lean_dec_ref(v_inst_933_);
            v___x_970_ = crate::leanh::lean_box_uint32(v_c_934_);
            crate::leanh::lean_inc(v_f_935_);
            v___f_971_ = crate::leanh::lean_alloc_closure(
                l_Lake_foldlUtf8M___redArg___lam__3___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_971_, 0, v___x_970_);
            crate::leanh::lean_closure_set(v___f_971_, 1, v_f_935_);
            v___x_972_ = 6;
            v___x_973_ = lean_uint32_shift_right(v_c_934_, v___x_972_);
            v___x_974_ = lean_uint32_to_uint8(v___x_973_);
            v___x_975_ = 31;
            v___x_976_ = lean_uint8_land(v___x_974_, v___x_975_);
            v___x_977_ = 192;
            v___x_978_ = lean_uint8_lor(v___x_976_, v___x_977_);
            v___x_979_ = crate::leanh::lean_box((v___x_978_) as usize);
            v___x_980_ = crate::leanh::lean_apply_2(v_f_935_, v_init_936_, v___x_979_);
            v___x_981_ = crate::leanh::lean_apply_4(
                v_toBind_969_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_980_,
                v___f_971_,
            );
            return v___x_981_;
        }
    } else {
        let mut v___x_982_: u8 = 0;
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_933_);
        v___x_982_ = lean_uint32_to_uint8(v_c_934_);
        v___x_983_ = crate::leanh::lean_box((v___x_982_) as usize);
        v___x_984_ = crate::leanh::lean_apply_2(v_f_935_, v_init_936_, v___x_983_);
        return v___x_984_;
    }
}
pub unsafe fn l_Lake_foldlUtf8M___redArg___boxed(
    mut v_inst_985_: *mut crate::leanh::LeanObject,
    mut v_c_986_: *mut crate::leanh::LeanObject,
    mut v_f_987_: *mut crate::leanh::LeanObject,
    mut v_init_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_989_: u32 = 0;
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_989_ = crate::leanh::lean_unbox_uint32(v_c_986_);
    crate::leanh::lean_dec(v_c_986_);
    v_res_990_ = l_Lake_foldlUtf8M___redArg(v_inst_985_, v_c_boxed_989_, v_f_987_, v_init_988_);
    return v_res_990_;
}
pub unsafe fn l_Lake_foldlUtf8M(
    mut v_m_991_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_992_: *mut crate::leanh::LeanObject,
    mut v_inst_993_: *mut crate::leanh::LeanObject,
    mut v_c_994_: u32,
    mut v_f_995_: *mut crate::leanh::LeanObject,
    mut v_init_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_997_ = l_Lake_foldlUtf8M___redArg(v_inst_993_, v_c_994_, v_f_995_, v_init_996_);
    return v___x_997_;
}
pub unsafe fn l_Lake_foldlUtf8M___boxed(
    mut v_m_998_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_999_: *mut crate::leanh::LeanObject,
    mut v_inst_1000_: *mut crate::leanh::LeanObject,
    mut v_c_1001_: *mut crate::leanh::LeanObject,
    mut v_f_1002_: *mut crate::leanh::LeanObject,
    mut v_init_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1004_: u32 = 0;
    let mut v_res_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1004_ = crate::leanh::lean_unbox_uint32(v_c_1001_);
    crate::leanh::lean_dec(v_c_1001_);
    v_res_1005_ = l_Lake_foldlUtf8M(
        v_m_998_,
        v_00_u03c3_999_,
        v_inst_1000_,
        v_c_boxed_1004_,
        v_f_1002_,
        v_init_1003_,
    );
    return v_res_1005_;
}
pub unsafe fn l_Lake_foldlUtf8___redArg___lam__0(
    mut v_f_1006_: *mut crate::leanh::LeanObject,
    mut v_x1_1007_: *mut crate::leanh::LeanObject,
    mut v_x2_1008_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = crate::leanh::lean_box((v_x2_1008_) as usize);
    v___x_1010_ = crate::leanh::lean_apply_2(v_f_1006_, v_x1_1007_, v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn l_Lake_foldlUtf8___redArg___lam__0___boxed(
    mut v_f_1011_: *mut crate::leanh::LeanObject,
    mut v_x1_1012_: *mut crate::leanh::LeanObject,
    mut v_x2_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_83__boxed_1014_: u8 = 0;
    let mut v_res_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_83__boxed_1014_ = (crate::leanh::lean_unbox(v_x2_1013_) as u8);
    v_res_1015_ = l_Lake_foldlUtf8___redArg___lam__0(v_f_1011_, v_x1_1012_, v_x2_83__boxed_1014_);
    return v_res_1015_;
}
pub unsafe fn l_Lake_foldlUtf8___redArg(
    mut v_c_1035_: u32,
    mut v_f_1036_: *mut crate::leanh::LeanObject,
    mut v_init_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1038_ = crate::leanh::lean_alloc_closure(
        l_Lake_foldlUtf8___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1038_, 0, v_f_1036_);
    v___x_1039_ = l_Lake_foldlUtf8___redArg___closed__9;
    v___x_1040_ = l_Lake_foldlUtf8M___redArg(v___x_1039_, v_c_1035_, v___f_1038_, v_init_1037_);
    return v___x_1040_;
}
pub unsafe fn l_Lake_foldlUtf8___redArg___boxed(
    mut v_c_1041_: *mut crate::leanh::LeanObject,
    mut v_f_1042_: *mut crate::leanh::LeanObject,
    mut v_init_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1044_: u32 = 0;
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1044_ = crate::leanh::lean_unbox_uint32(v_c_1041_);
    crate::leanh::lean_dec(v_c_1041_);
    v_res_1045_ = l_Lake_foldlUtf8___redArg(v_c_boxed_1044_, v_f_1042_, v_init_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Lake_foldlUtf8(
    mut v_00_u03c3_1046_: *mut crate::leanh::LeanObject,
    mut v_c_1047_: u32,
    mut v_f_1048_: *mut crate::leanh::LeanObject,
    mut v_init_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1050_ = crate::leanh::lean_alloc_closure(
        l_Lake_foldlUtf8___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1050_, 0, v_f_1048_);
    v___x_1051_ = l_Lake_foldlUtf8___redArg___closed__9;
    v___x_1052_ = l_Lake_foldlUtf8M___redArg(v___x_1051_, v_c_1047_, v___f_1050_, v_init_1049_);
    return v___x_1052_;
}
pub unsafe fn l_Lake_foldlUtf8___boxed(
    mut v_00_u03c3_1053_: *mut crate::leanh::LeanObject,
    mut v_c_1054_: *mut crate::leanh::LeanObject,
    mut v_f_1055_: *mut crate::leanh::LeanObject,
    mut v_init_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1057_: u32 = 0;
    let mut v_res_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1057_ = crate::leanh::lean_unbox_uint32(v_c_1054_);
    crate::leanh::lean_dec(v_c_1054_);
    v_res_1058_ = l_Lake_foldlUtf8(v_00_u03c3_1053_, v_c_boxed_1057_, v_f_1055_, v_init_1056_);
    return v_res_1058_;
}
pub unsafe fn l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(
    mut v_c_1059_: u32,
    mut v_init_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: u32 = 0;
    let mut v___x_1062_: u8 = 0;
    v___x_1061_ = 127;
    v___x_1062_ = lean_uint32_dec_le(v_c_1059_, v___x_1061_);
    if v___x_1062_ == 0 {
        let mut v___x_1063_: u32 = 0;
        let mut v___x_1064_: u8 = 0;
        v___x_1063_ = 2047;
        v___x_1064_ = lean_uint32_dec_le(v_c_1059_, v___x_1063_);
        if v___x_1064_ == 0 {
            let mut v___x_1065_: u32 = 0;
            let mut v___x_1066_: u8 = 0;
            v___x_1065_ = 65535;
            v___x_1066_ = lean_uint32_dec_le(v_c_1059_, v___x_1065_);
            if v___x_1066_ == 0 {
                let mut v___x_1067_: u32 = 0;
                let mut v___x_1068_: u32 = 0;
                let mut v___x_1069_: u8 = 0;
                let mut v___x_1070_: u8 = 0;
                let mut v___x_1071_: u8 = 0;
                let mut v___x_1072_: u8 = 0;
                let mut v___x_1073_: u8 = 0;
                let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1075_: u32 = 0;
                let mut v___x_1076_: u32 = 0;
                let mut v___x_1077_: u8 = 0;
                let mut v___x_1078_: u8 = 0;
                let mut v___x_1079_: u8 = 0;
                let mut v___x_1080_: u8 = 0;
                let mut v___x_1081_: u8 = 0;
                let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1083_: u32 = 0;
                let mut v___x_1084_: u32 = 0;
                let mut v___x_1085_: u8 = 0;
                let mut v___x_1086_: u8 = 0;
                let mut v___x_1087_: u8 = 0;
                let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1089_: u8 = 0;
                let mut v___x_1090_: u8 = 0;
                let mut v___x_1091_: u8 = 0;
                let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1067_ = 18;
                v___x_1068_ = lean_uint32_shift_right(v_c_1059_, v___x_1067_);
                v___x_1069_ = lean_uint32_to_uint8(v___x_1068_);
                v___x_1070_ = 7;
                v___x_1071_ = lean_uint8_land(v___x_1069_, v___x_1070_);
                v___x_1072_ = 240;
                v___x_1073_ = lean_uint8_lor(v___x_1071_, v___x_1072_);
                v___x_1074_ = l_Lake_uriEscapeByte(v___x_1073_, v_init_1060_);
                v___x_1075_ = 12;
                v___x_1076_ = lean_uint32_shift_right(v_c_1059_, v___x_1075_);
                v___x_1077_ = lean_uint32_to_uint8(v___x_1076_);
                v___x_1078_ = 63;
                v___x_1079_ = lean_uint8_land(v___x_1077_, v___x_1078_);
                v___x_1080_ = 128;
                v___x_1081_ = lean_uint8_lor(v___x_1079_, v___x_1080_);
                v___x_1082_ = l_Lake_uriEscapeByte(v___x_1081_, v___x_1074_);
                v___x_1083_ = 6;
                v___x_1084_ = lean_uint32_shift_right(v_c_1059_, v___x_1083_);
                v___x_1085_ = lean_uint32_to_uint8(v___x_1084_);
                v___x_1086_ = lean_uint8_land(v___x_1085_, v___x_1078_);
                v___x_1087_ = lean_uint8_lor(v___x_1086_, v___x_1080_);
                v___x_1088_ = l_Lake_uriEscapeByte(v___x_1087_, v___x_1082_);
                v___x_1089_ = lean_uint32_to_uint8(v_c_1059_);
                v___x_1090_ = lean_uint8_land(v___x_1089_, v___x_1078_);
                v___x_1091_ = lean_uint8_lor(v___x_1090_, v___x_1080_);
                v___x_1092_ = l_Lake_uriEscapeByte(v___x_1091_, v___x_1088_);
                return v___x_1092_;
            } else {
                let mut v___x_1093_: u32 = 0;
                let mut v___x_1094_: u32 = 0;
                let mut v___x_1095_: u8 = 0;
                let mut v___x_1096_: u8 = 0;
                let mut v___x_1097_: u8 = 0;
                let mut v___x_1098_: u8 = 0;
                let mut v___x_1099_: u8 = 0;
                let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1101_: u32 = 0;
                let mut v___x_1102_: u32 = 0;
                let mut v___x_1103_: u8 = 0;
                let mut v___x_1104_: u8 = 0;
                let mut v___x_1105_: u8 = 0;
                let mut v___x_1106_: u8 = 0;
                let mut v___x_1107_: u8 = 0;
                let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1109_: u8 = 0;
                let mut v___x_1110_: u8 = 0;
                let mut v___x_1111_: u8 = 0;
                let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1093_ = 12;
                v___x_1094_ = lean_uint32_shift_right(v_c_1059_, v___x_1093_);
                v___x_1095_ = lean_uint32_to_uint8(v___x_1094_);
                v___x_1096_ = 15;
                v___x_1097_ = lean_uint8_land(v___x_1095_, v___x_1096_);
                v___x_1098_ = 224;
                v___x_1099_ = lean_uint8_lor(v___x_1097_, v___x_1098_);
                v___x_1100_ = l_Lake_uriEscapeByte(v___x_1099_, v_init_1060_);
                v___x_1101_ = 6;
                v___x_1102_ = lean_uint32_shift_right(v_c_1059_, v___x_1101_);
                v___x_1103_ = lean_uint32_to_uint8(v___x_1102_);
                v___x_1104_ = 63;
                v___x_1105_ = lean_uint8_land(v___x_1103_, v___x_1104_);
                v___x_1106_ = 128;
                v___x_1107_ = lean_uint8_lor(v___x_1105_, v___x_1106_);
                v___x_1108_ = l_Lake_uriEscapeByte(v___x_1107_, v___x_1100_);
                v___x_1109_ = lean_uint32_to_uint8(v_c_1059_);
                v___x_1110_ = lean_uint8_land(v___x_1109_, v___x_1104_);
                v___x_1111_ = lean_uint8_lor(v___x_1110_, v___x_1106_);
                v___x_1112_ = l_Lake_uriEscapeByte(v___x_1111_, v___x_1108_);
                return v___x_1112_;
            }
        } else {
            let mut v___x_1113_: u32 = 0;
            let mut v___x_1114_: u32 = 0;
            let mut v___x_1115_: u8 = 0;
            let mut v___x_1116_: u8 = 0;
            let mut v___x_1117_: u8 = 0;
            let mut v___x_1118_: u8 = 0;
            let mut v___x_1119_: u8 = 0;
            let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1121_: u8 = 0;
            let mut v___x_1122_: u8 = 0;
            let mut v___x_1123_: u8 = 0;
            let mut v___x_1124_: u8 = 0;
            let mut v___x_1125_: u8 = 0;
            let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1113_ = 6;
            v___x_1114_ = lean_uint32_shift_right(v_c_1059_, v___x_1113_);
            v___x_1115_ = lean_uint32_to_uint8(v___x_1114_);
            v___x_1116_ = 31;
            v___x_1117_ = lean_uint8_land(v___x_1115_, v___x_1116_);
            v___x_1118_ = 192;
            v___x_1119_ = lean_uint8_lor(v___x_1117_, v___x_1118_);
            v___x_1120_ = l_Lake_uriEscapeByte(v___x_1119_, v_init_1060_);
            v___x_1121_ = lean_uint32_to_uint8(v_c_1059_);
            v___x_1122_ = 63;
            v___x_1123_ = lean_uint8_land(v___x_1121_, v___x_1122_);
            v___x_1124_ = 128;
            v___x_1125_ = lean_uint8_lor(v___x_1123_, v___x_1124_);
            v___x_1126_ = l_Lake_uriEscapeByte(v___x_1125_, v___x_1120_);
            return v___x_1126_;
        }
    } else {
        let mut v___x_1127_: u8 = 0;
        let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1127_ = lean_uint32_to_uint8(v_c_1059_);
        v___x_1128_ = l_Lake_uriEscapeByte(v___x_1127_, v_init_1060_);
        return v___x_1128_;
    }
}
pub unsafe fn l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(
    mut v_c_1129_: *mut crate::leanh::LeanObject,
    mut v_init_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1131_: u32 = 0;
    let mut v_res_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1131_ = crate::leanh::lean_unbox_uint32(v_c_1129_);
    crate::leanh::lean_dec(v_c_1129_);
    v_res_1132_ =
        l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_boxed_1131_, v_init_1130_);
    return v_res_1132_;
}
pub unsafe fn l_Lake_uriEscapeChar(
    mut v_c_1133_: u32,
    mut v_s_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_1133_, v_s_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Lake_uriEscapeChar___boxed(
    mut v_c_1136_: *mut crate::leanh::LeanObject,
    mut v_s_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1138_: u32 = 0;
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1138_ = crate::leanh::lean_unbox_uint32(v_c_1136_);
    crate::leanh::lean_dec(v_c_1136_);
    v_res_1139_ = l_Lake_uriEscapeChar(v_c_boxed_1138_, v_s_1137_);
    return v_res_1139_;
}
pub unsafe fn l_Lake_isUriUnreservedMark(mut v_c_1140_: u32) -> u8 {
    let mut v___x_1141_: u32 = 0;
    let mut v___x_1142_: u8 = 0;
    v___x_1141_ = 45;
    v___x_1142_ = lean_uint32_dec_eq(v_c_1140_, v___x_1141_);
    if v___x_1142_ == 0 {
        let mut v___x_1143_: u32 = 0;
        let mut v___x_1144_: u8 = 0;
        v___x_1143_ = 95;
        v___x_1144_ = lean_uint32_dec_eq(v_c_1140_, v___x_1143_);
        if v___x_1144_ == 0 {
            let mut v___x_1145_: u32 = 0;
            let mut v___x_1146_: u8 = 0;
            v___x_1145_ = 46;
            v___x_1146_ = lean_uint32_dec_eq(v_c_1140_, v___x_1145_);
            if v___x_1146_ == 0 {
                let mut v___x_1147_: u32 = 0;
                let mut v___x_1148_: u8 = 0;
                v___x_1147_ = 126;
                v___x_1148_ = lean_uint32_dec_eq(v_c_1140_, v___x_1147_);
                return v___x_1148_;
            } else {
                return v___x_1146_;
            }
        } else {
            return v___x_1144_;
        }
    } else {
        return v___x_1142_;
    }
}
pub unsafe fn l_Lake_isUriUnreservedMark___boxed(
    mut v_c_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1150_: u32 = 0;
    let mut v_res_1151_: u8 = 0;
    let mut v_r_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1150_ = crate::leanh::lean_unbox_uint32(v_c_1149_);
    crate::leanh::lean_dec(v_c_1149_);
    v_res_1151_ = l_Lake_isUriUnreservedMark(v_c_boxed_1150_);
    v_r_1152_ = crate::leanh::lean_box((v_res_1151_) as usize);
    return v_r_1152_;
}
pub unsafe fn l_Lake_uriEncodeChar(
    mut v_c_1153_: u32,
    mut v_s_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1156_: u8 = 0;
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1162_: u8 = 0;
    let mut v___x_1163_: u32 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: u32 = 0;
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u32 = 0;
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: u32 = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: u32 = 0;
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: u32 = 0;
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1173_ = 65;
                v___x_1174_ = lean_uint32_dec_le(v___x_1173_, v_c_1153_);
                if v___x_1174_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_1175_ = 90;
                    v___x_1176_ = lean_uint32_dec_le(v_c_1153_, v___x_1175_);
                    if v___x_1176_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_1177_ = lean_string_push(v_s_1154_, v_c_1153_);
                        return v___x_1177_;
                    }
                }
            }
            1 => {
                if v___y_1156_ == 0 {
                    v___x_1157_ = l_Lake_isUriUnreservedMark(v_c_1153_);
                    if v___x_1157_ == 0 {
                        v___x_1158_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(
                            v_c_1153_, v_s_1154_,
                        );
                        return v___x_1158_;
                    } else {
                        v___x_1159_ = lean_string_push(v_s_1154_, v_c_1153_);
                        return v___x_1159_;
                    }
                } else {
                    v___x_1160_ = lean_string_push(v_s_1154_, v_c_1153_);
                    return v___x_1160_;
                }
            }
            2 => {
                if v___y_1162_ == 0 {
                    v___x_1163_ = 48;
                    v___x_1164_ = lean_uint32_dec_le(v___x_1163_, v_c_1153_);
                    if v___x_1164_ == 0 {
                        v___y_1156_ = v___x_1164_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1165_ = 57;
                        v___x_1166_ = lean_uint32_dec_le(v_c_1153_, v___x_1165_);
                        v___y_1156_ = v___x_1166_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1167_ = lean_string_push(v_s_1154_, v_c_1153_);
                    return v___x_1167_;
                }
            }
            3 => {
                v___x_1169_ = 97;
                v___x_1170_ = lean_uint32_dec_le(v___x_1169_, v_c_1153_);
                if v___x_1170_ == 0 {
                    v___y_1162_ = v___x_1170_;
                    state = 2;
                    continue;
                } else {
                    v___x_1171_ = 122;
                    v___x_1172_ = lean_uint32_dec_le(v_c_1153_, v___x_1171_);
                    v___y_1162_ = v___x_1172_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_uriEncodeChar___boxed(
    mut v_c_1178_: *mut crate::leanh::LeanObject,
    mut v_s_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1180_: u32 = 0;
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1180_ = crate::leanh::lean_unbox_uint32(v_c_1178_);
    crate::leanh::lean_dec(v_c_1178_);
    v_res_1181_ = l_Lake_uriEncodeChar(v_c_boxed_1180_, v_s_1179_);
    return v_res_1181_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(
    mut v___x_1182_: *mut crate::leanh::LeanObject,
    mut v_s_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_b_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut v___x_1190_: u32 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1186_ = crate::leanh::lean_ctor_get(v___x_1182_, 1);
                v_endExclusive_1187_ = crate::leanh::lean_ctor_get(v___x_1182_, 2);
                v___x_1188_ = lean_nat_sub(v_endExclusive_1187_, v_startInclusive_1186_);
                v___x_1189_ = lean_nat_dec_eq(v_a_1184_, v___x_1188_);
                crate::leanh::lean_dec(v___x_1188_);
                if v___x_1189_ == 0 {
                    v___x_1190_ = lean_string_utf8_get_fast(v_s_1183_, v_a_1184_);
                    v___x_1191_ = lean_string_utf8_next_fast(v_s_1183_, v_a_1184_);
                    crate::leanh::lean_dec(v_a_1184_);
                    v___x_1192_ = l_Lake_uriEncodeChar(v___x_1190_, v_b_1185_);
                    v_a_1184_ = v___x_1191_;
                    v_b_1185_ = v___x_1192_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1184_);
                    return v_b_1185_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(
    mut v___x_1194_: *mut crate::leanh::LeanObject,
    mut v_s_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_b_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(
        v___x_1194_,
        v_s_1195_,
        v_a_1196_,
        v_b_1197_,
    );
    crate::leanh::lean_dec_ref(v_s_1195_);
    crate::leanh::lean_dec_ref(v___x_1194_);
    return v_res_1198_;
}
pub unsafe fn l_Lake_uriEncode(
    mut v_s_1199_: *mut crate::leanh::LeanObject,
    mut v_init_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1202_ = lean_string_utf8_byte_size(v_s_1199_);
    crate::leanh::lean_inc_ref(v_s_1199_);
    v___x_1203_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1203_, 0, v_s_1199_);
    crate::leanh::lean_ctor_set(v___x_1203_, 1, v___x_1201_);
    crate::leanh::lean_ctor_set(v___x_1203_, 2, v___x_1202_);
    v___x_1204_ = l_String_Slice_positions(v___x_1203_);
    v___x_1205_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(
        v___x_1203_,
        v_s_1199_,
        v___x_1204_,
        v_init_1200_,
    );
    crate::leanh::lean_dec_ref(v_s_1199_);
    crate::leanh::lean_dec_ref_known(v___x_1203_, 3);
    return v___x_1205_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(
    mut v___x_1206_: *mut crate::leanh::LeanObject,
    mut v_s_1207_: *mut crate::leanh::LeanObject,
    mut v_inst_1208_: *mut crate::leanh::LeanObject,
    mut v_R_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
    mut v_b_1211_: *mut crate::leanh::LeanObject,
    mut v_c_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(
        v___x_1206_,
        v_s_1207_,
        v_a_1210_,
        v_b_1211_,
    );
    return v___x_1213_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(
    mut v___x_1214_: *mut crate::leanh::LeanObject,
    mut v_s_1215_: *mut crate::leanh::LeanObject,
    mut v_inst_1216_: *mut crate::leanh::LeanObject,
    mut v_R_1217_: *mut crate::leanh::LeanObject,
    mut v_a_1218_: *mut crate::leanh::LeanObject,
    mut v_b_1219_: *mut crate::leanh::LeanObject,
    mut v_c_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(
        v___x_1214_,
        v_s_1215_,
        v_inst_1216_,
        v_R_1217_,
        v_a_1218_,
        v_b_1219_,
        v_c_1220_,
    );
    crate::leanh::lean_dec_ref(v_s_1215_);
    crate::leanh::lean_dec_ref(v___x_1214_);
    return v_res_1221_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(
    mut v_x_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v_a_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1238_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1224_) == 0 {
                    v___x_1225_ =
                        l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0;
                    return v___x_1225_;
                } else {
                    v___x_1226_ = l_Lean_Json_getNat_x3f(v_x_1224_);
                    if crate::leanh::lean_obj_tag(v___x_1226_) == 0 {
                        v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
                        v_isSharedCheck_1234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1226_)) as u8;
                        if v_isSharedCheck_1234_ == 0 {
                            v___x_1229_ = v___x_1226_;
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1227_);
                            crate::leanh::lean_dec(v___x_1226_);
                            v___x_1229_ = crate::leanh::lean_box(0);
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1235_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
                        v_isSharedCheck_1243_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1226_)) as u8;
                        if v_isSharedCheck_1243_ == 0 {
                            v___x_1237_ = v___x_1226_;
                            v_isShared_1238_ = v_isSharedCheck_1243_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1235_);
                            crate::leanh::lean_dec(v___x_1226_);
                            v___x_1237_ = crate::leanh::lean_box(0);
                            v_isShared_1238_ = v_isSharedCheck_1243_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1230_ == 0 {
                    v___x_1232_ = v___x_1229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
                    v___x_1232_ = v_reuseFailAlloc_1233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1232_;
            }
            3 => {
                v___x_1239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1239_, 0, v_a_1235_);
                if v_isShared_1238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1239_);
                    v___x_1241_ = v___x_1237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
                    v___x_1241_ = v_reuseFailAlloc_1242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0;
    v___x_1246_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1247_ = lean_mk_empty_array_with_capacity(v___x_1246_);
    v___x_1248_ = lean_array_push(v___x_1247_, v___x_1245_);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(
    mut v_as_1249_: *mut crate::leanh::LeanObject,
    mut v_i_1250_: usize,
    mut v_stop_1251_: usize,
    mut v_b_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: usize = 0;
    let mut v___x_1259_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = lean_usize_dec_eq(v_i_1250_, v_stop_1251_);
                if v___x_1253_ == 0 {
                    v___x_1254_ = lean_array_uget_borrowed(v_as_1249_, v_i_1250_);
                    v___x_1255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1);
                    crate::leanh::lean_inc(v___x_1254_);
                    v___x_1256_ = lean_array_push(v___x_1255_, v___x_1254_);
                    v___x_1257_ = l_Array_append___redArg(v_b_1252_, v___x_1256_);
                    crate::leanh::lean_dec_ref(v___x_1256_);
                    v___x_1258_ = 1usize;
                    v___x_1259_ = lean_usize_add(v_i_1250_, v___x_1258_);
                    v_i_1250_ = v___x_1259_;
                    v_b_1252_ = v___x_1257_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1252_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(
    mut v_as_1261_: *mut crate::leanh::LeanObject,
    mut v_i_1262_: *mut crate::leanh::LeanObject,
    mut v_stop_1263_: *mut crate::leanh::LeanObject,
    mut v_b_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1265_: usize = 0;
    let mut v_stop_boxed_1266_: usize = 0;
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1265_ = crate::leanh::lean_unbox_usize(v_i_1262_);
    crate::leanh::lean_dec(v_i_1262_);
    v_stop_boxed_1266_ = crate::leanh::lean_unbox_usize(v_stop_1263_);
    crate::leanh::lean_dec(v_stop_1263_);
    v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_as_1261_, v_i_boxed_1265_, v_stop_boxed_1266_, v_b_1264_);
    crate::leanh::lean_dec_ref(v_as_1261_);
    return v_res_1267_;
}
pub unsafe fn l_Lake_getUrl_x3f(
    mut v_url_1304_: *mut crate::leanh::LeanObject,
    mut v_headers_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: u8 = 0;
    let mut v_stdout_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdout_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: usize = 0;
    let mut v___x_1426_: usize = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_args_1417_ = l_Lake_getUrl_x3f___closed__18;
                v___x_1418_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1419_ = lean_array_get_size(v_headers_1305_);
                v___x_1420_ = lean_nat_dec_lt(v___x_1418_, v___x_1419_);
                if v___x_1420_ == 0 {
                    v___y_1390_ = v_args_1417_;
                    state = 9;
                    continue;
                } else {
                    v___x_1421_ = lean_nat_dec_le(v___x_1419_, v___x_1419_);
                    if v___x_1421_ == 0 {
                        if v___x_1420_ == 0 {
                            v___y_1390_ = v_args_1417_;
                            state = 9;
                            continue;
                        } else {
                            v___x_1422_ = 0usize;
                            v___x_1423_ = lean_usize_of_nat(v___x_1419_);
                            v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_1305_, v___x_1422_, v___x_1423_, v_args_1417_);
                            v___y_1390_ = v___x_1424_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_1425_ = 0usize;
                        v___x_1426_ = lean_usize_of_nat(v___x_1419_);
                        v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_1305_, v___x_1425_, v___x_1426_, v_args_1417_);
                        v___y_1390_ = v___x_1427_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1311_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1311_, 0, v___y_1309_);
                crate::leanh::lean_ctor_set(v___x_1311_, 1, v_a_1310_);
                return v___x_1311_;
            }
            2 => {
                v___x_1316_ = l_Lake_getUrl_x3f___closed__0;
                v___x_1317_ = lean_string_append(v___x_1316_, v_a_1315_);
                crate::leanh::lean_dec_ref(v_a_1315_);
                v___x_1318_ = 3;
                v___x_1319_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1317_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1319_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1318_,
                );
                v___x_1320_ = lean_array_push(v___y_1314_, v___x_1319_);
                v___y_1309_ = v___y_1313_;
                v_a_1310_ = v___x_1320_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1324_ = l_Lake_getUrl_x3f___closed__2;
                v___x_1325_ = lean_array_push(v___y_1323_, v___x_1324_);
                v___y_1309_ = v___y_1322_;
                v_a_1310_ = v___x_1325_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1330_ = l_Lake_getUrl_x3f___closed__3;
                v___x_1331_ = lean_string_append(v___x_1330_, v_a_1329_);
                crate::leanh::lean_dec_ref(v_a_1329_);
                v___x_1332_ = 3;
                v___x_1333_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1331_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1332_,
                );
                v___x_1334_ = lean_array_push(v___y_1328_, v___x_1333_);
                v___y_1309_ = v___y_1327_;
                v_a_1310_ = v___x_1334_;
                state = 1;
                continue;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_1340_) == 0 {
                    crate::leanh::lean_dec(v___y_1339_);
                    crate::leanh::lean_dec_ref(v___y_1336_);
                    v___y_1322_ = v___y_1337_;
                    v___y_1323_ = v___y_1338_;
                    state = 3;
                    continue;
                } else {
                    v_val_1341_ = crate::leanh::lean_ctor_get(v_a_1340_, 0);
                    v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v_a_1340_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v___x_1343_ = v_a_1340_;
                        v_isShared_1344_ = v_isSharedCheck_1373_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1341_);
                        crate::leanh::lean_dec(v_a_1340_);
                        v___x_1343_ = crate::leanh::lean_box(0);
                        v_isShared_1344_ = v_isSharedCheck_1373_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1345_ = crate::leanh::lean_unsigned_to_nat(200);
                v___x_1346_ = lean_nat_dec_eq(v_val_1341_, v___x_1345_);
                if v___x_1346_ == 0 {
                    crate::leanh::lean_del_object(v___x_1343_);
                    crate::leanh::lean_dec(v___y_1339_);
                    v___x_1347_ = crate::leanh::lean_unsigned_to_nat(404);
                    v___x_1348_ = lean_nat_dec_eq(v_val_1341_, v___x_1347_);
                    if v___x_1348_ == 0 {
                        v_stdout_1349_ = crate::leanh::lean_ctor_get(v___y_1336_, 0);
                        crate::leanh::lean_inc_ref(v_stdout_1349_);
                        crate::leanh::lean_dec_ref(v___y_1336_);
                        v___x_1350_ = l_Lake_getUrl_x3f___closed__4;
                        v___x_1351_ = l_Nat_reprFast(v_val_1341_);
                        v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
                        crate::leanh::lean_dec_ref(v___x_1351_);
                        v___x_1353_ = l_Lake_getUrl_x3f___closed__5;
                        v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
                        v___x_1355_ = lean_string_append(v___x_1354_, v_stdout_1349_);
                        crate::leanh::lean_dec_ref(v_stdout_1349_);
                        v___x_1356_ = 3;
                        v___x_1357_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1355_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1357_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1356_,
                        );
                        v___x_1358_ = lean_array_push(v___y_1338_, v___x_1357_);
                        v___y_1309_ = v___y_1337_;
                        v_a_1310_ = v___x_1358_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_1341_);
                        crate::leanh::lean_dec(v___y_1337_);
                        crate::leanh::lean_dec_ref(v___y_1336_);
                        v___x_1359_ = crate::leanh::lean_box(0);
                        v___x_1360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
                        crate::leanh::lean_ctor_set(v___x_1360_, 1, v___y_1338_);
                        return v___x_1360_;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_1341_);
                    crate::leanh::lean_dec(v___y_1337_);
                    v_stdout_1361_ = crate::leanh::lean_ctor_get(v___y_1336_, 0);
                    crate::leanh::lean_inc_ref(v_stdout_1361_);
                    crate::leanh::lean_dec_ref(v___y_1336_);
                    v___x_1362_ = lean_string_utf8_byte_size(v_stdout_1361_);
                    v___x_1363_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1363_, 0, v_stdout_1361_);
                    crate::leanh::lean_ctor_set(v___x_1363_, 1, v___y_1339_);
                    crate::leanh::lean_ctor_set(v___x_1363_, 2, v___x_1362_);
                    v___x_1364_ = l_String_Slice_trimAscii(v___x_1363_);
                    v_str_1365_ = crate::leanh::lean_ctor_get(v___x_1364_, 0);
                    crate::leanh::lean_inc_ref(v_str_1365_);
                    v_startInclusive_1366_ = crate::leanh::lean_ctor_get(v___x_1364_, 1);
                    crate::leanh::lean_inc(v_startInclusive_1366_);
                    v_endExclusive_1367_ = crate::leanh::lean_ctor_get(v___x_1364_, 2);
                    crate::leanh::lean_inc(v_endExclusive_1367_);
                    crate::leanh::lean_dec_ref(v___x_1364_);
                    v___x_1368_ = lean_string_utf8_extract(
                        v_str_1365_,
                        v_startInclusive_1366_,
                        v_endExclusive_1367_,
                    );
                    crate::leanh::lean_dec(v_endExclusive_1367_);
                    crate::leanh::lean_dec(v_startInclusive_1366_);
                    crate::leanh::lean_dec_ref(v_str_1365_);
                    if v_isShared_1344_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1343_, 0, v___x_1368_);
                        v___x_1370_ = v___x_1343_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1368_);
                        v___x_1370_ = v_reuseFailAlloc_1372_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1371_, 0, v___x_1370_);
                crate::leanh::lean_ctor_set(v___x_1371_, 1, v___y_1338_);
                return v___x_1371_;
            }
            8 => {
                v___x_1380_ = l_Lake_getUrl_x3f___closed__6;
                v___x_1381_ = l_Lake_JsonObject_getJson_x3f(v___y_1375_, v___x_1380_);
                crate::leanh::lean_dec(v___y_1375_);
                if crate::leanh::lean_obj_tag(v___x_1381_) == 0 {
                    crate::leanh::lean_dec(v___y_1379_);
                    crate::leanh::lean_dec_ref(v___y_1376_);
                    v___y_1322_ = v___y_1377_;
                    v___y_1323_ = v___y_1378_;
                    state = 3;
                    continue;
                } else {
                    v_val_1382_ = crate::leanh::lean_ctor_get(v___x_1381_, 0);
                    crate::leanh::lean_inc(v_val_1382_);
                    crate::leanh::lean_dec_ref_known(v___x_1381_, 1);
                    v___x_1383_ =
                        l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_1382_);
                    if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                        crate::leanh::lean_dec(v___y_1379_);
                        crate::leanh::lean_dec_ref(v___y_1376_);
                        v_a_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                        crate::leanh::lean_inc(v_a_1384_);
                        crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                        v___x_1385_ = l_Lake_getUrl_x3f___closed__7;
                        v___x_1386_ = lean_string_append(v___x_1385_, v_a_1384_);
                        crate::leanh::lean_dec(v_a_1384_);
                        v___y_1313_ = v___y_1377_;
                        v___y_1314_ = v___y_1378_;
                        v_a_1315_ = v___x_1386_;
                        state = 2;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                            crate::leanh::lean_dec(v___y_1379_);
                            crate::leanh::lean_dec_ref(v___y_1376_);
                            v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                            crate::leanh::lean_inc(v_a_1387_);
                            crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                            v___y_1313_ = v___y_1377_;
                            v___y_1314_ = v___y_1378_;
                            v_a_1315_ = v_a_1387_;
                            state = 2;
                            continue;
                        } else {
                            v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                            crate::leanh::lean_inc(v_a_1388_);
                            crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                            v___y_1336_ = v___y_1376_;
                            v___y_1337_ = v___y_1377_;
                            v___y_1338_ = v___y_1378_;
                            v___y_1339_ = v___y_1379_;
                            v_a_1340_ = v_a_1388_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_1391_ = l_Lake_getUrl_x3f___closed__8;
                v___x_1392_ = l_Lake_getUrl_x3f___closed__9;
                v___x_1393_ = lean_array_push(v___y_1390_, v_url_1304_);
                v___x_1394_ = crate::leanh::lean_box(0);
                v___x_1395_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1396_ = l_Lake_getUrl_x3f___closed__10;
                v___x_1397_ = 1;
                v___x_1398_ = 0;
                v___x_1399_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1399_, 0, v___x_1391_);
                crate::leanh::lean_ctor_set(v___x_1399_, 1, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1399_, 2, v___x_1393_);
                crate::leanh::lean_ctor_set(v___x_1399_, 3, v___x_1394_);
                crate::leanh::lean_ctor_set(v___x_1399_, 4, v___x_1396_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1399_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_1397_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1399_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1398_,
                );
                crate::leanh::lean_inc_ref(v_a_1306_);
                v___x_1400_ = l_Lake_captureProc_x27(v___x_1399_, v_a_1306_);
                v___x_1401_ = lean_array_get_size(v_a_1306_);
                crate::leanh::lean_dec_ref(v_a_1306_);
                if crate::leanh::lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1402_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                    crate::leanh::lean_inc(v_a_1402_);
                    v_a_1403_ = crate::leanh::lean_ctor_get(v___x_1400_, 1);
                    crate::leanh::lean_inc(v_a_1403_);
                    crate::leanh::lean_dec_ref_known(v___x_1400_, 2);
                    v_stderr_1404_ = crate::leanh::lean_ctor_get(v_a_1402_, 1);
                    crate::leanh::lean_inc_ref(v_stderr_1404_);
                    v___x_1405_ = l_Lean_Json_parse(v_stderr_1404_);
                    if crate::leanh::lean_obj_tag(v___x_1405_) == 0 {
                        crate::leanh::lean_dec(v_a_1402_);
                        v_a_1406_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                        crate::leanh::lean_inc(v_a_1406_);
                        crate::leanh::lean_dec_ref_known(v___x_1405_, 1);
                        v___y_1327_ = v___x_1401_;
                        v___y_1328_ = v_a_1403_;
                        v_a_1329_ = v_a_1406_;
                        state = 4;
                        continue;
                    } else {
                        v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                        crate::leanh::lean_inc(v_a_1407_);
                        crate::leanh::lean_dec_ref_known(v___x_1405_, 1);
                        v___x_1408_ = l_Lean_Json_getObj_x3f(v_a_1407_);
                        if crate::leanh::lean_obj_tag(v___x_1408_) == 0 {
                            crate::leanh::lean_dec(v_a_1402_);
                            v_a_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                            crate::leanh::lean_inc(v_a_1409_);
                            crate::leanh::lean_dec_ref_known(v___x_1408_, 1);
                            v___y_1327_ = v___x_1401_;
                            v___y_1328_ = v_a_1403_;
                            v_a_1329_ = v_a_1409_;
                            state = 4;
                            continue;
                        } else {
                            v_a_1410_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                            crate::leanh::lean_inc(v_a_1410_);
                            crate::leanh::lean_dec_ref_known(v___x_1408_, 1);
                            v___x_1411_ = l_Lake_getUrl_x3f___closed__11;
                            v___x_1412_ = l_Lake_JsonObject_getJson_x3f(v_a_1410_, v___x_1411_);
                            if crate::leanh::lean_obj_tag(v___x_1412_) == 0 {
                                crate::leanh::lean_dec(v_a_1410_);
                                crate::leanh::lean_dec(v_a_1402_);
                                v___y_1322_ = v___x_1401_;
                                v___y_1323_ = v_a_1403_;
                                state = 3;
                                continue;
                            } else {
                                v_val_1413_ = crate::leanh::lean_ctor_get(v___x_1412_, 0);
                                crate::leanh::lean_inc(v_val_1413_);
                                crate::leanh::lean_dec_ref_known(v___x_1412_, 1);
                                v___x_1414_ =
                                    l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(
                                        v_val_1413_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_1414_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1414_, 1);
                                    v___y_1375_ = v_a_1410_;
                                    v___y_1376_ = v_a_1402_;
                                    v___y_1377_ = v___x_1401_;
                                    v___y_1378_ = v_a_1403_;
                                    v___y_1379_ = v___x_1395_;
                                    state = 8;
                                    continue;
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_1414_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1414_, 1);
                                        v___y_1375_ = v_a_1410_;
                                        v___y_1376_ = v_a_1402_;
                                        v___y_1377_ = v___x_1401_;
                                        v___y_1378_ = v_a_1403_;
                                        v___y_1379_ = v___x_1395_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1410_);
                                        v_a_1415_ = crate::leanh::lean_ctor_get(v___x_1414_, 0);
                                        crate::leanh::lean_inc(v_a_1415_);
                                        crate::leanh::lean_dec_ref_known(v___x_1414_, 1);
                                        v___y_1336_ = v_a_1402_;
                                        v___y_1337_ = v___x_1401_;
                                        v___y_1338_ = v_a_1403_;
                                        v___y_1339_ = v___x_1395_;
                                        v_a_1340_ = v_a_1415_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v_a_1416_ = crate::leanh::lean_ctor_get(v___x_1400_, 1);
                    crate::leanh::lean_inc(v_a_1416_);
                    crate::leanh::lean_dec_ref_known(v___x_1400_, 2);
                    v___y_1309_ = v___x_1401_;
                    v_a_1310_ = v_a_1416_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getUrl_x3f___boxed(
    mut v_url_1428_: *mut crate::leanh::LeanObject,
    mut v_headers_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lake_getUrl_x3f(v_url_1428_, v_headers_1429_, v_a_1430_);
    crate::leanh::lean_dec_ref(v_headers_1429_);
    return v_res_1432_;
}
pub unsafe fn l_Lake_getUrl(
    mut v_url_1443_: *mut crate::leanh::LeanObject,
    mut v_headers_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v_stdout_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1475_: u8 = 0;
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_args_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_args_1485_ = l_Lake_getUrl___closed__0;
                v___x_1486_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1487_ = lean_array_get_size(v_headers_1444_);
                v___x_1488_ = lean_nat_dec_lt(v___x_1486_, v___x_1487_);
                if v___x_1488_ == 0 {
                    v___y_1448_ = v_args_1485_;
                    state = 1;
                    continue;
                } else {
                    v___x_1489_ = lean_nat_dec_le(v___x_1487_, v___x_1487_);
                    if v___x_1489_ == 0 {
                        if v___x_1488_ == 0 {
                            v___y_1448_ = v_args_1485_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1490_ = 0usize;
                            v___x_1491_ = lean_usize_of_nat(v___x_1487_);
                            v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_1444_, v___x_1490_, v___x_1491_, v_args_1485_);
                            v___y_1448_ = v___x_1492_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1493_ = 0usize;
                        v___x_1494_ = lean_usize_of_nat(v___x_1487_);
                        v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_1444_, v___x_1493_, v___x_1494_, v_args_1485_);
                        v___y_1448_ = v___x_1495_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1449_ = l_Lake_getUrl_x3f___closed__8;
                v___x_1450_ = l_Lake_getUrl_x3f___closed__9;
                v___x_1451_ = lean_array_push(v___y_1448_, v_url_1443_);
                v___x_1452_ = crate::leanh::lean_box(0);
                v___x_1453_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1454_ = l_Lake_getUrl_x3f___closed__10;
                v___x_1455_ = 1;
                v___x_1456_ = 0;
                v___x_1457_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1449_);
                crate::leanh::lean_ctor_set(v___x_1457_, 1, v___x_1450_);
                crate::leanh::lean_ctor_set(v___x_1457_, 2, v___x_1451_);
                crate::leanh::lean_ctor_set(v___x_1457_, 3, v___x_1452_);
                crate::leanh::lean_ctor_set(v___x_1457_, 4, v___x_1454_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_1455_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1456_,
                );
                v___x_1458_ = l_Lake_captureProc_x27(v___x_1457_, v_a_1445_);
                if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                    v_a_1459_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                    v_a_1460_ = crate::leanh::lean_ctor_get(v___x_1458_, 1);
                    v_isSharedCheck_1475_ = (!crate::leanh::lean_is_exclusive(v___x_1458_)) as u8;
                    if v_isSharedCheck_1475_ == 0 {
                        v___x_1462_ = v___x_1458_;
                        v_isShared_1463_ = v_isSharedCheck_1475_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1460_);
                        crate::leanh::lean_inc(v_a_1459_);
                        crate::leanh::lean_dec(v___x_1458_);
                        v___x_1462_ = crate::leanh::lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1475_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                    v_a_1477_ = crate::leanh::lean_ctor_get(v___x_1458_, 1);
                    v_isSharedCheck_1484_ = (!crate::leanh::lean_is_exclusive(v___x_1458_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1479_ = v___x_1458_;
                        v_isShared_1480_ = v_isSharedCheck_1484_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1477_);
                        crate::leanh::lean_inc(v_a_1476_);
                        crate::leanh::lean_dec(v___x_1458_);
                        v___x_1479_ = crate::leanh::lean_box(0);
                        v_isShared_1480_ = v_isSharedCheck_1484_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_stdout_1464_ = crate::leanh::lean_ctor_get(v_a_1459_, 0);
                crate::leanh::lean_inc_ref(v_stdout_1464_);
                crate::leanh::lean_dec(v_a_1459_);
                v___x_1465_ = lean_string_utf8_byte_size(v_stdout_1464_);
                v___x_1466_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1466_, 0, v_stdout_1464_);
                crate::leanh::lean_ctor_set(v___x_1466_, 1, v___x_1453_);
                crate::leanh::lean_ctor_set(v___x_1466_, 2, v___x_1465_);
                v___x_1467_ = l_String_Slice_trimAscii(v___x_1466_);
                v_str_1468_ = crate::leanh::lean_ctor_get(v___x_1467_, 0);
                crate::leanh::lean_inc_ref(v_str_1468_);
                v_startInclusive_1469_ = crate::leanh::lean_ctor_get(v___x_1467_, 1);
                crate::leanh::lean_inc(v_startInclusive_1469_);
                v_endExclusive_1470_ = crate::leanh::lean_ctor_get(v___x_1467_, 2);
                crate::leanh::lean_inc(v_endExclusive_1470_);
                crate::leanh::lean_dec_ref(v___x_1467_);
                v___x_1471_ = lean_string_utf8_extract(
                    v_str_1468_,
                    v_startInclusive_1469_,
                    v_endExclusive_1470_,
                );
                crate::leanh::lean_dec(v_endExclusive_1470_);
                crate::leanh::lean_dec(v_startInclusive_1469_);
                crate::leanh::lean_dec_ref(v_str_1468_);
                if v_isShared_1463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1471_);
                    v___x_1473_ = v___x_1462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_a_1460_);
                    v___x_1473_ = v_reuseFailAlloc_1474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1473_;
            }
            4 => {
                if v_isShared_1480_ == 0 {
                    v___x_1482_ = v___x_1479_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1477_);
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getUrl___boxed(
    mut v_url_1496_: *mut crate::leanh::LeanObject,
    mut v_headers_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Lake_getUrl(v_url_1496_, v_headers_1497_, v_a_1498_);
    crate::leanh::lean_dec_ref(v_headers_1497_);
    return v_res_1500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Url(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Url(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Url(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Url(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Url(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Url(builtin);
}
